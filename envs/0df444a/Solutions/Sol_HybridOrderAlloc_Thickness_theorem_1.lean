-- Prove2me | solution 1 for HybridOrderAlloc.Thickness.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T06:52:15.061171+00:00
-- url     : https://prove2.me/submissions/2d1630b4-d2d1-455e-9cae-b3a686fc5a8b

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory HybridOrderAlloc.Thickness

namespace HOAProof

variable {Ω : Type*} [MeasurableSpace Ω]

def dom : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 ≤ q.2}

lemma measurableSet_dom : MeasurableSet dom := by
  have h1 : MeasurableSet {q : ℝ × ℝ | 0 < q.1} := measurableSet_lt measurable_const measurable_fst
  have h2 : MeasurableSet {q : ℝ × ℝ | 0 ≤ q.2} := measurableSet_le measurable_const measurable_snd
  exact h1.inter h2

lemma aesm_comp {μ : Measure Ω} (F : ℝ × ℝ → ℝ) (hF : ContinuousOn F dom)
    (g : Ω → ℝ × ℝ) (hg : AEMeasurable g μ) (hgs : ∀ᵐ ω ∂μ, g ω ∈ dom) :
    AEStronglyMeasurable (fun ω => F (g ω)) μ := by
  classical
  have hm : Measurable (dom.piecewise F (fun _ => (0:ℝ))) :=
    ContinuousOn.measurable_piecewise hF continuousOn_const measurableSet_dom
  have hae : (fun ω => F (g ω)) =ᵐ[μ] fun ω => dom.piecewise F (fun _ => (0:ℝ)) (g ω) := by
    filter_upwards [hgs] with ω hω
    simp [Set.piecewise, hω]
  exact (hm.comp_aemeasurable hg).aestronglyMeasurable.congr hae.symm

/-- the integrand of the continuation term of (5) -/
noncomputable def nxt (S : Sys Ω) (W : ℝ → ℝ → ℝ) (M D y : ℝ) (ω : Ω) : ℝ :=
  W ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y)
    (S.eta * D + S.theta ω * M + S.eps ω)

def Reg (W : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (Function.uncurry W) dom ∧
    ∃ C : ℝ, ∀ M D : ℝ, 0 < M → 0 ≤ D → |W M D| ≤ C * (1 + M + D)

noncomputable def lin (S : Sys Ω) (c0 c1 c2 c3 : ℝ) (ω : Ω) : ℝ :=
  c0 + c1 * S.beta ω + c2 * S.theta ω + c3 * S.eps ω

noncomputable def Eeps (S : Sys Ω) : ℝ := ∫ ω, S.eps ω ∂S.P

lemma integrable_lin (S : Sys Ω) (hS : S.Standing) (c0 c1 c2 c3 : ℝ) :
    Integrable (lin S c0 c1 c2 c3) S.P := by
  haveI := hS.isProb
  have hb : Integrable S.beta S.P := hS.beta_memLp.integrable one_le_two
  have ht : Integrable S.theta S.P := hS.theta_memLp.integrable one_le_two
  have he : Integrable S.eps S.P := hS.eps_memLp.integrable one_le_two
  exact (((integrable_const c0).add (hb.const_mul c1)).add (ht.const_mul c2)).add (he.const_mul c3)

lemma integral_lin (S : Sys Ω) (hS : S.Standing) (c0 c1 c2 c3 : ℝ) :
    ∫ ω, lin S c0 c1 c2 c3 ω ∂S.P = c0 + c1 * S.mu + c2 * S.muTheta + c3 * Eeps S := by
  haveI := hS.isProb
  have hb : Integrable S.beta S.P := hS.beta_memLp.integrable one_le_two
  have ht : Integrable S.theta S.P := hS.theta_memLp.integrable one_le_two
  have he : Integrable S.eps S.P := hS.eps_memLp.integrable one_le_two
  have h1 : Integrable (fun ω => c0 + c1 * S.beta ω) S.P := (integrable_const c0).add (hb.const_mul c1)
  have h2 : Integrable (fun ω => c0 + c1 * S.beta ω + c2 * S.theta ω) S.P := h1.add (ht.const_mul c2)
  unfold lin
  rw [integral_add h2 (he.const_mul c3), integral_add h1 (ht.const_mul c2),
    integral_add (integrable_const c0) (hb.const_mul c1), integral_const, integral_const_mul,
    integral_const_mul, integral_const_mul]
  simp [Sys.mu, Sys.muTheta, Eeps]

lemma int_ge (S : Sys Ω) (hS : S.Standing) {f h : Ω → ℝ} (hf : Integrable f S.P)
    (hh : Integrable h S.P) (c0 c1 c2 c3 : ℝ)
    (hle : ∀ᵐ ω ∂S.P, h ω + lin S c0 c1 c2 c3 ω ≤ f ω) :
    (∫ ω, h ω ∂S.P) + (c0 + c1 * S.mu + c2 * S.muTheta + c3 * Eeps S) ≤ ∫ ω, f ω ∂S.P := by
  rw [← integral_lin S hS, ← integral_add hh (integrable_lin S hS c0 c1 c2 c3)]
  exact integral_mono_ae (hh.add (integrable_lin S hS c0 c1 c2 c3)) hf hle

lemma int_le (S : Sys Ω) (hS : S.Standing) {f h : Ω → ℝ} (hf : Integrable f S.P)
    (hh : Integrable h S.P) (c0 c1 c2 c3 : ℝ)
    (hle : ∀ᵐ ω ∂S.P, f ω ≤ h ω + lin S c0 c1 c2 c3 ω) :
    ∫ ω, f ω ∂S.P ≤ (∫ ω, h ω ∂S.P) + (c0 + c1 * S.mu + c2 * S.muTheta + c3 * Eeps S) := by
  rw [← integral_lin S hS, ← integral_add hh (integrable_lin S hS c0 c1 c2 c3)]
  exact integral_mono_ae hf (hh.add (integrable_lin S hS c0 c1 c2 c3)) hle

lemma R_pos (S : Sys Ω) (hS : S.Standing) : 0 < S.R := lt_of_lt_of_le zero_lt_one hS.one_le_R

lemma nxt_mem (S : Sys Ω) (hS : S.Standing) {M D y : ℝ} (hM : 0 < M) (hD : 0 ≤ D) (hy : 0 ≤ y) :
    ∀ᵐ ω ∂S.P, ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y,
      S.eta * D + S.theta ω * M + S.eps ω) ∈ dom := by
  filter_upwards [hS.growth_pos, hS.theta_nonneg, hS.eps_nonneg] with ω h1 h2 h3
  have hδ := hS.delta_nonneg
  have hR := (R_pos S hS).le
  have hη := hS.eta_nonneg
  constructor
  · show 0 < _
    have := mul_pos h1 hM
    have := mul_nonneg (mul_nonneg hδ hR) hy
    linarith
  · show 0 ≤ _
    have := mul_nonneg hη hD
    have := mul_nonneg h2 hM.le
    linarith

lemma integrable_nxt (S : Sys Ω) (hS : S.Standing) {W : ℝ → ℝ → ℝ} (hW : Reg W)
    {M D y : ℝ} (hM : 0 < M) (hD : 0 ≤ D) (hy : 0 ≤ y) :
    Integrable (nxt S W M D y) S.P := by
  haveI := hS.isProb
  obtain ⟨hc, C, hC⟩ := hW
  have hb : Integrable S.beta S.P := hS.beta_memLp.integrable one_le_two
  have ht : Integrable S.theta S.P := hS.theta_memLp.integrable one_le_two
  have he : Integrable S.eps S.P := hS.eps_memLp.integrable one_le_two
  have hmem := nxt_mem S hS hM hD hy
  have hg : AEMeasurable (fun ω => ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y,
      S.eta * D + S.theta ω * M + S.eps ω)) S.P := by
    have hbm := hb.aemeasurable
    have htm := ht.aemeasurable
    have hem := he.aemeasurable
    refine AEMeasurable.prodMk ?_ ?_
    · exact ((aemeasurable_const.add (hbm.const_mul _)).mul_const _).add aemeasurable_const
    · exact (aemeasurable_const.add (htm.mul_const _)).add hem
  have hlin : Integrable (lin S (C * (1 + S.rho * M + S.delta * S.R * y + S.eta * D))
      (C * (S.delta * S.R * M)) (C * M) C) S.P := integrable_lin S hS _ _ _ _
  refine Integrable.mono' hlin ?_ ?_
  · exact aesm_comp (Function.uncurry W) hc _ hg hmem
  · filter_upwards [hmem] with ω hω
    rw [Real.norm_eq_abs]
    have := hC _ _ hω.1 hω.2
    unfold nxt lin
    calc _ ≤ _ := this
      _ = _ := by ring

noncomputable def Fq (S : Sys Ω) (M y : ℝ) : ℝ :=
  S.p * (1 - 2 * S.R * S.mu) * y - S.p * S.R * y ^ 2 / M + S.p * S.muTilde * M

lemma integral_F (S : Sys Ω) (hS : S.Standing) {M : ℝ} (hM : M ≠ 0) (y : ℝ) :
    ∫ ω, S.p * (y + S.beta ω * M) * (1 - S.R * (y + S.beta ω * M) / M) ∂S.P = Fq S M y := by
  haveI := hS.isProb
  have hb : Integrable S.beta S.P := hS.beta_memLp.integrable one_le_two
  have hb2 : Integrable (fun ω => S.beta ω ^ 2) S.P := hS.beta_memLp.integrable_sq
  have hvar : S.sigma2 = ∫ ω, S.beta ω ^ 2 ∂S.P - S.mu ^ 2 := by
    unfold Sys.sigma2 Sys.mu
    rw [variance_eq_sub hS.beta_memLp]
    simp [Pi.pow_apply]
  have hpt : ∀ ω, S.p * (y + S.beta ω * M) * (1 - S.R * (y + S.beta ω * M) / M)
      = ((S.p * y - S.p * S.R * y ^ 2 / M) + (S.p * M - 2 * S.p * S.R * y) * S.beta ω)
        + (- S.p * S.R * M) * S.beta ω ^ 2 := by
    intro ω
    field_simp
    ring
  simp_rw [hpt]
  have h1 : Integrable (fun ω => (S.p * y - S.p * S.R * y ^ 2 / M)
      + (S.p * M - 2 * S.p * S.R * y) * S.beta ω) S.P :=
    (integrable_const _).add (hb.const_mul _)
  rw [integral_add h1 (hb2.const_mul _), integral_add (integrable_const _) (hb.const_mul _),
    integral_const, integral_const_mul, integral_const_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold Fq Sys.muTilde
  rw [hvar]
  unfold Sys.mu
  ring

lemma stage_eq (S : Sys Ω) (hS : S.Standing) (W : ℝ → ℝ → ℝ) {M : ℝ} (hM : M ≠ 0) (D y : ℝ) :
    S.stage W M D y = S.r * (D - y) + Fq S M y + S.gam * ∫ ω, nxt S W M D y ω ∂S.P := by
  unfold Sys.stage nxt
  rw [integral_F S hS hM]

lemma Vto_succ (S : Sys Ω) (k : ℕ) (M D : ℝ) :
    S.Vto (k + 1) M D = sSup (S.stage (S.Vto k) M D '' Set.Icc 0 D) := rfl

lemma Vto_le (S : Sys Ω) {k : ℕ} {M D c : ℝ} (hD : 0 ≤ D)
    (h : ∀ y ∈ Set.Icc 0 D, S.stage (S.Vto k) M D y ≤ c) : S.Vto (k + 1) M D ≤ c := by
  rw [Vto_succ]
  apply csSup_le ((Set.nonempty_Icc.2 hD).image _)
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

lemma le_Vto (S : Sys Ω) {k : ℕ} {M D c y : ℝ}
    (hb : ∀ y ∈ Set.Icc 0 D, S.stage (S.Vto k) M D y ≤ c)
    (hy : y ∈ Set.Icc 0 D) : S.stage (S.Vto k) M D y ≤ S.Vto (k + 1) M D := by
  rw [Vto_succ]
  refine le_csSup ⟨c, ?_⟩ (Set.mem_image_of_mem _ hy)
  rintro _ ⟨z, hz, rfl⟩
  exact hb z hz

lemma quad_bound {k y M a : ℝ} (hM : 0 < M) (ha : 0 < a) (hy : 0 ≤ y) :
    k * y - a * y ^ 2 / M ≤ (max k 0) ^ 2 / (4 * a) * M := by
  rcases le_total k 0 with hk | hk
  · rw [max_eq_right hk]
    have : 0 ≤ a * y ^ 2 / M := by positivity
    have : k * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk hy
    simp
    linarith
  · rw [max_eq_left hk]
    have h : k * y - a * y ^ 2 / M - k ^ 2 / (4 * a) * M = -(2 * a * y - M * k) ^ 2 / (4 * a * M) := by
      field_simp
      ring
    have h2 : -(2 * a * y - M * k) ^ 2 / (4 * a * M) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith [sq_nonneg (2 * a * y - M * k)]
      · positivity
    linarith

lemma contOn_of_lip (W : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ M1 M2 D : ℝ, 0 < M1 → M1 ≤ M2 → 0 ≤ D → |W M2 D - W M1 D| ≤ K * (M2 - M1))
    (hD : ∀ M D1 D2 : ℝ, 0 < M → 0 ≤ D1 → D1 ≤ D2 → |W M D2 - W M D1| ≤ K * (D2 - D1)) :
    ContinuousOn (Function.uncurry W) dom := by
  have hM' : ∀ M1 M2 D : ℝ, 0 < M1 → 0 < M2 → 0 ≤ D → |W M2 D - W M1 D| ≤ K * |M2 - M1| := by
    intro M1 M2 D h1 h2 hD0
    rcases le_total M1 M2 with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact hM M1 M2 D h1 h hD0
    · rw [abs_sub_comm, abs_sub_comm M2 M1, abs_of_nonneg (sub_nonneg.2 h)]
      exact hM M2 M1 D h2 h hD0
  have hD' : ∀ M D1 D2 : ℝ, 0 < M → 0 ≤ D1 → 0 ≤ D2 → |W M D2 - W M D1| ≤ K * |D2 - D1| := by
    intro M D1 D2 h0 h1 h2
    rcases le_total D1 D2 with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact hD M D1 D2 h0 h1 h
    · rw [abs_sub_comm, abs_sub_comm D2 D1, abs_of_nonneg (sub_nonneg.2 h)]
      exact hD M D2 D1 h0 h2 h
  have hlip : LipschitzOnWith (Real.toNNReal (2 * K)) (Function.uncurry W) dom := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd⟩
    simp only [Function.uncurry_apply_pair, Real.dist_eq, Prod.dist_eq]
    rw [Real.coe_toNNReal _ (by positivity)]
    have h1 := hM' c a b hc ha hb
    have h2 := hD' c d b hc hd hb
    have h3 : |W a b - W c d| ≤ |W a b - W c b| + |W c b - W c d| := abs_sub_le _ _ _
    have h4 : |a - c| ≤ max |a - c| |b - d| := le_max_left _ _
    have h5 : |b - d| ≤ max |a - c| |b - d| := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left h4 hK, mul_le_mul_of_nonneg_left h5 hK]
  exact hlip.continuousOn

/-! ### the bounding sequences -/

noncomputable def ell (S : Sys Ω) : ℕ → ℝ
  | 0 => 0
  | k + 1 => S.r + S.gam * S.eta * ell S k

noncomputable def ee (S : Sys Ω) : ℕ → ℝ
  | 0 => 0
  | k + 1 => S.gam * (ell S k * Eeps S + ee S k)

noncomputable def gg (S : Sys Ω) : ℕ → ℝ
  | 0 => 0
  | k + 1 => S.p * S.muTilde + S.gam * (ell S k * S.muTheta)
      + S.gam * gg S k * (S.rho + S.delta * S.R * S.mu)

noncomputable def upd (S : Sys Ω) (l u : ℝ) : ℝ :=
  S.p * S.muTilde + S.gam * (l * S.muTheta) + S.gam * u * (S.rho + S.delta * S.R * S.mu)
    + (max (2 * S.p * S.R * (S.mu0 - S.mu) + S.gam * u * S.delta * S.R) 0) ^ 2 / (4 * (S.p * S.R))

noncomputable def uu (S : Sys Ω) : ℕ → ℝ
  | 0 => 0
  | k + 1 => upd S (ell S k) (uu S k)

noncomputable def kd (S : Sys Ω) : ℕ → ℝ
  | 0 => 0
  | k + 1 => S.r + |S.p * (1 - 2 * S.R * S.mu)|
      + S.gam * (max (uu S k) 0 * (S.delta * S.R) + S.eta * kd S k)

def Upper (S : Sys Ω) (k : ℕ) (u : ℝ) : Prop :=
  ∀ M D : ℝ, 0 < M → 0 ≤ D → S.Vto k M D ≤ ell S k * D + ee S k + u * M

structure Inv (S : Sys Ω) (k : ℕ) : Prop where
  lo : ∀ M D : ℝ, 0 < M → 0 ≤ D → ell S k * D + ee S k + gg S k * M ≤ S.Vto k M D
  up : Upper S k (uu S k)
  i1 : ∀ M1 M2 D : ℝ, 0 < M1 → M1 ≤ M2 → 0 ≤ D →
    gg S k * (M2 - M1) ≤ S.Vto k M2 D - S.Vto k M1 D
  i2 : ∀ M D1 D2 : ℝ, 0 < M → 0 ≤ D1 → D1 ≤ D2 →
    ell S k * (D2 - D1) ≤ S.Vto k M D2 - S.Vto k M D1
  du : ∀ M D1 D2 : ℝ, 0 < M → 0 ≤ D1 → D1 ≤ D2 →
    S.Vto k M D2 - S.Vto k M D1 ≤ kd S k * (D2 - D1)
  pp : ∀ lam M D D1 : ℝ, 0 < lam → lam ≤ 1 → 0 < M → 0 ≤ D → lam * D ≤ D1 →
    lam * S.Vto k M D + ell S k * (D1 - lam * D) + (1 - lam) * ee S k ≤ S.Vto k (lam * M) D1

lemma mup (S : Sys Ω) {k : ℕ} (hI : Inv S k) {u : ℝ} (hU : Upper S k u)
    {M1 M2 D : ℝ} (h1 : 0 < M1) (h12 : M1 ≤ M2) (hD : 0 ≤ D) :
    S.Vto k M2 D - S.Vto k M1 D ≤ u * (M2 - M1) := by
  have h2 : 0 < M2 := lt_of_lt_of_le h1 h12
  set lam := M1 / M2 with hlam
  have hl0 : 0 < lam := div_pos h1 h2
  have hl1 : lam ≤ 1 := (div_le_one h2).2 h12
  have hlM : lam * M2 = M1 := div_mul_cancel₀ M1 h2.ne'
  have hp := hI.pp lam M2 D D hl0 hl1 h2 hD (by nlinarith)
  rw [hlM] at hp
  have hu := hU M2 D h2 hD
  have hA : (1 - lam) * (S.Vto k M2 D - ell S k * D - ee S k) ≤ (1 - lam) * (u * M2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hB : u * ((1 - lam) * M2) = u * (M2 - M1) := by rw [sub_mul, one_mul, hlM]
  linarith

lemma reg_of_inv (S : Sys Ω) {k : ℕ} (hI : Inv S k) : Reg (S.Vto k) := by
  constructor
  · apply contOn_of_lip _ (|gg S k| + |uu S k| + |ell S k| + |kd S k|) (by positivity)
    · intro M1 M2 D h1 h12 hD
      have hlo := hI.i1 M1 M2 D h1 h12 hD
      have hup := mup S hI hI.up h1 h12 hD
      have hd : 0 ≤ M2 - M1 := by linarith
      have a1 : -(|gg S k|) * (M2 - M1) ≤ gg S k * (M2 - M1) :=
        mul_le_mul_of_nonneg_right (neg_abs_le _) hd
      have a2 : uu S k * (M2 - M1) ≤ |uu S k| * (M2 - M1) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hd
      have a3 : 0 ≤ (|ell S k| + |kd S k|) * (M2 - M1) := by positivity
      have a4 : 0 ≤ |gg S k| * (M2 - M1) := by positivity
      have a5 : 0 ≤ |uu S k| * (M2 - M1) := by positivity
      rw [abs_le]
      constructor <;> linarith
    · intro M D1 D2 h0 h1 h12
      have hlo := hI.i2 M D1 D2 h0 h1 h12
      have hup := hI.du M D1 D2 h0 h1 h12
      have hd : 0 ≤ D2 - D1 := by linarith
      have a1 : -(|ell S k|) * (D2 - D1) ≤ ell S k * (D2 - D1) :=
        mul_le_mul_of_nonneg_right (neg_abs_le _) hd
      have a2 : kd S k * (D2 - D1) ≤ |kd S k| * (D2 - D1) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hd
      have a3 : 0 ≤ (|gg S k| + |uu S k|) * (D2 - D1) := by positivity
      have a4 : 0 ≤ |ell S k| * (D2 - D1) := by positivity
      have a5 : 0 ≤ |kd S k| * (D2 - D1) := by positivity
      rw [abs_le]
      constructor <;> linarith
  · refine ⟨|ell S k| + |ee S k| + |gg S k| + |uu S k|, ?_⟩
    intro M D hM hD
    have hlo := hI.lo M D hM hD
    have hup := hI.up M D hM hD
    have b1 : -(|ell S k|) * D ≤ ell S k * D := mul_le_mul_of_nonneg_right (neg_abs_le _) hD
    have b2 : ell S k * D ≤ |ell S k| * D := mul_le_mul_of_nonneg_right (le_abs_self _) hD
    have b3 : -(|gg S k|) * M ≤ gg S k * M := mul_le_mul_of_nonneg_right (neg_abs_le _) hM.le
    have b4 : uu S k * M ≤ |uu S k| * M := mul_le_mul_of_nonneg_right (le_abs_self _) hM.le
    have b5 := neg_abs_le (ee S k)
    have b6 := le_abs_self (ee S k)
    have c1 : 0 ≤ |ell S k| * M := by positivity
    have c2 : 0 ≤ |ee S k| * M := by positivity
    have c3 : 0 ≤ |ee S k| * D := by positivity
    have c4 : 0 ≤ |gg S k| * D := by positivity
    have c5 : 0 ≤ |uu S k| * D := by positivity
    have c6 : 0 ≤ |gg S k| := abs_nonneg _
    have c7 : 0 ≤ |uu S k| := abs_nonneg _
    have c8 : 0 ≤ |ell S k| := abs_nonneg _
    have c9 : 0 ≤ |gg S k| * M := by positivity
    have c10 : 0 ≤ |uu S k| * M := by positivity
    rw [abs_le]
    constructor <;> nlinarith

lemma two_pR_mu0 (S : Sys Ω) (hS : S.Standing) : 2 * S.p * S.R * S.mu0 = S.p - S.r := by
  have hp := hS.p_pos
  have hR := R_pos S hS
  unfold Sys.mu0
  field_simp

lemma stage_upper (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hreg : Reg (S.Vto k)) {u : ℝ}
    (hU : Upper S k u) {M D : ℝ} (hM : 0 < M) (hD : 0 ≤ D) :
    ∀ y ∈ Set.Icc 0 D, S.stage (S.Vto k) M D y
      ≤ ell S (k + 1) * D + ee S (k + 1) + upd S (ell S k) u * M := by
  have := hS.isProb
  intro y hy
  rw [stage_eq S hS _ hM.ne']
  have hJ := int_le S hS (integrable_nxt S hS hreg hM hD hy.1) (integrable_const (0:ℝ))
    (ell S k * S.eta * D + ee S k + u * (S.rho * M + S.delta * S.R * y))
    (u * (S.delta * S.R * M)) (ell S k * M) (ell S k) (by
      filter_upwards [nxt_mem S hS hM hD hy.1] with ω hω
      have := hU _ _ hω.1 hω.2
      unfold nxt lin
      calc _ ≤ _ := this
        _ = _ := by ring)
  simp only [integral_const, smul_eq_mul, mul_zero, zero_add] at hJ
  have hγ := hS.gam_nonneg
  have hJ' := mul_le_mul_of_nonneg_left hJ hγ
  have hq := quad_bound (k := 2 * S.p * S.R * (S.mu0 - S.mu) + S.gam * u * S.delta * S.R)
    (a := S.p * S.R) hM (mul_pos hS.p_pos (R_pos S hS)) hy.1
  have hm0 := two_pR_mu0 S hS
  have hm0y : 2 * S.p * S.R * S.mu0 * y = (S.p - S.r) * y := by rw [hm0]
  rw [show ell S (k + 1) = S.r + S.gam * S.eta * ell S k from rfl,
    show ee S (k + 1) = S.gam * (ell S k * Eeps S + ee S k) from rfl]
  unfold Fq upd
  linarith

lemma upper_step (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hreg : Reg (S.Vto k)) {u : ℝ}
    (hU : Upper S k u) : Upper S (k + 1) (upd S (ell S k) u) := by
  intro M D hM hD
  exact Vto_le S hD (stage_upper S hS hreg hU hM hD)

lemma Fq_scale (S : Sys Ω) {lam M : ℝ} (hl : lam ≠ 0) (hM : M ≠ 0) (y : ℝ) :
    Fq S (lam * M) (lam * y) = lam * Fq S M y := by
  unfold Fq
  field_simp

lemma lo_step (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hI : Inv S k) {M D : ℝ}
    (hM : 0 < M) (hD : 0 ≤ D) :
    ell S (k + 1) * D + ee S (k + 1) + gg S (k + 1) * M ≤ S.Vto (k + 1) M D := by
  have := hS.isProb
  have hreg := reg_of_inv S hI
  have h0 : (0:ℝ) ∈ Set.Icc 0 D := ⟨le_refl 0, hD⟩
  refine le_trans ?_ (le_Vto S (stage_upper S hS hreg hI.up hM hD) h0)
  rw [stage_eq S hS _ hM.ne']
  have hJ := int_ge S hS (integrable_nxt S hS hreg hM hD (le_refl 0)) (integrable_const (0:ℝ))
    (ell S k * S.eta * D + ee S k + gg S k * (S.rho * M))
    (gg S k * (S.delta * S.R * M)) (ell S k * M) (ell S k) (by
      filter_upwards [nxt_mem S hS hM hD (le_refl 0)] with ω hm
      obtain ⟨hA, hB⟩ : 0 < (S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * 0 ∧
          0 ≤ S.eta * D + S.theta ω * M + S.eps ω := hm
      have e := hI.lo _ _ hA hB
      unfold nxt lin
      linarith)
  simp only [integral_const, smul_eq_mul, mul_zero, zero_add] at hJ
  have hJ' := mul_le_mul_of_nonneg_left hJ hS.gam_nonneg
  rw [show ell S (k + 1) = S.r + S.gam * S.eta * ell S k from rfl,
    show ee S (k + 1) = S.gam * (ell S k * Eeps S + ee S k) from rfl,
    show gg S (k + 1) = S.p * S.muTilde + S.gam * (ell S k * S.muTheta)
      + S.gam * gg S k * (S.rho + S.delta * S.R * S.mu) from rfl]
  unfold Fq
  have hz : S.p * S.R * (0:ℝ) ^ 2 / M = 0 := by simp
  linarith

lemma i1_step (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hI : Inv S k) {M1 M2 D : ℝ}
    (h1 : 0 < M1) (h12 : M1 ≤ M2) (hD : 0 ≤ D) :
    gg S (k + 1) * (M2 - M1) ≤ S.Vto (k + 1) M2 D - S.Vto (k + 1) M1 D := by
  have := hS.isProb
  have hreg := reg_of_inv S hI
  have h2 : 0 < M2 := lt_of_lt_of_le h1 h12
  suffices H : S.Vto (k + 1) M1 D ≤ S.Vto (k + 1) M2 D - gg S (k + 1) * (M2 - M1) by linarith
  apply Vto_le S hD
  intro y hy
  have hV := le_Vto S (stage_upper S hS hreg hI.up h2 hD) hy
  rw [stage_eq S hS _ h2.ne'] at hV
  rw [stage_eq S hS _ h1.ne']
  have hJ := int_ge S hS (integrable_nxt S hS hreg h2 hD hy.1) (integrable_nxt S hS hreg h1 hD hy.1)
    (gg S k * (S.rho * (M2 - M1))) (gg S k * (S.delta * S.R * (M2 - M1))) (ell S k * (M2 - M1)) 0 (by
      filter_upwards [nxt_mem S hS h1 hD hy.1, nxt_mem S hS h2 hD hy.1, hS.growth_pos,
        hS.theta_nonneg] with ω hm1 hm2 ha hθ
      obtain ⟨hA1, hB1⟩ : 0 < (S.rho + S.delta * S.R * S.beta ω) * M1 + S.delta * S.R * y ∧
          0 ≤ S.eta * D + S.theta ω * M1 + S.eps ω := hm1
      obtain ⟨hA2, hB2⟩ : 0 < (S.rho + S.delta * S.R * S.beta ω) * M2 + S.delta * S.R * y ∧
          0 ≤ S.eta * D + S.theta ω * M2 + S.eps ω := hm2
      have hMle : (S.rho + S.delta * S.R * S.beta ω) * M1 + S.delta * S.R * y
          ≤ (S.rho + S.delta * S.R * S.beta ω) * M2 + S.delta * S.R * y := by
        nlinarith [mul_le_mul_of_nonneg_left h12 ha.le]
      have hDle : S.eta * D + S.theta ω * M1 + S.eps ω ≤ S.eta * D + S.theta ω * M2 + S.eps ω := by
        nlinarith [mul_le_mul_of_nonneg_left h12 hθ]
      have e1 := hI.i1 _ _ _ hA1 hMle hB2
      have e2 := hI.i2 _ _ _ hA1 hB1 hDle
      unfold nxt lin
      linarith)
  have hJ' := mul_le_mul_of_nonneg_left hJ hS.gam_nonneg
  have hq : S.p * S.R * y ^ 2 / M2 ≤ S.p * S.R * y ^ 2 / M1 :=
    div_le_div_of_nonneg_left (by have := (mul_pos hS.p_pos (R_pos S hS)).le; positivity) h1 h12
  rw [show gg S (k + 1) = S.p * S.muTilde + S.gam * (ell S k * S.muTheta)
      + S.gam * gg S k * (S.rho + S.delta * S.R * S.mu) from rfl]
  unfold Fq at hV ⊢
  linarith

lemma i2_step (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hI : Inv S k) {M D1 D2 : ℝ}
    (h0 : 0 < M) (h1 : 0 ≤ D1) (h12 : D1 ≤ D2) :
    ell S (k + 1) * (D2 - D1) ≤ S.Vto (k + 1) M D2 - S.Vto (k + 1) M D1 := by
  have := hS.isProb
  have hreg := reg_of_inv S hI
  have h2 : 0 ≤ D2 := le_trans h1 h12
  suffices H : S.Vto (k + 1) M D1 ≤ S.Vto (k + 1) M D2 - ell S (k + 1) * (D2 - D1) by linarith
  apply Vto_le S h1
  intro y hy
  have hy2 : y ∈ Set.Icc 0 D2 := ⟨hy.1, le_trans hy.2 h12⟩
  have hV := le_Vto S (stage_upper S hS hreg hI.up h0 h2) hy2
  rw [stage_eq S hS _ h0.ne'] at hV
  rw [stage_eq S hS _ h0.ne']
  have hJ := int_ge S hS (integrable_nxt S hS hreg h0 h2 hy.1) (integrable_nxt S hS hreg h0 h1 hy.1)
    (ell S k * (S.eta * (D2 - D1))) 0 0 0 (by
      filter_upwards [nxt_mem S hS h0 h1 hy.1] with ω hm1
      obtain ⟨hA1, hB1⟩ : 0 < (S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y ∧
          0 ≤ S.eta * D1 + S.theta ω * M + S.eps ω := hm1
      have hDle : S.eta * D1 + S.theta ω * M + S.eps ω ≤ S.eta * D2 + S.theta ω * M + S.eps ω := by
        nlinarith [mul_le_mul_of_nonneg_left h12 hS.eta_nonneg]
      have e2 := hI.i2 _ _ _ hA1 hB1 hDle
      unfold nxt lin
      linarith)
  have hJ' := mul_le_mul_of_nonneg_left hJ hS.gam_nonneg
  rw [show ell S (k + 1) = S.r + S.gam * S.eta * ell S k from rfl]
  linarith

lemma du_step (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hI : Inv S k) {M D1 D2 : ℝ}
    (h0 : 0 < M) (h1 : 0 ≤ D1) (h12 : D1 ≤ D2) :
    S.Vto (k + 1) M D2 - S.Vto (k + 1) M D1 ≤ kd S (k + 1) * (D2 - D1) := by
  have := hS.isProb
  have hreg := reg_of_inv S hI
  have h2 : 0 ≤ D2 := le_trans h1 h12
  suffices H : S.Vto (k + 1) M D2 ≤ S.Vto (k + 1) M D1 + kd S (k + 1) * (D2 - D1) by linarith
  apply Vto_le S h2
  intro y2 hy2
  obtain ⟨y1, hy1, hy12, hy21⟩ : ∃ y1 : ℝ, y1 ∈ Set.Icc 0 D1 ∧ y1 ≤ y2 ∧ y2 - y1 ≤ D2 - D1 := by
    rcases le_total y2 D1 with h | h
    · exact ⟨y2, ⟨hy2.1, h⟩, le_refl _, by linarith⟩
    · exact ⟨D1, ⟨h1, le_refl _⟩, h, by linarith [hy2.2]⟩
  have hV := le_Vto S (stage_upper S hS hreg hI.up h0 h1) hy1
  rw [stage_eq S hS _ h0.ne'] at hV
  rw [stage_eq S hS _ h0.ne']
  have hδR : 0 ≤ S.delta * S.R := mul_nonneg hS.delta_nonneg (R_pos S hS).le
  have hJ := int_le S hS (integrable_nxt S hS hreg h0 h2 hy2.1) (integrable_nxt S hS hreg h0 h1 hy1.1)
    (uu S k * (S.delta * S.R * (y2 - y1)) + kd S k * (S.eta * (D2 - D1))) 0 0 0 (by
      filter_upwards [nxt_mem S hS h0 h1 hy1.1, nxt_mem S hS h0 h2 hy2.1] with ω hm1 hm2
      obtain ⟨hA1, hB1⟩ : 0 < (S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y1 ∧
          0 ≤ S.eta * D1 + S.theta ω * M + S.eps ω := hm1
      obtain ⟨hA2, hB2⟩ : 0 < (S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y2 ∧
          0 ≤ S.eta * D2 + S.theta ω * M + S.eps ω := hm2
      have hMle : (S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y1
          ≤ (S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y2 := by
        nlinarith [mul_le_mul_of_nonneg_left hy12 hδR]
      have hDle : S.eta * D1 + S.theta ω * M + S.eps ω ≤ S.eta * D2 + S.theta ω * M + S.eps ω := by
        nlinarith [mul_le_mul_of_nonneg_left h12 hS.eta_nonneg]
      have e1 := mup S hI hI.up hA1 hMle hB2
      have e2 := hI.du _ _ _ hA1 hB1 hDle
      unfold nxt lin
      linarith)
  have hJ' := mul_le_mul_of_nonneg_left hJ hS.gam_nonneg
  have hd : 0 ≤ y2 - y1 := sub_nonneg.2 hy12
  have hA : S.p * (1 - 2 * S.R * S.mu) * (y2 - y1) ≤ |S.p * (1 - 2 * S.R * S.mu)| * (D2 - D1) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) hd)
      (mul_le_mul_of_nonneg_left hy21 (abs_nonneg _))
  have hB : uu S k * (y2 - y1) ≤ max (uu S k) 0 * (D2 - D1) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
      (mul_le_mul_of_nonneg_left hy21 (le_max_right _ _))
  have hB' := mul_le_mul_of_nonneg_left hB (mul_nonneg hS.gam_nonneg hδR)
  have hsq : S.p * S.R * y1 ^ 2 / M ≤ S.p * S.R * y2 ^ 2 / M := by
    apply div_le_div_of_nonneg_right _ h0.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy1.1 hy12 2)
      (mul_pos hS.p_pos (R_pos S hS)).le
  have hr : 0 ≤ S.r * (y2 - y1) := mul_nonneg hS.r_nonneg hd
  rw [show kd S (k + 1) = S.r + |S.p * (1 - 2 * S.R * S.mu)|
      + S.gam * (max (uu S k) 0 * (S.delta * S.R) + S.eta * kd S k) from rfl]
  unfold Fq at hV ⊢
  linarith

lemma pp_step (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hI : Inv S k) {lam M D D1 : ℝ}
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (hM : 0 < M) (hD : 0 ≤ D) (hD1 : lam * D ≤ D1) :
    lam * S.Vto (k + 1) M D + ell S (k + 1) * (D1 - lam * D) + (1 - lam) * ee S (k + 1)
      ≤ S.Vto (k + 1) (lam * M) D1 := by
  have := hS.isProb
  have hreg := reg_of_inv S hI
  have hD1' : 0 ≤ D1 := le_trans (mul_nonneg hl0.le hD) hD1
  have hlM : 0 < lam * M := mul_pos hl0 hM
  suffices H : S.Vto (k + 1) M D ≤ (S.Vto (k + 1) (lam * M) D1
      - (ell S (k + 1) * (D1 - lam * D) + (1 - lam) * ee S (k + 1))) / lam by
    rw [le_div_iff₀ hl0] at H
    linarith
  apply Vto_le S hD
  intro y hy
  rw [le_div_iff₀ hl0]
  have hly : lam * y ∈ Set.Icc 0 D1 :=
    ⟨mul_nonneg hl0.le hy.1, le_trans (mul_le_mul_of_nonneg_left hy.2 hl0.le) hD1⟩
  have hV := le_Vto S (stage_upper S hS hreg hI.up hlM hD1') hly
  rw [stage_eq S hS _ hlM.ne', Fq_scale S hl0.ne' hM.ne'] at hV
  rw [stage_eq S hS _ hM.ne']
  have hJ := int_ge S hS (integrable_nxt S hS hreg hlM hD1' hly.1)
    ((integrable_nxt S hS hreg hM hD hy.1).const_mul lam)
    (ell S k * (S.eta * (D1 - lam * D)) + (1 - lam) * ee S k) 0 0 (ell S k * (1 - lam)) (by
      filter_upwards [nxt_mem S hS hM hD hy.1, hS.eps_nonneg] with ω hm hε
      obtain ⟨hA, hB⟩ : 0 < (S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y ∧
          0 ≤ S.eta * D + S.theta ω * M + S.eps ω := hm
      have hle : lam * (S.eta * D + S.theta ω * M + S.eps ω)
          ≤ S.eta * D1 + S.theta ω * (lam * M) + S.eps ω := by
        nlinarith [mul_le_mul_of_nonneg_left hD1 hS.eta_nonneg, mul_nonneg (sub_nonneg.2 hl1) hε]
      have e := hI.pp lam _ _ _ hl0 hl1 hA hB hle
      have hEq : (S.rho + S.delta * S.R * S.beta ω) * (lam * M) + S.delta * S.R * (lam * y)
          = lam * ((S.rho + S.delta * S.R * S.beta ω) * M + S.delta * S.R * y) := by ring
      unfold nxt lin
      rw [hEq]
      beta_reduce
      linarith)
  rw [integral_const_mul] at hJ
  have hJ' := mul_le_mul_of_nonneg_left hJ hS.gam_nonneg
  rw [show ell S (k + 1) = S.r + S.gam * S.eta * ell S k from rfl,
    show ee S (k + 1) = S.gam * (ell S k * Eeps S + ee S k) from rfl]
  linarith

lemma inv_zero (S : Sys Ω) : Inv S 0 where
  lo := by intro M D _ _; simp [Sys.Vto, ell, ee, gg]
  up := by intro M D _ _; simp [Sys.Vto, ell, ee, uu]
  i1 := by intro M1 M2 D _ _ _; simp [Sys.Vto, gg]
  i2 := by intro M D1 D2 _ _ _; simp [Sys.Vto, ell]
  du := by intro M D1 D2 _ _ _; simp [Sys.Vto, kd]
  pp := by intro lam M D D1 _ _ _ _ _; simp [Sys.Vto, ell, ee]

lemma inv_succ (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hI : Inv S k) : Inv S (k + 1) where
  lo := fun _ _ hM hD => lo_step S hS hI hM hD
  up := upper_step S hS (reg_of_inv S hI) hI.up
  i1 := fun _ _ _ h1 h12 hD => i1_step S hS hI h1 h12 hD
  i2 := fun _ _ _ h0 h1 h12 => i2_step S hS hI h0 h1 h12
  du := fun _ _ _ h0 h1 h12 => du_step S hS hI h0 h1 h12
  pp := fun _ _ _ _ hl0 hl1 hM hD hD1 => pp_step S hS hI hl0 hl1 hM hD hD1

lemma inv_all (S : Sys Ω) (hS : S.Standing) : ∀ k, Inv S k
  | 0 => inv_zero S
  | k + 1 => inv_succ S hS (inv_all S hS k)

/-! ### regional consequences -/

lemma mu_nonneg (S : Sys Ω) (hS : S.Standing) : 0 ≤ S.mu :=
  integral_nonneg_of_ae hS.beta_nonneg

lemma mt_nonneg (S : Sys Ω) (hS : S.Standing) : 0 ≤ S.muTheta := hS.muTheta_nonneg

lemma a_nonneg (S : Sys Ω) (hS : S.Standing) : 0 ≤ S.rho + S.delta * S.R * S.mu := by
  have := mul_nonneg (mul_nonneg hS.delta_nonneg (R_pos S hS).le) (mu_nonneg S hS)
  linarith [hS.rho_nonneg]

lemma ell_nonneg (S : Sys Ω) (hS : S.Standing) : ∀ k, 0 ≤ ell S k
  | 0 => le_refl 0
  | k + 1 => by
    have := ell_nonneg S hS k
    have := mul_nonneg (mul_nonneg hS.gam_nonneg hS.eta_nonneg) this
    show 0 ≤ S.r + S.gam * S.eta * ell S k
    linarith [hS.r_nonneg]

lemma ell_succ_le (S : Sys Ω) (hS : S.Standing) : ∀ k, ell S k ≤ ell S (k + 1)
  | 0 => by show (0:ℝ) ≤ S.r + S.gam * S.eta * 0; simp [hS.r_nonneg]
  | k + 1 => by
    have h := ell_succ_le S hS k
    have := mul_le_mul_of_nonneg_left h (mul_nonneg hS.gam_nonneg hS.eta_nonneg)
    show S.r + S.gam * S.eta * ell S k ≤ S.r + S.gam * S.eta * ell S (k + 1)
    linarith

lemma ell_mono (S : Sys Ω) (hS : S.Standing) : Monotone (ell S) :=
  monotone_nat_of_le_succ (ell_succ_le S hS)

lemma ell_le (S : Sys Ω) (hS : S.Standing) (hx : S.gam * S.eta < 1) :
    ∀ k, ell S k ≤ S.r * (1 - S.gam * S.eta)⁻¹
  | 0 => by
    show (0:ℝ) ≤ _
    have : 0 < 1 - S.gam * S.eta := by linarith
    have := hS.r_nonneg
    positivity
  | k + 1 => by
    have h := ell_le S hS hx k
    have hx0 : 0 ≤ S.gam * S.eta := mul_nonneg hS.gam_nonneg hS.eta_nonneg
    have hpos : 0 < 1 - S.gam * S.eta := by linarith
    show S.r + S.gam * S.eta * ell S k ≤ _
    have h2 := mul_le_mul_of_nonneg_left h hx0
    have h3 : S.r + S.gam * S.eta * (S.r * (1 - S.gam * S.eta)⁻¹) = S.r * (1 - S.gam * S.eta)⁻¹ := by
      field_simp
      ring
    linarith

lemma costly_of_upper (S : Sys Ω) (hS : S.Standing) {k : ℕ} {u : ℝ} (hU : Upper S k u)
    (hu : u ≤ 0) : ∀ D : ℝ, 0 < D → AntitoneOn (fun M => S.Vto k M D) (Set.Ioi 0) := by
  intro D hD a ha b hb hab
  have h := mup S (inv_all S hS k) hU ha hab hD.le
  have := mul_nonpos_of_nonpos_of_nonneg hu (sub_nonneg.2 hab)
  show S.Vto k b D ≤ S.Vto k a D
  linarith

lemma benefits_of_g (S : Sys Ω) (hS : S.Standing) {k : ℕ} (hg : 0 ≤ gg S k) :
    ∀ D : ℝ, 0 < D → MonotoneOn (fun M => S.Vto k M D) (Set.Ioi 0) := by
  intro D hD a ha b hb hab
  have h := (inv_all S hS k).i1 a b D ha hab hD.le
  have := mul_nonneg hg (sub_nonneg.2 hab)
  show S.Vto k a D ≤ S.Vto k b D
  linarith

lemma upper_zero_R1 (S : Sys Ω) (hS : S.Standing) (h1 : S.InR1) : ∀ k, Upper S k 0
  | 0 => by intro M D _ _; simp [Sys.Vto, ell, ee]
  | k + 1 => by
    have hU := upper_step S hS (reg_of_inv S (inv_all S hS k)) (upper_zero_R1 S hS h1 k)
    obtain ⟨_, _, hx, hlt⟩ := h1
    have hp := hS.p_pos
    have hR := R_pos S hS
    have hpR : 0 < S.p * S.R := mul_pos hp hR
    have hx0 : 0 ≤ S.gam * S.eta := mul_nonneg hS.gam_nonneg hS.eta_nonneg
    have hpos : 0 < 1 - S.gam * S.eta := by linarith
    have hDelta : S.DeltaFin = S.gam * S.r * S.muTheta / S.p * (1 - S.gam * S.eta)⁻¹ := by
      unfold Sys.DeltaFin
      rw [tsum_geometric_of_lt_one hx0 hx]
    have hmax : (max (2 * S.p * S.R * (S.mu0 - S.mu) + S.gam * 0 * S.delta * S.R) 0) ^ 2
        / (4 * (S.p * S.R)) = S.p * S.R * (max (S.mu0 - S.mu) 0) ^ 2 := by
      simp only [mul_zero, zero_mul, add_zero]
      rcases le_total (S.mu0 - S.mu) 0 with h | h
      · rw [max_eq_right h, max_eq_right (by nlinarith)]
        simp
      · rw [max_eq_left h, max_eq_left (by positivity)]
        field_simp
        ring
    have hupd : upd S (ell S k) 0 ≤ 0 := by
      unfold upd
      rw [hmax]
      have hl := ell_le S hS hx k
      have hmt : 0 ≤ S.muTheta := mt_nonneg S hS
      have h4 := mul_le_mul_of_nonneg_left hl (mul_nonneg hS.gam_nonneg hmt)
      have h5 := mul_lt_mul_of_pos_left hlt hpR
      have heq : S.p * S.R * (S.mu / S.R - S.mu ^ 2 + max (S.mu0 - S.mu) 0 ^ 2 + S.DeltaFin / S.R)
          = S.p * S.mu - S.p * S.R * S.mu ^ 2 + S.p * S.R * max (S.mu0 - S.mu) 0 ^ 2
            + S.gam * S.muTheta * (S.r * (1 - S.gam * S.eta)⁻¹) := by
        rw [hDelta]
        field_simp
      unfold Sys.muTilde
      nlinarith
    intro M D hM hD
    have := hU M D hM hD
    have := mul_nonpos_of_nonpos_of_nonneg hupd hM.le
    linarith

lemma gg_nonneg_R2 (S : Sys Ω) (hS : S.Standing) (h2 : S.InR2) : ∀ k, 0 ≤ gg S k
  | 0 => le_refl 0
  | k + 1 => by
    have ih := gg_nonneg_R2 S hS h2 k
    obtain ⟨_, _, hlt⟩ := h2
    have hR := R_pos S hS
    have hmt : 0 < S.muTilde := by
      have h5 := mul_lt_mul_of_pos_left hlt hR
      have heq : S.R * (S.mu / S.R - S.mu ^ 2) = S.mu - S.R * S.mu ^ 2 := by
        field_simp
      unfold Sys.muTilde
      nlinarith
    show 0 ≤ S.p * S.muTilde + S.gam * (ell S k * S.muTheta)
      + S.gam * gg S k * (S.rho + S.delta * S.R * S.mu)
    have := mul_pos hS.p_pos hmt
    have := mul_nonneg hS.gam_nonneg (mul_nonneg (ell_nonneg S hS k) (mt_nonneg S hS))
    have := mul_nonneg (mul_nonneg hS.gam_nonneg ih) (a_nonneg S hS)
    linarith

lemma muTilde_neg_R3 (S : Sys Ω) (hS : S.Standing) (h3 : S.InR3) : S.muTilde < 0 := by
  obtain ⟨_, _, hlt, _⟩ := h3
  have hR := R_pos S hS
  have h5 := mul_lt_mul_of_pos_left hlt hR
  have heq : S.R * (S.mu / S.R - S.mu ^ 2) = S.mu - S.R * S.mu ^ 2 := by
    field_simp
  unfold Sys.muTilde
  nlinarith

lemma upper_affine (S : Sys Ω) (hS : S.Standing) (hμ : S.mu0 ≤ S.mu) :
    ∀ k, (∀ j, j < k → gg S j ≤ 0) → Upper S k (gg S k)
  | 0 => fun _ => by intro M D _ _; simp [Sys.Vto, ell, ee, gg]
  | k + 1 => fun hj => by
    have ih := upper_affine S hS hμ k (fun j hjk => hj j (Nat.lt_succ_of_lt hjk))
    have hgk : gg S k ≤ 0 := hj k (Nat.lt_succ_self k)
    have hU := upper_step S hS (reg_of_inv S (inv_all S hS k)) ih
    have hneg : 2 * S.p * S.R * (S.mu0 - S.mu) + S.gam * gg S k * S.delta * S.R ≤ 0 := by
      have h1 : 2 * S.p * S.R * (S.mu0 - S.mu) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by have := hS.p_pos; have := R_pos S hS; positivity)
          (by linarith)
      have h2 : S.gam * gg S k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hS.gam_nonneg hgk
      have h3 : S.gam * gg S k * S.delta ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h2 hS.delta_nonneg
      have h4 : S.gam * gg S k * S.delta * S.R ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h3 (R_pos S hS).le
      linarith
    have heq : upd S (ell S k) (gg S k) = gg S (k + 1) := by
      unfold upd
      rw [max_eq_right hneg, zero_pow two_ne_zero, zero_div, add_zero]
      rfl
    rw [heq] at hU
    exact hU

lemma g_neg (S : Sys Ω) (hS : S.Standing) :
    ∀ k, S.p * S.muTilde + S.gam * (ell S k * S.muTheta) < 0 → gg S (k + 1) < 0
  | 0 => fun h => by
    show S.p * S.muTilde + S.gam * (ell S 0 * S.muTheta)
      + S.gam * gg S 0 * (S.rho + S.delta * S.R * S.mu) < 0
    simp only [gg, mul_zero, zero_mul, add_zero]
    exact h
  | k + 1 => fun h => by
    have hmono := ell_succ_le S hS k
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono (mt_nonneg S hS))
      hS.gam_nonneg
    have ih := g_neg S hS k (by linarith)
    have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hS.gam_nonneg ih.le)
      (a_nonneg S hS)
    show S.p * S.muTilde + S.gam * (ell S (k + 1) * S.muTheta)
      + S.gam * gg S (k + 1) * (S.rho + S.delta * S.R * S.mu) < 0
    linarith

lemma g_persist (S : Sys Ω) (hS : S.Standing) :
    ∀ j k, j ≤ k → 0 < gg S j → 0 ≤ gg S k := by
  intro j k hjk hj
  cases j with
  | zero => exact absurd hj (by simp [gg])
  | succ i =>
    have hc : 0 ≤ S.p * S.muTilde + S.gam * (ell S i * S.muTheta) := by
      by_contra hcon
      push Not at hcon
      exact absurd (g_neg S hS i hcon) (not_lt.2 hj.le)
    induction k, hjk using Nat.le_induction with
    | base => exact hj.le
    | succ n hn ihn =>
      have hin : i ≤ n := by omega
      have hl := ell_mono S hS hin
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hl (mt_nonneg S hS))
        hS.gam_nonneg
      have := mul_nonneg (mul_nonneg hS.gam_nonneg ihn) (a_nonneg S hS)
      show 0 ≤ S.p * S.muTilde + S.gam * (ell S n * S.muTheta)
        + S.gam * gg S n * (S.rho + S.delta * S.R * S.mu)
      linarith

lemma cl_last (S : Sys Ω) (hS : S.Standing) (hmt : S.muTilde < 0) :
    ∀ D : ℝ, 0 < D → ∃ M0 : ℝ, 0 < M0 ∧ AntitoneOn (fun M => S.Vto 1 M D) (Set.Ici M0) := by
  have := hS.isProb
  intro D hD
  have hR := R_pos S hS
  have hp := hS.p_pos
  have hneg : 0 < -S.muTilde := by linarith
  have hne : S.muTilde ≠ 0 := hmt.ne
  set c := S.R / (-S.muTilde) with hc
  have hc0 : 0 ≤ c := div_nonneg hR.le hneg.le
  have hcm : -S.muTilde * c = S.R := by
    rw [hc]
    field_simp
  refine ⟨(c + 1) * (D + 1), by positivity, ?_⟩
  intro a ha b hb hab
  have ha' : (c + 1) * (D + 1) ≤ a := ha
  have hM0 : 0 < (c + 1) * (D + 1) := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le hM0 ha'
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  show S.Vto 1 b D ≤ S.Vto 1 a D
  apply Vto_le S hD.le
  intro y hy
  refine le_trans ?_ (le_Vto S (stage_upper S hS (reg_of_inv S (inv_zero S)) (inv_zero S).up
    ha0 hD.le) hy)
  rw [stage_eq S hS _ hb0.ne', stage_eq S hS _ ha0.ne']
  have hz : ∀ M : ℝ, ∫ ω, nxt S (S.Vto 0) M D y ω ∂S.P = 0 := by
    intro M
    simp [nxt, Sys.Vto]
  rw [hz, hz]
  have hy2 : y ^ 2 ≤ (D + 1) ^ 2 := by nlinarith [hy.1, hy.2]
  have hab2 : (c + 1) * (D + 1) * ((c + 1) * (D + 1)) ≤ a * b :=
    mul_le_mul ha' (le_trans ha' hab) hM0.le ha0.le
  have hcc : c * (D + 1) ^ 2 ≤ (c + 1) * (D + 1) * ((c + 1) * (D + 1)) := by
    nlinarith [sq_nonneg c, sq_nonneg (D + 1), mul_nonneg (sq_nonneg c) (sq_nonneg (D + 1)),
      mul_nonneg hc0 (sq_nonneg (D + 1))]
  have key : S.R * y ^ 2 ≤ -S.muTilde * (a * b) := by
    calc S.R * y ^ 2 ≤ S.R * (D + 1) ^ 2 := mul_le_mul_of_nonneg_left hy2 hR.le
      _ = -S.muTilde * (c * (D + 1) ^ 2) := by rw [← hcm]; ring
      _ ≤ -S.muTilde * (a * b) :=
        mul_le_mul_of_nonneg_left (le_trans hcc hab2) hneg.le
  have e : S.p * S.R * y ^ 2 / a - S.p * S.R * y ^ 2 / b
      = S.p * (S.R * y ^ 2) * (b - a) / (a * b) := by
    field_simp
  have h2 : S.p * (S.R * y ^ 2) * (b - a) / (a * b) ≤ S.p * (-S.muTilde) * (b - a) := by
    rw [div_le_iff₀ (mul_pos ha0 hb0)]
    have hpb : 0 ≤ S.p * (b - a) := mul_nonneg hp.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left key hpb]
  unfold Fq
  nlinarith

end HOAProof

open HybridOrderAlloc.Thickness in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    (S.InR1 → ∀ t : ℕ, 1 ≤ t → t ≤ S.T → S.Costly t) ∧
    (S.InR2 → ∀ t : ℕ, 1 ≤ t → t ≤ S.T → S.Benefits t) ∧
    (S.InR3 → ∃ τ₁ τ₂ : ℕ, 1 ≤ τ₁ ∧ τ₁ ≤ τ₂ ∧ τ₂ ≤ S.T ∧
      (∀ t : ℕ, 1 ≤ t → t < τ₁ → S.Benefits t) ∧
      (∀ t : ℕ, τ₂ ≤ t → t ≤ S.T → S.CostlyInLimit t) ∧
      (S.mu0 < S.mu → τ₁ = τ₂)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h1 t _ _ D hD
    exact HOAProof.costly_of_upper S hS (HOAProof.upper_zero_R1 S hS h1 (S.T + 1 - t)) le_rfl D hD
  · intro h2 t _ _ D hD
    exact HOAProof.benefits_of_g S hS (HOAProof.gg_nonneg_R2 S hS h2 (S.T + 1 - t)) D hD
  · intro h3
    have hmt := HOAProof.muTilde_neg_R3 S hS h3
    have hT := hS.one_le_T
    by_cases hμ : S.mu0 < S.mu
    · classical
      have hex : ∃ t : ℕ, 1 ≤ t ∧ ∀ j, j ≤ S.T + 1 - t → HOAProof.gg S j ≤ 0 := by
        refine ⟨S.T, hT, ?_⟩
        intro j hj
        have hj1 : j ≤ 1 := by omega
        interval_cases j
        · simp [HOAProof.gg]
        · show S.p * S.muTilde + S.gam * (HOAProof.ell S 0 * S.muTheta)
            + S.gam * HOAProof.gg S 0 * (S.rho + S.delta * S.R * S.mu) ≤ 0
          simp only [HOAProof.ell, HOAProof.gg, zero_mul, mul_zero, add_zero]
          have := mul_neg_of_pos_of_neg hS.p_pos hmt
          linarith
      have hspec := Nat.find_spec hex
      have hτT : Nat.find hex ≤ S.T := Nat.find_min' hex ⟨hT, fun j hj => by
        have hj1 : j ≤ 1 := by omega
        interval_cases j
        · simp [HOAProof.gg]
        · show S.p * S.muTilde + S.gam * (HOAProof.ell S 0 * S.muTheta)
            + S.gam * HOAProof.gg S 0 * (S.rho + S.delta * S.R * S.mu) ≤ 0
          simp only [HOAProof.ell, HOAProof.gg, zero_mul, mul_zero, add_zero]
          have := mul_neg_of_pos_of_neg hS.p_pos hmt
          linarith⟩
      refine ⟨Nat.find hex, Nat.find hex, hspec.1, le_refl _, hτT, ?_, ?_, fun _ => rfl⟩
      · intro t ht1 htτ D hD
        have hnot := Nat.find_min hex htτ
        have hex2 : ∃ j, j ≤ S.T + 1 - t ∧ 0 < HOAProof.gg S j := by
          by_contra hcon
          push Not at hcon
          exact hnot ⟨ht1, hcon⟩
        obtain ⟨j, hj, hjpos⟩ := hex2
        exact HOAProof.benefits_of_g S hS (HOAProof.g_persist S hS j _ hj hjpos) D hD
      · intro t hτt htT D hD
        have hall : ∀ j, j ≤ S.T + 1 - t → HOAProof.gg S j ≤ 0 :=
          fun j hj => hspec.2 j (by omega)
        have hU := HOAProof.upper_affine S hS hμ.le (S.T + 1 - t) (fun j hj => hall j hj.le)
        have hA := HOAProof.costly_of_upper S hS hU (hall _ le_rfl) D hD
        exact ⟨1, one_pos, hA.mono (fun x (hx : (1:ℝ) ≤ x) => (lt_of_lt_of_le one_pos hx : (0:ℝ) < x))⟩
    · refine ⟨1, S.T, le_refl 1, hT, le_refl _, fun t h1 h2 => absurd h2 (not_lt.2 h1), ?_,
        fun h => absurd h hμ⟩
      intro t h1 h2 D hD
      have ht : t = S.T := le_antisymm h2 h1
      subst ht
      have h1' : S.T + 1 - S.T = 1 := by omega
      show ∃ M0 : ℝ, 0 < M0 ∧ AntitoneOn (fun M => S.Vto (S.T + 1 - S.T) M D) (Set.Ici M0)
      rw [h1']
      exact HOAProof.cl_last S hS hmt D hD
