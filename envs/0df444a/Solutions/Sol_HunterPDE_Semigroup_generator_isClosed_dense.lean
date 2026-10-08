-- Prove2me | solution 1 for HunterPDE.Semigroup.generator_isClosed_dense
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:37:56.89047+00:00
-- url     : https://prove2.me/submissions/5236b4af-9a74-44bb-95b2-9a59c7a4afba

import Mathlib
import Definitions.Def_HunterPDE_Semigroup_C0Semigroup

/-!
Hunter, *Notes on PDEs*, Theorem 5.32: the generator of a strongly continuous semigroup is closed and
densely defined.

Proof.  Local boundedness of `‖T t‖` follows from the uniform boundedness principle and strong
continuity at `0⁺` (`local_bound`), and gives continuity of `t ↦ T t f` on `[0, ∞)` (`C0_continuousOn`).
For `F u = ∫₀ᵘ T s f ds` one has `T δ (F h) = F (h + δ) - F δ`, so `F h ∈ D(A)` with `A (F h) = T h f - f`
(`Fint_mem_domain`) and `δ⁻¹ F δ → f` gives density.  For `f ∈ D(A)`, `T t f` has right derivative
`T t (A f)`, so `T h f - f = ∫₀ʰ T s (A f) ds` (`T_sub_eq_Fint`, via a function with vanishing right
derivative).  If `fₙ → f`, `A fₙ → g`, passing to the limit gives `T h f - f = ∫₀ʰ T s g ds`, whence
`(T h f - f)/h → g`, i.e. `f ∈ D(A)` and `A f = g` (`generator_isClosed`).
-/

open Filter
open scoped Topology

namespace HunterPDE.Semigroup

section Basic

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {T : ℝ → X →L[𝕜] X}

theorem local_bound_small (hT : IsC0Semigroup T) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 1 ≤ M ∧ ∀ t, 0 ≤ t → t ≤ δ → ‖T t‖ ≤ M := by
  by_contra hno
  push Not at hno
  have hch : ∀ n : ℕ, ∃ t : ℝ, 0 < t ∧ t ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 < ‖T t‖ := by
    intro n
    obtain ⟨t, ht0, htδ, htM⟩ := hno (1 / ((n : ℝ) + 1)) (by positivity) ((n : ℝ) + 1)
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have : t ≠ 0 := by
      rintro rfl
      have h0 : T 0 = 1 := hT.1
      rw [h0] at htM
      have := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := X)
      have : ‖(1 : X →L[𝕜] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact ⟨t, lt_of_le_of_ne ht0 (Ne.symm this), htδ, htM⟩
  choose t ht0 htδ htM using hch
  have hbd : ∀ f : X, ∃ C : ℝ, ∀ n : ℕ, ‖T (t n) f‖ ≤ C := by
    intro f
    have htend : Tendsto t atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall ht0⟩
      refine squeeze_zero (fun n => (ht0 n).le) htδ ?_
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := ((hT.2.2 f).comp htend).norm.bddAbove_range
    obtain ⟨C, hC⟩ := this
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hbd
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC n
  have := htM n
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]


theorem local_bound (hT : IsC0Semigroup T) (τ : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t, 0 ≤ t → t ≤ τ → ‖T t‖ ≤ M := by
  obtain ⟨δ, hδ, M, hM1, hM⟩ := local_bound_small hT
  have key : ∀ k : ℕ, ∀ t, 0 ≤ t → t ≤ k * δ → ‖T t‖ ≤ M ^ k := by
    intro k
    induction k with
    | zero =>
      intro t ht0 htk
      have : t = 0 := by simp at htk; linarith
      subst this
      rw [hT.1, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      intro t ht0 htk
      by_cases hts : t ≤ δ
      · calc ‖T t‖ ≤ M := hM t ht0 hts
          _ ≤ M ^ (k + 1) := le_self_pow₀ hM1 (by omega)
      · push Not at hts
        have h1 : T t = T δ * T (t - δ) := by
          rw [hT.2.1 δ (t - δ) hδ.le (by linarith)]; congr 1; ring
        have h2 : t - δ ≤ k * δ := by push_cast at htk; linarith
        rw [h1, pow_succ']
        calc ‖T δ * T (t - δ)‖ ≤ ‖T δ‖ * ‖T (t - δ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ M * M ^ k := mul_le_mul (hM δ hδ.le le_rfl) (ih _ (by linarith) h2)
              (norm_nonneg _) (by linarith)
  obtain ⟨k, hk⟩ := exists_nat_ge (τ / δ)
  refine ⟨M ^ k, one_le_pow₀ hM1, fun t ht0 htτ => key k t ht0 ?_⟩
  have : τ ≤ k * δ := by rwa [div_le_iff₀ hδ] at hk
  linarith

theorem C0_continuousOn (hT : IsC0Semigroup T) (f : X) :
    ContinuousOn (fun t => T t f) (Set.Ici 0) := by
  intro t ht
  rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with h0 | hpos
  · subst h0
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have := hT.2.2 f
    rw [ContinuousWithinAt, hT.1]
    simpa using this
  · have hnhds : Set.Ici (0 : ℝ) ∈ 𝓝 t := Ici_mem_nhds hpos
    rw [continuousWithinAt_iff_continuousAt hnhds, continuousAt_iff_continuous_left_right]
    constructor
    · rw [← continuousWithinAt_Iio_iff_Iic]
      -- left continuity
      obtain ⟨M, hM1, hM⟩ := local_bound hT t
      rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun s : ℝ => t - s) (𝓝[<] t) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => t - s) (𝓝 t) (𝓝 (t - t)) :=
            (continuous_const.sub continuous_id).tendsto t
          rw [sub_self] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          simpa using hs
      have h2 : Tendsto (fun s : ℝ => ‖f - T (t - s) f‖) (𝓝[<] t) (𝓝 0) := by
        have := ((hT.2.2 f).comp hlim)
        have h3 := (tendsto_iff_norm_sub_tendsto_zero.mp this)
        simpa [norm_sub_rev] using h3
      refine squeeze_zero' (Eventually.of_forall (fun s => norm_nonneg _)) ?_
        (by simpa using h2.const_mul M)
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (Ici_mem_nhds hpos)] with s hs hs0'
      have hs0 : 0 ≤ s := hs0'
      have hst : s < t := hs
      have h1 : T s f - T t f = - T s (T (t - s) f - f) := by
        have : T t = T s * T (t - s) := by
          rw [hT.2.1 s (t - s) hs0 (by linarith)]; congr 1; ring
        rw [this]; simp [sub_eq_add_neg]
      rw [h1, norm_neg]
      calc ‖T s (T (t - s) f - f)‖ ≤ ‖T s‖ * ‖T (t - s) f - f‖ := (T s).le_opNorm _
        _ ≤ M * ‖f - T (t - s) f‖ := by
          rw [norm_sub_rev (T (t - s) f)]
          exact mul_le_mul (hM s hs0 hst.le) le_rfl (norm_nonneg _) (by linarith)
    · rw [← continuousWithinAt_Ioi_iff_Ici]
      -- right continuity
      rw [ContinuousWithinAt]
      have hlim : Tendsto (fun s : ℝ => s - t) (𝓝[>] t) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (t - t)) :=
            (continuous_id.sub continuous_const).tendsto t
          rw [sub_self] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          simpa using hs
      have h2 := ((T t).continuous.tendsto f).comp ((hT.2.2 f).comp hlim)
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hst : t < s := hs
      simp only [Function.comp]
      have : T s = T t * T (s - t) := by
        rw [hT.2.1 t (s - t) hpos.le (by linarith)]; congr 1; ring
      rw [this]; rfl


section Integral

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

/-- The orbit extended continuously to negative times by `T 0 f`. -/
noncomputable def phi (T : ℝ → X →L[𝕜] X) (f : X) (s : ℝ) : X := T (max s 0) f

theorem phi_continuous (hT : IsC0Semigroup T) (f : X) : Continuous (phi T f) :=
  (C0_continuousOn hT f).comp_continuous (continuous_id.max continuous_const)
    (fun s => Set.mem_Ici.mpr (le_max_right _ _))

theorem phi_of_nonneg {f : X} {s : ℝ} (hs : 0 ≤ s) : phi T f s = T s f := by
  simp [phi, max_eq_left hs]

/-- `F u = ∫₀ᵘ T s f ds`. -/
noncomputable def Fint (T : ℝ → X →L[𝕜] X) (f : X) (u : ℝ) : X := ∫ s in (0 : ℝ)..u, phi T f s

theorem Fint_hasDerivAt (hT : IsC0Semigroup T) (f : X) (u : ℝ) :
    HasDerivAt (Fint T f) (phi T f u) u :=
  ((phi_continuous hT f).integral_hasStrictDerivAt 0 u).hasDerivAt

theorem smul_real_eq (δ : ℝ) (v : X) : ((δ⁻¹ : ℝ) : 𝕜) • v = δ⁻¹ • v := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]

theorem T_comp_Fint (hT : IsC0Semigroup T) (f : X) {h δ : ℝ} (hh : 0 ≤ h) (hδ : 0 ≤ δ) :
    T δ (Fint T f h) = Fint T f (h + δ) - Fint T f δ := by
  unfold Fint
  have hint : IntervalIntegrable (phi T f) MeasureTheory.volume 0 h :=
    (phi_continuous hT f).intervalIntegrable _ _
  have h1 : T δ (∫ s in (0 : ℝ)..h, phi T f s) = ∫ s in (0 : ℝ)..h, T δ (phi T f s) :=
    (T δ).intervalIntegral_comp_comm hint |>.symm
  have h2 : ∫ s in (0 : ℝ)..h, T δ (phi T f s) = ∫ s in (0 : ℝ)..h, phi T f (s + δ) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hs' : 0 ≤ s := by
      rw [Set.uIcc_of_le hh] at hs; exact hs.1
    rw [phi_of_nonneg hs', phi_of_nonneg (by linarith), ← ContinuousLinearMap.mul_apply,
      hT.2.1 δ s hδ hs', add_comm]
  rw [h1, h2, intervalIntegral.integral_comp_add_right, zero_add,
    ← intervalIntegral.integral_interval_sub_left
      ((phi_continuous hT f).intervalIntegrable _ _) ((phi_continuous hT f).intervalIntegrable _ _)]

theorem Fint_mem_domain (hT : IsC0Semigroup T) {A : X →ₗ.[𝕜] X} (hA : IsGenerator T A) (f : X)
    {h : ℝ} (hh : 0 ≤ h) :
    ∃ hm : Fint T f h ∈ A.domain, A ⟨Fint T f h, hm⟩ = T h f - f := by
  have hlim : Tendsto (fun δ : ℝ => ((δ⁻¹ : ℝ) : 𝕜) • (T δ (Fint T f h) - Fint T f h))
      (𝓝[>] 0) (𝓝 (T h f - f)) := by
    have e1 := (Fint_hasDerivAt hT f h)
    have e2 := (Fint_hasDerivAt hT f 0)
    have s1 : Tendsto (fun δ : ℝ => δ⁻¹ • (Fint T f (h + δ) - Fint T f h)) (𝓝[>] 0)
        (𝓝 (phi T f h)) :=
      (hasDerivAt_iff_tendsto_slope_zero.mp e1).mono_left (nhdsGT_le_nhdsNE 0)
    have s2 : Tendsto (fun δ : ℝ => δ⁻¹ • (Fint T f (0 + δ) - Fint T f 0)) (𝓝[>] 0)
        (𝓝 (phi T f 0)) :=
      (hasDerivAt_iff_tendsto_slope_zero.mp e2).mono_left (nhdsGT_le_nhdsNE 0)
    have s3 := s1.sub s2
    have ph : phi T f h = T h f := phi_of_nonneg hh
    have p0 : phi T f 0 = f := by rw [phi_of_nonneg le_rfl, hT.1]; rfl
    rw [ph, p0] at s3
    refine s3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : 0 ≤ δ := le_of_lt hδ
    rw [smul_real_eq, T_comp_Fint hT f hh hδ']
    have hF0 : Fint T f 0 = 0 := by simp [Fint]
    rw [hF0, zero_add, sub_zero, ← smul_sub]
    congr 1
    abel
  exact (hA _ _).mp hlim


theorem Fint_quot_tendsto (hT : IsC0Semigroup T) (f : X) :
    Tendsto (fun δ : ℝ => ((δ⁻¹ : ℝ) : 𝕜) • Fint T f δ) (𝓝[>] 0) (𝓝 f) := by
  have e2 := (Fint_hasDerivAt hT f 0)
  have s2 : Tendsto (fun δ : ℝ => δ⁻¹ • (Fint T f (0 + δ) - Fint T f 0)) (𝓝[>] 0)
      (𝓝 (phi T f 0)) :=
    (hasDerivAt_iff_tendsto_slope_zero.mp e2).mono_left (nhdsGT_le_nhdsNE 0)
  have p0 : phi T f 0 = f := by rw [phi_of_nonneg le_rfl, hT.1]; rfl
  rw [p0] at s2
  refine s2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hF0 : Fint T f 0 = 0 := by simp [Fint]
  rw [smul_real_eq, hF0, zero_add, sub_zero]

theorem dense_domain (hT : IsC0Semigroup T) {A : X →ₗ.[𝕜] X} (hA : IsGenerator T A) :
    Dense (A.domain : Set X) := by
  intro f
  refine mem_closure_of_tendsto (Fint_quot_tendsto hT f) ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  obtain ⟨hm, _⟩ := Fint_mem_domain hT hA f (le_of_lt hδ)
  exact A.domain.smul_mem _ hm

theorem slope_T (hT : IsC0Semigroup T) {A : X →ₗ.[𝕜] X} (hA : IsGenerator T A) {f : X}
    (hf : f ∈ A.domain) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun t => T t f) (T x (A ⟨f, hf⟩)) (Set.Ici x) x := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope'
    (by simp : x ∉ Set.Ioi x)]
  have hq := (hA f (A ⟨f, hf⟩)).mpr ⟨hf, rfl⟩
  have hlim : Tendsto (fun s : ℝ => s - x) (𝓝[>] x) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => s - x) (𝓝 x) (𝓝 (x - x)) :=
        (continuous_id.sub continuous_const).tendsto x
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have h2 := ((T x).continuous.tendsto _).comp (hq.comp hlim)
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hst : x < s := hs
  simp only [Function.comp, slope_def_module]
  have hs2 : T s f = T x (T (s - x) f) := by
    rw [← ContinuousLinearMap.mul_apply, hT.2.1 x (s - x) hx (by linarith)]
    congr 2; ring
  rw [← smul_real_eq (𝕜 := 𝕜) (s - x) (T s f - T x f), map_smul, map_sub, hs2]


theorem T_sub_eq_Fint (hT : IsC0Semigroup T) {A : X →ₗ.[𝕜] X} (hA : IsGenerator T A) {f : X}
    (hf : f ∈ A.domain) {h : ℝ} (hh : 0 ≤ h) :
    T h f - f = Fint T (A ⟨f, hf⟩) h := by
  set u : X := A ⟨f, hf⟩ with hu
  have hcont : ContinuousOn (fun t => T t f - f - Fint T u t) (Set.Icc 0 h) := by
    have h1 : ContinuousOn (fun t => T t f) (Set.Icc 0 h) :=
      (C0_continuousOn hT f).mono Set.Icc_subset_Ici_self
    have h2 : Continuous (Fint T u) := continuous_iff_continuousAt.mpr
      (fun t => (Fint_hasDerivAt hT u t).continuousAt)
    exact (h1.sub continuousOn_const).sub h2.continuousOn
  have hder : ∀ x ∈ Set.Ico 0 h, HasDerivWithinAt (fun t => T t f - f - Fint T u t) 0
      (Set.Ici x) x := by
    intro x hx
    have d1 := slope_T hT hA hf hx.1
    have d2 := (Fint_hasDerivAt hT u x).hasDerivWithinAt (s := Set.Ici x)
    have := (d1.sub_const f).sub d2
    refine this.congr_deriv ?_
    rw [phi_of_nonneg hx.1, sub_self]
  have := constant_of_has_deriv_right_zero hcont hder h ⟨hh, le_rfl⟩
  simp only [hT.1, ContinuousLinearMap.one_apply, sub_self, zero_sub] at this
  have hF0 : Fint T u 0 = 0 := by simp [Fint]
  rw [hF0] at this
  exact sub_eq_zero.mp (by simpa using this)

theorem Fint_sub (hT : IsC0Semigroup T) (u v : X) (h : ℝ) :
    Fint T u h - Fint T v h = Fint T (u - v) h := by
  unfold Fint
  rw [← intervalIntegral.integral_sub ((phi_continuous hT u).intervalIntegrable _ _)
    ((phi_continuous hT v).intervalIntegrable _ _)]
  congr 1
  ext s
  simp [phi]

theorem Fint_norm_le (hT : IsC0Semigroup T) (w : X) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ t, 0 ≤ t → t ≤ h → ‖T t‖ ≤ M) : ‖Fint T w h‖ ≤ M * ‖w‖ * h := by
  unfold Fint
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
    (f := phi T w) (C := M * ‖w‖) (fun s hs => by
      rw [Set.uIoc_of_le hh] at hs
      rw [phi_of_nonneg hs.1.le]
      exact ((T s).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hM s hs.1.le hs.2)
        (norm_nonneg _)))
  rwa [abs_of_nonneg (by linarith : 0 ≤ h - 0), sub_zero] at this

theorem generator_isClosed (hT : IsC0Semigroup T) {A : X →ₗ.[𝕜] X} (hA : IsGenerator T A) :
    A.IsClosed := by
  unfold LinearPMap.IsClosed
  refine isClosed_of_closure_subset (fun p hp => ?_)
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hp
  choose y hy1 hy2 using fun n => (LinearPMap.mem_graph_iff A).mp (hu n)
  have hf : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hlim
  have hg : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hlim
  have key : ∀ h : ℝ, 0 ≤ h → T h p.1 - p.1 = Fint T p.2 h := by
    intro h hh
    obtain ⟨M, hM1, hM⟩ := local_bound hT h
    have h1 : Tendsto (fun n => T h (u n).1 - (u n).1) atTop (𝓝 (T h p.1 - p.1)) :=
      (((T h).continuous.tendsto _).comp hf).sub hf
    have h2 : Tendsto (fun n => Fint T (u n).2 h) atTop (𝓝 (Fint T p.2 h)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h3 : Tendsto (fun n => M * ‖(u n).2 - p.2‖ * h) atTop (𝓝 0) := by
        have := ((tendsto_iff_norm_sub_tendsto_zero.mp hg).const_mul M).mul_const h
        simpa using this
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h3
      rw [Fint_sub hT]
      exact Fint_norm_le hT _ hh hM
    have h4 : ∀ n, T h (u n).1 - (u n).1 = Fint T (u n).2 h := by
      intro n
      have := T_sub_eq_Fint hT hA (y n).2 hh
      rw [← hy1 n, ← hy2 n]
      exact this
    exact tendsto_nhds_unique (h1.congr h4) h2
  have hlim2 : Tendsto (fun δ : ℝ => ((δ⁻¹ : ℝ) : 𝕜) • (T δ p.1 - p.1)) (𝓝[>] 0) (𝓝 p.2) := by
    refine (Fint_quot_tendsto hT p.2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [key δ (le_of_lt hδ)]
  obtain ⟨hm, hAg⟩ := (hA p.1 p.2).mp hlim2
  exact (LinearPMap.mem_graph_iff A).mpr ⟨⟨p.1, hm⟩, rfl, hAg⟩

end Integral

end Basic

theorem generator_isClosed_dense_core {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (T : ℝ → X →L[𝕜] X) (A : X →ₗ.[𝕜] X)
    (hT : IsC0Semigroup T) (hA : IsGenerator T A) :
    A.IsClosed ∧ Dense (A.domain : Set X) := by
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  haveI : IsScalarTower ℝ 𝕜 X := RestrictScalars.isScalarTower ℝ 𝕜 X
  exact ⟨generator_isClosed hT hA, dense_domain hT hA⟩

end HunterPDE.Semigroup

open HunterPDE.Semigroup in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (T : ℝ → X →L[𝕜] X) (A : X →ₗ.[𝕜] X)
    (hT : IsC0Semigroup T) (hA : IsGenerator T A) :
    A.IsClosed ∧ Dense (A.domain : Set X) :=
  generator_isClosed_dense_core T A hT hA
