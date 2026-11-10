-- Prove2me | solution 1 for InfoInundation.CompleteScreening.proposition_1_all_accuracy_cases
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T13:44:26.525201+00:00
-- url     : https://prove2.me/submissions/1d751420-326a-4311-bb96-dccff4338736

import Mathlib
import Definitions.Def_InfoInundation_CompleteScreening_EstimatedAccuracy

set_option autoImplicit false

namespace InfoInundation.CompleteScreening.P1Aux

open MeasureTheory ProbabilityTheory InfoInundation.Screening InfoInundation.CompleteScreening

/-- A score that is a strictly decreasing function of the squared distance picks the closest posts. -/
lemma argmax_eq_closest {K : ℕ} (f F : ℝ → ℝ) (μ : ℝ) (Z : Fin K → ℝ)
    (hF : StrictAntiOn F (Set.Ici 0)) (hf : ∀ z, f z = F ((z - μ) ^ 2)) :
    argmaxMenu f Z = closestPosts μ Z := by
  ext i
  simp only [argmaxMenu, closestPosts, Finset.mem_filter, Finset.mem_univ, true_and, hf]
  refine forall_congr' fun j => ?_
  exact hF.le_iff_ge (Set.mem_Ici.2 (sq_nonneg _)) (Set.mem_Ici.2 (sq_nonneg _))

lemma argmax_const {K : ℕ} (f : ℝ → ℝ) (Z : Fin K → ℝ) (c : ℝ) (hf : ∀ z, f z = c) :
    argmaxMenu f Z = Finset.univ := by
  ext i
  simp [argmaxMenu, hf]

/-- Equation (2): `A(μ,s,z) = s² + (z-μ)²`. -/
lemma estAcc (μ s z : ℝ) : estimatedAccuracySq μ s z = s ^ 2 + (z - μ) ^ 2 := by
  unfold estimatedAccuracySq
  have hv : (((s ^ 2).toNNReal : NNReal) : ℝ) = s ^ 2 := Real.coe_toNNReal _ (sq_nonneg s)
  have h2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal μ (s ^ 2).toNNReal) :=
    memLp_id_gaussianReal' 2 (by simp)
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal μ (s ^ 2).toNNReal) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 (by simp))
  have hsq : Integrable (fun x : ℝ => (x - μ) ^ 2) (gaussianReal μ (s ^ 2).toNNReal) :=
    (h2.sub (memLp_const μ)).integrable_sq
  have hvar : ∫ x, (x - μ) ^ 2 ∂(gaussianReal μ (s ^ 2).toNNReal) = s ^ 2 := by
    have := variance_fun_id_gaussianReal (μ := μ) (v := (s ^ 2).toNNReal)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at this
    rw [this, hv]
  have hmean : ∫ x, x ∂(gaussianReal μ (s ^ 2).toNNReal) = μ := integral_id_gaussianReal
  have hfun : (fun u : ℝ => (u - z) ^ 2) =
      fun u => (u - μ) ^ 2 + ((2 * (μ - z)) * u + ((μ - z) ^ 2 - 2 * (μ - z) * μ)) := by
    funext u; ring
  have i3 : Integrable (fun u : ℝ => (2 * (μ - z)) * u) (gaussianReal μ (s ^ 2).toNNReal) :=
    h1.const_mul _
  have i4 : Integrable (fun _ : ℝ => (μ - z) ^ 2 - 2 * (μ - z) * μ)
      (gaussianReal μ (s ^ 2).toNNReal) := integrable_const _
  have i5 : Integrable (fun u : ℝ => (2 * (μ - z)) * u + ((μ - z) ^ 2 - 2 * (μ - z) * μ))
      (gaussianReal μ (s ^ 2).toNNReal) := i3.add i4
  rw [hfun, integral_add hsq i5, integral_add i3 i4, integral_const_mul, hmean, hvar,
    integral_const]
  simp
  ring

/-- The squared updated sd as a function of the accuracy. -/
noncomputable def q (s σ : ℝ) : ℝ := s ^ 2 * σ ^ 2 / (s ^ 2 + σ ^ 2)

/-- The likelihood scale `√(2(σ²+s²))`. -/
noncomputable def y (s σ : ℝ) : ℝ := Real.sqrt (2 * (σ ^ 2 + s ^ 2))

lemma q_nonneg (s σ : ℝ) (hs : 0 < s) : 0 ≤ q s σ := by
  unfold q; positivity

lemma q_le (s σ : ℝ) (hs : 0 < s) : q s σ ≤ s ^ 2 := by
  unfold q
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg s, sq_nonneg σ, mul_nonneg (sq_nonneg s) (sq_nonneg s)]

lemma nextSd_eq (s σ : ℝ) : nextSd s σ = Real.sqrt (q s σ) := rfl

lemma nextSd_sq (s σ : ℝ) (hs : 0 < s) : nextSd s σ ^ 2 = q s σ := by
  rw [nextSd_eq, Real.sq_sqrt (q_nonneg s σ hs)]

lemma q_inj (s x z : ℝ) (hs : 0 < s) (hx : 0 < x) (hz : 0 < z) (h : q s x = q s z) : x = z := by
  unfold q at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have h4 : s ^ 4 * (x ^ 2 - z ^ 2) = 0 := by linear_combination h
  have hs4 : s ^ 4 ≠ 0 := by positivity
  have hxz : x ^ 2 = z ^ 2 := by
    have := (mul_eq_zero.1 h4).resolve_left hs4
    linarith
  exact (pow_left_inj₀ hx.le hz.le two_ne_zero).1 hxz

lemma y_sq (s σ : ℝ) : y s σ ^ 2 = 2 * (σ ^ 2 + s ^ 2) := by
  unfold y; rw [Real.sq_sqrt (by positivity)]

lemma s_le_y (s σ : ℝ) (hs : 0 < s) : s ≤ y s σ := by
  unfold y
  rw [Real.le_sqrt hs.le (by positivity)]
  nlinarith [sq_nonneg σ, sq_nonneg s]

lemma y_pos (s σ : ℝ) (hs : 0 < s) : 0 < y s σ := lt_of_lt_of_le hs (s_le_y s σ hs)

lemma psi_pos (r yy : ℝ) (hy : 0 < yy) : 0 < psi r yy := by
  unfold psi
  have := Real.sqrt_pos.2 Real.pi_pos
  positivity

lemma psi_le (r : ℝ) (hr : 0 ≤ r) (s σ : ℝ) (hs : 0 < s) :
    psi r (y s σ) ≤ 1 / (Real.sqrt Real.pi * s) := by
  unfold psi
  have hpi := Real.sqrt_pos.2 Real.pi_pos
  have hy := s_le_y s σ hs
  have hyp := y_pos s σ hs
  have he : Real.exp (-(r / y s σ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hr (sq_nonneg _)))
  calc 1 / (Real.sqrt Real.pi * y s σ) * Real.exp (-(r / y s σ ^ 2))
      ≤ 1 / (Real.sqrt Real.pi * y s σ) * 1 :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = 1 / (Real.sqrt Real.pi * y s σ) := mul_one _
    _ ≤ 1 / (Real.sqrt Real.pi * s) :=
        one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hy hpi.le)

lemma psi_split (r1 r2 yy : ℝ) :
    psi r2 yy = psi r1 yy * Real.exp (-((r2 - r1) / yy ^ 2)) := by
  unfold psi
  rw [show -(r2 / yy ^ 2) = -(r1 / yy ^ 2) + -((r2 - r1) / yy ^ 2) by ring, Real.exp_add]
  ring

lemma rho_eq (r1 r2 s σ : ℝ) (hs : 0 < s) :
    Real.exp (-((r2 - r1) / y s σ ^ 2)) =
      Real.exp (-((r2 - r1) / (2 * s ^ 4) * s ^ 2)) *
        Real.exp ((r2 - r1) / (2 * s ^ 4) * q s σ) := by
  rw [← Real.exp_add, y_sq]
  congr 1
  unfold q
  have h1 : σ ^ 2 + s ^ 2 ≠ 0 := by positivity
  have h2 : s ^ 2 + σ ^ 2 ≠ 0 := by positivity
  have h3 : s ≠ 0 := hs.ne'
  field_simp
  ring

lemma psi_meas (r s : ℝ) : Measurable (fun σ => psi r (y s σ)) := by
  unfold psi y; fun_prop

/-- G-a.e. uniqueness forces a Dirac law. -/
lemma eq_dirac_of_ae (G : Measure ℝ) [IsProbabilityMeasure G] (P : ℝ → Prop)
    (hP : ∀ᵐ σ ∂G, P σ) (hu : ∀ x z, P x → P z → x = z) : ∃ m, G = Measure.dirac m := by
  obtain ⟨m, hm⟩ := hP.exists
  refine ⟨m, ?_⟩
  have hae : ∀ᵐ σ ∂G, σ = m := hP.mono fun σ h => hu σ m h hm
  ext A hA
  rw [Measure.dirac_apply' m hA]
  by_cases hmA : m ∈ A
  · rw [Set.indicator_of_mem hmA]
    have : ∀ᵐ σ ∂G, σ ∈ A := hae.mono fun σ h => h ▸ hmA
    simpa using (prob_compl_eq_zero_iff hA).1 (mem_ae_iff.1 this)
  · rw [Set.indicator_of_notMem hmA]
    have : ∀ᵐ σ ∂G, σ ∉ A := hae.mono fun σ h => h ▸ hmA
    rw [ae_iff] at this
    simpa using this

/-- Tilting a positive weight by a factor comonotone with `g` raises the weighted mean of `g`. -/
lemma tilt (G : Measure ℝ) (a b g ρ : ℝ → ℝ) (c k : ℝ) (hb : ∀ σ, b σ = a σ * ρ σ)
    (ha : Integrable a G) (hga : Integrable (fun σ => g σ * a σ) G) (hbI : Integrable b G)
    (hgb : Integrable (fun σ => g σ * b σ) G) (hA : 0 < ∫ σ, a σ ∂G) (hB : 0 < ∫ σ, b σ ∂G)
    (ha0 : ∀ σ, 0 ≤ a σ) (hc : c = (∫ σ, g σ * a σ ∂G) / ∫ σ, a σ ∂G)
    (hpair : ∀ σ, 0 ≤ (g σ - c) * (ρ σ - k))
    (hstrict : ¬ (fun σ => (g σ - c) * (ρ σ - k) * a σ) =ᵐ[G] 0) :
    (∫ σ, g σ * a σ ∂G) / (∫ σ, a σ ∂G) < (∫ σ, g σ * b σ ∂G) / (∫ σ, b σ ∂G) := by
  have hF : (fun σ => (g σ - c) * (ρ σ - k) * a σ) =
      fun σ => g σ * b σ - c * b σ - k * (g σ * a σ) + k * c * a σ := by
    funext σ; rw [hb]; ring
  have hFi : Integrable (fun σ => (g σ - c) * (ρ σ - k) * a σ) G := by
    rw [hF]; exact ((hgb.sub (hbI.const_mul c)).sub (hga.const_mul k)).add (ha.const_mul (k * c))
  have hF0 : (0 : ℝ → ℝ) ≤ fun σ => (g σ - c) * (ρ σ - k) * a σ :=
    fun σ => mul_nonneg (hpair σ) (ha0 σ)
  have hpos : 0 < ∫ σ, (g σ - c) * (ρ σ - k) * a σ ∂G := by
    rcases (integral_nonneg hF0).lt_or_eq with h | h
    · exact h
    · exact absurd ((integral_eq_zero_iff_of_nonneg hF0 hFi).1 h.symm) hstrict
  have hca : c * ∫ σ, a σ ∂G = ∫ σ, g σ * a σ ∂G := by
    rw [hc]; exact div_mul_cancel₀ _ hA.ne'
  have hval : ∫ σ, (g σ - c) * (ρ σ - k) * a σ ∂G =
      (∫ σ, g σ * b σ ∂G) - c * ∫ σ, b σ ∂G := by
    have j1 : Integrable (fun σ => c * b σ) G := hbI.const_mul c
    have j2 : Integrable (fun σ => k * (g σ * a σ)) G := hga.const_mul k
    have j3 : Integrable (fun σ => k * c * a σ) G := ha.const_mul (k * c)
    have j4 : Integrable (fun σ => g σ * b σ - c * b σ) G := hgb.sub j1
    have j5 : Integrable (fun σ => g σ * b σ - c * b σ - k * (g σ * a σ)) G := j4.sub j2
    rw [hF, integral_add j5 j3, integral_sub j4 j2, integral_sub hgb j1,
      integral_const_mul, integral_const_mul,
      integral_const_mul, mul_assoc k c, hca]
    ring
  rw [← hc, lt_div_iff₀ hB]
  linarith

/-- Known accuracy: the posterior mean of an increasing function of the accuracy rises strictly
with the squared distance, unless `G` is a point mass. -/
lemma known_strictMono (G : Measure ℝ) (hG : AccuracyLaw G) (hnd : ∀ σ : ℝ, G ≠ Measure.dirac σ)
    (s : ℝ) (hs : 0 < s) (g : ℝ → ℝ) (hgm : Measurable g) (B : ℝ) (hgB : ∀ σ, |g σ| ≤ B)
    (hg0 : ∀ σ, 0 ≤ g σ)
    (hpairG : ∀ c : ℝ, 0 ≤ c → ∃ C : ℝ, ∀ κ : ℝ, 0 < κ → ∀ M : ℝ, 0 < M → ∃ k : ℝ, ∀ σ,
      0 ≤ (g σ - c) * (M * Real.exp (κ * q s σ) - k) ∧
      ((g σ - c) * (M * Real.exp (κ * q s σ) - k) = 0 → q s σ = C)) :
    StrictMonoOn (fun r => (∫ σ, g σ * psi r (y s σ) ∂G) / ∫ σ, psi r (y s σ) ∂G)
      (Set.Ici 0) := by
  have := hG.isProb
  obtain ⟨lo, hi, hlo, -, hsupp⟩ := hG.bdd
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hgB 0)
  have hpi := Real.sqrt_pos.2 Real.pi_pos
  have intL : ∀ r, 0 ≤ r → Integrable (fun σ => psi r (y s σ)) G := fun r hr =>
    Integrable.of_bound (psi_meas r s).aestronglyMeasurable (1 / (Real.sqrt Real.pi * s))
      (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs, abs_of_pos (psi_pos _ _ (y_pos s σ hs))]
        exact psi_le r hr s σ hs)
  have intgL : ∀ r, 0 ≤ r → Integrable (fun σ => g σ * psi r (y s σ)) G := fun r hr =>
    Integrable.of_bound (hgm.mul (psi_meas r s)).aestronglyMeasurable
      (B * (1 / (Real.sqrt Real.pi * s)))
      (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (psi_pos _ _ (y_pos s σ hs))]
        exact mul_le_mul (hgB σ) (psi_le r hr s σ hs) (psi_pos _ _ (y_pos s σ hs)).le hB0)
  have posL : ∀ r, 0 ≤ r → 0 < ∫ σ, psi r (y s σ) ∂G := fun r hr => by
    rw [integral_pos_iff_support_of_nonneg (fun σ => (psi_pos _ _ (y_pos s σ hs)).le) (intL r hr)]
    have : Function.support (fun σ => psi r (y s σ)) = Set.univ :=
      Set.eq_univ_of_forall fun σ => (psi_pos _ _ (y_pos s σ hs)).ne'
    rw [this, measure_univ]
    exact one_pos
  intro r1 hr1 r2 hr2 h12
  simp only [Set.mem_Ici] at hr1 hr2
  set c := (∫ σ, g σ * psi r1 (y s σ) ∂G) / ∫ σ, psi r1 (y s σ) ∂G with hc
  have hc0 : 0 ≤ c :=
    div_nonneg (integral_nonneg fun σ => mul_nonneg (hg0 σ) (psi_pos _ _ (y_pos s σ hs)).le)
      (posL r1 hr1).le
  obtain ⟨C, hC⟩ := hpairG c hc0
  set κ := (r2 - r1) / (2 * s ^ 4) with hκ
  have hκ0 : 0 < κ := div_pos (sub_pos.2 h12) (by positivity)
  set M := Real.exp (-((r2 - r1) / (2 * s ^ 4) * s ^ 2)) with hM
  obtain ⟨k, hk⟩ := hC κ hκ0 M (Real.exp_pos _)
  refine tilt G (fun σ => psi r1 (y s σ)) (fun σ => psi r2 (y s σ)) g
    (fun σ => M * Real.exp (κ * q s σ)) c k (fun σ => ?_) (intL r1 hr1) (intgL r1 hr1)
    (intL r2 hr2) (intgL r2 hr2) (posL r1 hr1) (posL r2 hr2)
    (fun σ => (psi_pos _ _ (y_pos s σ hs)).le) hc (fun σ => (hk σ).1) ?_
  · show psi r2 (y s σ) = psi r1 (y s σ) * (M * Real.exp (κ * q s σ))
    rw [psi_split r1 r2, rho_eq r1 r2 s σ hs]
  · intro hF
    have hsupp' : Set.Icc lo hi ∈ ae G := mem_ae_iff.2 hsupp
    have hP : ∀ᵐ σ ∂G, q s σ = C ∧ σ ∈ Set.Icc lo hi := by
      filter_upwards [hF, hsupp'] with σ h1 h2
      refine ⟨?_, h2⟩
      have h1' : (g σ - c) * (M * Real.exp (κ * q s σ) - k) * psi r1 (y s σ) = 0 := h1
      rcases mul_eq_zero.1 h1' with h | h
      · exact (hk σ).2 h
      · exact absurd h (psi_pos _ _ (y_pos s σ hs)).ne'
    obtain ⟨m, hm⟩ := eq_dirac_of_ae G _ hP fun x z hx hz =>
      q_inj s x z hs (lt_of_lt_of_le hlo hx.2.1) (lt_of_lt_of_le hlo hz.2.1) (hx.1.trans hz.1.symm)
    exact hnd m hm

lemma pair_sd (s : ℝ) (hs : 0 < s) (c : ℝ) (hc : 0 ≤ c) : ∃ C : ℝ, ∀ κ : ℝ, 0 < κ → ∀ M : ℝ,
    0 < M → ∃ k : ℝ, ∀ σ,
      0 ≤ (nextSd s σ - c) * (M * Real.exp (κ * q s σ) - k) ∧
      ((nextSd s σ - c) * (M * Real.exp (κ * q s σ) - k) = 0 → q s σ = C) := by
  refine ⟨c ^ 2, fun κ hκ M hM => ⟨M * Real.exp (κ * c ^ 2), fun σ => ?_⟩⟩
  have ht := q_nonneg s σ hs
  have hsq : Real.sqrt (q s σ) * Real.sqrt (q s σ) = q s σ := Real.mul_self_sqrt ht
  have hsn := Real.sqrt_nonneg (q s σ)
  rw [nextSd_eq]
  constructor
  · rcases le_total c (Real.sqrt (q s σ)) with h | h
    · have h2 : c ^ 2 ≤ q s σ := by nlinarith [mul_self_le_mul_self hc h]
      have h3 : M * Real.exp (κ * c ^ 2) ≤ M * Real.exp (κ * q s σ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 hκ.le)) hM.le
      exact mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h3)
    · have h2 : q s σ ≤ c ^ 2 := by nlinarith [mul_self_le_mul_self hsn h]
      have h3 : M * Real.exp (κ * q s σ) ≤ M * Real.exp (κ * c ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 hκ.le)) hM.le
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h) (sub_nonpos.2 h3)
  · intro h0
    rcases mul_eq_zero.1 h0 with h | h
    · have : Real.sqrt (q s σ) = c := by linarith
      rw [← this]; nlinarith [hsq]
    · have h1 : M * Real.exp (κ * q s σ) = M * Real.exp (κ * c ^ 2) := by linarith
      have h2 := Real.exp_eq_exp.1 (mul_left_cancel₀ hM.ne' h1)
      exact mul_left_cancel₀ hκ.ne' h2

lemma pair_var (s : ℝ) (hs : 0 < s) (c : ℝ) (_hc : 0 ≤ c) : ∃ C : ℝ, ∀ κ : ℝ, 0 < κ → ∀ M : ℝ,
    0 < M → ∃ k : ℝ, ∀ σ,
      0 ≤ ((fun σ => nextSd s σ ^ 2) σ - c) * (M * Real.exp (κ * q s σ) - k) ∧
      (((fun σ => nextSd s σ ^ 2) σ - c) * (M * Real.exp (κ * q s σ) - k) = 0 → q s σ = C) := by
  refine ⟨c, fun κ hκ M hM => ⟨M * Real.exp (κ * c), fun σ => ?_⟩⟩
  simp only [nextSd_sq s σ hs]
  constructor
  · rcases le_total c (q s σ) with h | h
    · have h3 : M * Real.exp (κ * c) ≤ M * Real.exp (κ * q s σ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hκ.le)) hM.le
      exact mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h3)
    · have h3 : M * Real.exp (κ * q s σ) ≤ M * Real.exp (κ * c) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hκ.le)) hM.le
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h) (sub_nonpos.2 h3)
  · intro h0
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · have h1 : M * Real.exp (κ * q s σ) = M * Real.exp (κ * c) := by linarith
      have h2 := Real.exp_eq_exp.1 (mul_left_cancel₀ hM.ne' h1)
      exact mul_left_cancel₀ hκ.ne' h2

lemma anti_of_mono (E : ℝ → ℝ) (t : ℝ) (hE : StrictMonoOn E (Set.Ici 0)) :
    StrictAntiOn (fun r => t - E r) (Set.Ici 0) := by
  intro a ha b hb hab
  have := hE ha hb hab
  simp only
  linarith

lemma Qu_mono (s : ℝ) (hs : 0 < s) :
    StrictMonoOn (fun r : ℝ => s ^ 2 * (s ^ 2 + r) / (s ^ 2 + (s ^ 2 + r))) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  simp only
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hs2 : 0 < s ^ 2 := by positivity
  nlinarith [mul_pos (mul_pos hs2 hs2) (sub_pos.2 hab)]

lemma unknownSd_eq (μ s z : ℝ) : unknownSdScore μ s z =
    s - Real.sqrt (s ^ 2 * (s ^ 2 + (z - μ) ^ 2) / (s ^ 2 + (s ^ 2 + (z - μ) ^ 2))) := by
  unfold unknownSdScore nextSd
  rw [estAcc, Real.sq_sqrt (by positivity)]

lemma unknownVar_eq (μ s z : ℝ) : unknownVarScore μ s z =
    s ^ 2 - s ^ 2 * (s ^ 2 + (z - μ) ^ 2) / (s ^ 2 + (s ^ 2 + (z - μ) ^ 2)) := by
  unfold unknownVarScore nextSd
  rw [estAcc, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

lemma sd_le (s σ : ℝ) (hs : 0 < s) : |nextSd s σ| ≤ s := by
  rw [nextSd_eq, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (q s σ) ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt (q_le s σ hs)
    _ = s := Real.sqrt_sq hs.le

lemma main (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s)
    {K : ℕ} (Z : Fin K → ℝ) :
    ((∀ σ : ℝ, G ≠ Measure.dirac σ) →
      argmaxMenu (sdScore G μ s) Z = closestPosts μ Z ∧
      argmaxMenu (varScore G μ s) Z = closestPosts μ Z ∧
      argmaxMenu (unknownSdScore μ s) Z = closestPosts μ Z ∧
      argmaxMenu (unknownVarScore μ s) Z = closestPosts μ Z) ∧
    (∀ σ : ℝ, 0 < σ → G = Measure.dirac σ →
      argmaxMenu (sdScore G μ s) Z = Finset.univ ∧
      argmaxMenu (varScore G μ s) Z = Finset.univ) := by
  refine ⟨fun hnd => ⟨?_, ?_, ?_, ?_⟩, fun σ0 _ hGσ => ⟨?_, ?_⟩⟩
  · refine argmax_eq_closest _ _ μ Z (anti_of_mono _ s (known_strictMono G hG hnd s hs (nextSd s)
      (by unfold nextSd; fun_prop) s (sd_le s · hs) (fun σ => Real.sqrt_nonneg _)
      (pair_sd s hs))) (fun z => rfl)
  · refine argmax_eq_closest _ _ μ Z (anti_of_mono _ (s ^ 2) (known_strictMono G hG hnd s hs
      (fun σ => nextSd s σ ^ 2) (by unfold nextSd; fun_prop) (s ^ 2) (fun σ => ?_)
      (fun σ => sq_nonneg _) (pair_var s hs))) (fun z => rfl)
    rw [abs_of_nonneg (sq_nonneg _), nextSd_sq s σ hs]
    exact q_le s σ hs
  · refine argmax_eq_closest _ (fun r => s - Real.sqrt (s ^ 2 * (s ^ 2 + r) / (s ^ 2 + (s ^ 2 + r))))
      μ Z ?_ (unknownSd_eq μ s)
    intro a ha b hb hab
    have h1 := Qu_mono s hs ha hb hab
    have h0 : 0 ≤ s ^ 2 * (s ^ 2 + a) / (s ^ 2 + (s ^ 2 + a)) := by
      simp only [Set.mem_Ici] at ha; positivity
    have := Real.sqrt_lt_sqrt h0 h1
    simp only
    linarith
  · refine argmax_eq_closest _ (fun r => s ^ 2 - s ^ 2 * (s ^ 2 + r) / (s ^ 2 + (s ^ 2 + r)))
      μ Z (anti_of_mono _ _ (Qu_mono s hs)) (unknownVar_eq μ s)
  · subst hGσ
    refine argmax_const _ Z (s - nextSd s σ0) fun z => ?_
    have hL : likelihood μ s σ0 z ≠ 0 := (psi_pos _ _ (y_pos s σ0 hs)).ne'
    simp only [sdScore, postExp, integral_dirac]
    rw [mul_div_assoc, div_self hL, mul_one]
  · subst hGσ
    refine argmax_const _ Z (s ^ 2 - nextSd s σ0 ^ 2) fun z => ?_
    have hL : likelihood μ s σ0 z ≠ 0 := (psi_pos _ _ (y_pos s σ0 hs)).ne'
    simp only [varScore, postExp, integral_dirac]
    rw [mul_div_assoc, div_self hL, mul_one]

end InfoInundation.CompleteScreening.P1Aux

open MeasureTheory InfoInundation.Screening InfoInundation.CompleteScreening in
theorem solution
    (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s)
    {K : ℕ} (Z : Fin K → ℝ) :
    ((∀ σ : ℝ, G ≠ Measure.dirac σ) →
      argmaxMenu (sdScore G μ s) Z = closestPosts μ Z ∧
      argmaxMenu (varScore G μ s) Z = closestPosts μ Z ∧
      argmaxMenu (unknownSdScore μ s) Z = closestPosts μ Z ∧
      argmaxMenu (unknownVarScore μ s) Z = closestPosts μ Z) ∧
    (∀ σ : ℝ, 0 < σ → G = Measure.dirac σ →
      argmaxMenu (sdScore G μ s) Z = Finset.univ ∧
      argmaxMenu (varScore G μ s) Z = Finset.univ) := by
  exact InfoInundation.CompleteScreening.P1Aux.main G hG μ s hs Z
