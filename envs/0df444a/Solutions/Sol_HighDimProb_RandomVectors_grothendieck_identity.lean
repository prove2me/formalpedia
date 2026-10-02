-- Prove2me | solution 1 for HighDimProb.RandomVectors.grothendieck_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:47:54.563588+00:00
-- url     : https://prove2.me/submissions/e74e3ffc-57a1-4482-a4e6-f88d343911b1

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector

open MeasureTheory ProbabilityTheory Real Set

set_option autoImplicit false

namespace GrothAux

lemma measurable_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

lemma abs_sign_le (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [Real.sign_of_neg h]
  · simp [h]
  · simp [Real.sign_of_pos h]

/-- the angular integrand -/
noncomputable def hθ (α θ : ℝ) : ℝ := Real.sign (cos θ) * Real.sign (cos (θ - α))

lemma measurable_hθ (α : ℝ) : Measurable (hθ α) := by
  unfold hθ
  exact (measurable_sign.comp continuous_cos.measurable).mul
    (measurable_sign.comp (continuous_cos.comp (continuous_id.sub continuous_const)).measurable)

lemma hθ_periodic (α : ℝ) : Function.Periodic (hθ α) π := by
  intro θ
  have h1 : cos (θ + π - α) = - cos (θ - α) := by
    rw [show θ + π - α = (θ - α) + π by ring, cos_add_pi]
  simp only [hθ, cos_add_pi, h1, Real.sign_neg]
  ring

lemma intervalIntegrable_hθ (α a b : ℝ) : IntervalIntegrable (hθ α) volume a b := by
  refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun (measurable_hθ α).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun θ => ?_)
  simp only [norm_one, Real.norm_eq_abs, hθ, abs_mul]
  calc |Real.sign (cos θ)| * |Real.sign (cos (θ - α))| ≤ 1 * 1 :=
        mul_le_mul (abs_sign_le _) (abs_sign_le _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma half_integral (α : ℝ) (h0 : 0 ≤ α) (hπ : α ≤ π) :
    ∫ θ in (-(π/2))..(π/2), hθ α θ = π - 2 * α := by
  set c := α - π / 2 with hc
  have hc1 : -(π/2) ≤ c := by linarith
  have hc2 : c ≤ π/2 := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
    (intervalIntegrable_hθ α _ _) (intervalIntegrable_hθ α _ _)]
  have hA : ∫ θ in (-(π/2))..c, hθ α θ = ∫ θ in (-(π/2))..c, (-1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton c).ae_notMem volume] with θ hθc hmem
    rw [Set.uIoc_of_le hc1] at hmem
    have hθ' : θ < c := lt_of_le_of_ne hmem.2 (by simpa using hθc)
    have hcos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨hmem.1, by linarith⟩
    have hcos2 : cos (θ - α) < 0 := by
      have : cos (θ - α) = - cos (θ - α + π) := by rw [cos_add_pi]; ring
      rw [this, neg_lt_zero]
      exact cos_pos_of_mem_Ioo ⟨by linarith [hmem.1], by linarith⟩
    simp [hθ, Real.sign_of_pos hcos, Real.sign_of_neg hcos2]
  have hB : ∫ θ in c..(π/2), hθ α θ = ∫ θ in c..(π/2), (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton (π/2)).ae_notMem volume] with θ hθc hmem
    rw [Set.uIoc_of_le hc2] at hmem
    have hθ' : θ < π/2 := lt_of_le_of_ne hmem.2 (by simpa using hθc)
    have hcos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [hmem.1], hθ'⟩
    have hcos2 : 0 < cos (θ - α) := cos_pos_of_mem_Ioo ⟨by linarith [hmem.1], by linarith⟩
    simp [hθ, Real.sign_of_pos hcos, Real.sign_of_pos hcos2]
  rw [hA, hB]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_neg, mul_one]
  rw [hc]; ring

lemma full_integral (α : ℝ) (h0 : 0 ≤ α) (hπ : α ≤ π) :
    ∫ θ in Ioo (-π) π, hθ α θ = 2 * π - 4 * α := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (intervalIntegrable_hθ α _ _) (intervalIntegrable_hθ α _ _)]
  have P := hθ_periodic α
  have e1 := P.intervalIntegral_add_eq (-π) (-(π/2))
  have e2 := P.intervalIntegral_add_eq 0 (-(π/2))
  rw [show -π + π = (0:ℝ) by ring, show -(π/2) + π = π/2 by ring] at e1
  rw [show (0:ℝ) + π = π by ring, show -(π/2) + π = π/2 by ring] at e2
  rw [e1, e2, half_integral α h0 hπ]
  ring

lemma radial : ∫ r in Ioi (0:ℝ), r * rexp (-(r ^ 2) / 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1/2 : ℂ)) (by norm_num)
  have h2 : (∫ r : ℝ in Ioi 0, ((r * rexp (-(r ^ 2) / 2) : ℝ) : ℂ)) = (1 : ℂ) := by
    have e : (2 * (1/2 : ℂ))⁻¹ = 1 := by norm_num
    rw [e] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    push_cast
    congr 2
    ring
  rw [integral_complex_ofReal] at h2
  exact_mod_cast h2

end GrothAux

namespace GrothAux

lemma sign_mul_of_pos {r x : ℝ} (hr : 0 < r) : Real.sign (r * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hr h)]
  · simp [h]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hr h)]

lemma core (α : ℝ) (h0 : 0 ≤ α) (hπ : α ≤ π) :
    ∫ p, Real.sign p.1 * Real.sign (cos α * p.1 + sin α * p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 - 2 * α / π := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero 0 hv]
  rw [MeasureTheory.prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
  have hm : Measurable (fun z : ℝ × ℝ => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) :=
    ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun z => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top))]
  rw [← Measure.volume_eq_prod]
  rw [← integral_comp_polarCoord_symm]
  have htarget : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  have hmeas : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioo (-π) π) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  rw [htarget]
  have key : ∀ p ∈ Ioi (0:ℝ) ×ˢ Ioo (-π) π,
      p.1 • (((gaussianPDF 0 1 (polarCoord.symm p).1 * gaussianPDF 0 1 (polarCoord.symm p).2).toReal) •
        (Real.sign (polarCoord.symm p).1 *
          Real.sign (cos α * (polarCoord.symm p).1 + sin α * (polarCoord.symm p).2)))
      = (p.1 * rexp (-(p.1 ^ 2) / 2)) * ((2 * π)⁻¹ * hθ α p.2) := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [mem_Ioi] at hr
    simp only [polarCoord_symm_apply, smul_eq_mul]
    rw [ENNReal.toReal_mul, gaussianPDF, gaussianPDF,
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [sign_mul_of_pos hr]
    have e1 : cos α * (r * cos θ) + sin α * (r * sin θ) = r * cos (θ - α) := by
      rw [cos_sub]; ring
    rw [e1, sign_mul_of_pos hr]
    have e2 : rexp (-(r * cos θ) ^ 2 / 2) * rexp (-(r * sin θ) ^ 2 / 2) = rexp (-(r ^ 2) / 2) := by
      rw [← Real.exp_add]; congr 1
      linear_combination (-(r ^ 2) / 2) * sin_sq_add_cos_sq θ
    have e3 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    have : (√(2 * π))⁻¹ * rexp (-(r * cos θ) ^ 2 / 2) * ((√(2 * π))⁻¹ * rexp (-(r * sin θ) ^ 2 / 2))
        = (2 * π)⁻¹ * rexp (-(r ^ 2) / 2) := by
      rw [← e2, ← e3]; ring
    rw [this]
    simp only [hθ]
    ring
  rw [setIntegral_congr_fun hmeas key]
  rw [Measure.volume_eq_prod]
  have hsp := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => r * rexp (-(r ^ 2) / 2)) (fun θ : ℝ => (2 * π)⁻¹ * hθ α θ) (Ioi 0) (Ioo (-π) π)
  try simp only at hsp
  rw [hsp]
  rw [radial, integral_const_mul, full_integral α h0 hπ]
  field_simp
  ring

end GrothAux

namespace GrothAux

open HighDimProb.RandomVectors

lemma memLp_g {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (i : Fin n) : MemLp (g i) 2 P := by
  have h : MemLp id 2 (P.map (g i)) := by rw [hg.2.2 i]; exact memLp_id_gaussianReal 2
  exact h.comp_of_map (hg.1 i).aemeasurable

lemma cov_lin {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (a b : Fin n → ℝ) :
    cov[fun ω => ∑ i, g i ω * a i, fun ω => ∑ i, g i ω * b i; P] = ∑ i, a i * b i := by
  rw [covariance_fun_sum_fun_sum (fun i => (memLp_g hg i).mul_const (a i))
    (fun j => (memLp_g hg j).mul_const (b j))]
  have hcov : ∀ i j, cov[fun ω => g i ω * a i, fun ω => g j ω * b j; P]
      = if i = j then a i * b i else 0 := by
    intro i j
    rw [covariance_mul_const_left, covariance_mul_const_right]
    split_ifs with h
    · subst h
      rw [covariance_self (hg.1 i).aemeasurable]
      have : Var[g i; P] = 1 := by
        rw [← variance_id_map (hg.1 i).aemeasurable, hg.2.2 i, variance_id_gaussianReal]; simp
      rw [this]; ring
    · rw [(hg.2.1.indepFun h).covariance_eq_zero (memLp_g hg i) (memLp_g hg j)]; ring
  simp_rw [hcov]
  simp

lemma mean_lin {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (a : Fin n → ℝ) :
    ∫ ω, ∑ i, g i ω * a i ∂P = 0 := by
  rw [integral_finsetSum _ (fun i _ => ((memLp_g hg i).integrable one_le_two).mul_const (a i))]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [integral_mul_const]
  have : ∫ ω, g i ω ∂P = 0 := by
    have h := integral_map (μ := P) (hg.1 i).aemeasurable (f := id)
      measurable_id.aestronglyMeasurable
    rw [hg.2.2 i] at h
    simp only [id] at h
    rw [← h, integral_id_gaussianReal]
  rw [this, zero_mul]

end GrothAux

open MeasureTheory ProbabilityTheory HighDimProb.RandomVectors in
theorem solution :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {n : ℕ} (g : Fin n → Ω → ℝ), IsStandardGaussianVector P g →
      ∀ u v : Fin n → ℝ, (∑ i, (u i) ^ 2 = 1) → (∑ i, (v i) ^ 2 = 1) →
        ∫ ω, Real.sign (∑ i, g i ω * u i) * Real.sign (∑ i, g i ω * v i) ∂P =
          (2 / Real.pi) * Real.arcsin (∑ i, u i * v i) := by
  intro Ω _ P _ n g hg u v hu hv
  set ρ := ∑ i, u i * v i with hρdef
  have hρle : ρ ≤ 1 := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (u i - v i))
    have e : ∑ i, (u i - v i) ^ 2 = ∑ i, u i ^ 2 + ∑ i, v i ^ 2 - 2 * ρ := by
      rw [hρdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hu, hv] at h; linarith
  have hρge : -1 ≤ ρ := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (u i + v i))
    have e : ∑ i, (u i + v i) ^ 2 = ∑ i, u i ^ 2 + ∑ i, v i ^ 2 + 2 * ρ := by
      rw [hρdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hu, hv] at h; linarith
  set w : Fin n → ℝ := fun i => v i - ρ * u i with hw
  set X : Ω → ℝ := fun ω => ∑ i, g i ω * u i with hX
  set Z : Ω → ℝ := fun ω => ∑ i, g i ω * w i with hZ
  have hY : ∀ ω, ∑ i, g i ω * v i = ρ * X ω + Z ω := by
    intro ω
    simp only [hX, hZ, hw, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hG : HasGaussianLaw (fun ω => (g · ω)) P :=
    iIndepFun.hasGaussianLaw (fun i => ⟨by rw [hg.2.2 i]; infer_instance⟩) hg.2.1
  let L : (Fin n → ℝ) →L[ℝ] ℝ × ℝ :=
    (∑ i, u i • ContinuousLinearMap.proj i).prod (∑ i, w i • ContinuousLinearMap.proj i)
  have hXZ : HasGaussianLaw (fun ω => (X ω, Z ω)) P := by
    have h := hG.map_fun L
    have hfun : (fun ω => (X ω, Z ω)) = (fun ω => L (fun i => g i ω)) := by
      funext ω
      ext <;> simp [L, hX, hZ] <;> exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hfun]; exact h
  have huw : ∑ i, u i * w i = 0 := by
    have e : ∑ i, u i * w i = ρ - ρ * ∑ i, u i ^ 2 := by
      rw [hρdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [hw]; ring)
    rw [e, hu]; ring
  have hww : ∑ i, w i * w i = 1 - ρ ^ 2 := by
    have e : ∑ i, w i * w i = ∑ i, (v i ^ 2 - 2 * ρ * (u i * v i) + ρ ^ 2 * u i ^ 2) :=
      Finset.sum_congr rfl (fun i _ => by simp only [hw]; ring)
    rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← hρdef, hu, hv]
    ring
  have huu : ∑ i, u i * u i = 1 := by
    rw [← hu]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hXm : AEMeasurable X P := hXZ.fst.aemeasurable
  have hZm : AEMeasurable Z P := hXZ.snd.aemeasurable
  have hind : IndepFun X Z P := by
    refine hXZ.indepFun_of_covariance_eq_zero ?_
    rw [hX, hZ, GrothAux.cov_lin hg u w, huw]
  have hXlaw : P.map X = gaussianReal 0 1 := by
    rw [hXZ.fst.map_eq_gaussianReal, ← covariance_self hXm, hX, GrothAux.cov_lin hg u u, huu,
      GrothAux.mean_lin hg u]
    simp
  set s : ℝ := Real.sin (Real.arccos ρ) with hs
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := by
    rw [hs, Real.sin_arccos, Real.sq_sqrt (by nlinarith)]
  have hZlaw : P.map Z = (gaussianReal 0 1).map (s * ·) := by
    rw [hXZ.snd.map_eq_gaussianReal, ← covariance_self hZm, hZ, GrothAux.cov_lin hg w w, hww,
      GrothAux.mean_lin hg w, gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      simp only [Real.coe_toNNReal', NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one, hs2]
      exact max_eq_left (by nlinarith)
  have hF : Measurable (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) :=
    (GrothAux.measurable_sign.comp measurable_fst).mul
      (GrothAux.measurable_sign.comp ((measurable_fst.const_mul ρ).add measurable_snd))
  have hcos : Real.cos (Real.arccos ρ) = ρ := Real.cos_arccos hρge hρle
  calc ∫ ω, Real.sign (∑ i, g i ω * u i) * Real.sign (∑ i, g i ω * v i) ∂P
      = ∫ ω, (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) (X ω, Z ω) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        simp only [hY ω]
        rfl
    _ = ∫ p, (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) p
          ∂(P.map (fun ω => (X ω, Z ω))) :=
        (integral_map (hXm.prodMk hZm) hF.aestronglyMeasurable).symm
    _ = ∫ p, (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) p
          ∂((gaussianReal 0 1).prod ((gaussianReal 0 1).map (s * ·))) := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map hXm hZm).1 hind, hXlaw, hZlaw]
    _ = ∫ p, (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) p
          ∂(((gaussianReal 0 1).prod (gaussianReal 0 1)).map (Prod.map id (s * ·))) := by
        rw [← Measure.map_prod_map _ _ measurable_id (measurable_const_mul s), Measure.map_id]
    _ = ∫ p, Real.sign p.1 * Real.sign (Real.cos (Real.arccos ρ) * p.1
          + Real.sin (Real.arccos ρ) * p.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
        rw [integral_map (measurable_id.prodMap (measurable_const_mul s)).aemeasurable
          hF.aestronglyMeasurable, hcos]
        rfl
    _ = 1 - 2 * Real.arccos ρ / Real.pi :=
        GrothAux.core _ (Real.arccos_nonneg ρ) (Real.arccos_le_pi ρ)
    _ = (2 / Real.pi) * Real.arcsin ρ := by
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]
        field_simp
        ring
