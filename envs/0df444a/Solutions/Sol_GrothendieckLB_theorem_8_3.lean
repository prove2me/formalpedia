-- Prove2me | solution 1 for GrothendieckLB.theorem_8_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:35:39.745664+00:00
-- url     : https://prove2.me/submissions/c87b3b4f-26b8-4d74-89a6-7ad6b5a06276
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckLB_IsTernaryFn
import Definitions.Def_GrothendieckLB_V
import Definitions.Def_GrothendieckLB_beta
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_Pfun
import Definitions.Def_GrothendieckLB_gaussExp
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8
import Theorems.Thm_GrothendieckLB_fiber_dual_medium
import Theorems.Thm_GrothendieckLB_fiber_dual_tail

section

-- Gaussian projection, contraction, and integrability lemmas adapted from LG’s symmetric-scheme proof.
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace KG

/-- Standard Gaussian density on `Fin k → ℝ`. -/
noncomputable def phiK (k : ℕ) (x : Fin k → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma phiK_nonneg (k : ℕ) (x : Fin k → ℝ) : 0 ≤ phiK k x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

lemma measurable_phiK (k : ℕ) : Measurable (phiK k) := by
  unfold phiK
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

lemma pi_gauss (k : ℕ) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity (fun x => ENNReal.ofReal (phiK k x)) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : Fin k → ℝ, (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (phiK k x)) x
      = ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      unfold phiK
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  have hint : Integrable (fun x : Fin k → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun i =>
      (integrable_gaussianPDFReal 0 1).indicator (hs i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
      Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  rw [volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_indicator (hs i), gaussianReal_apply 0 one_ne_zero (s i)]
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
    (Filter.Eventually.of_forall fun y => gaussianPDFReal_nonneg 0 1 y)]
  rfl

/-- Integrals against the Gaussian density equal integrals against the product measure. -/
lemma integral_phiK (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    ∫ x, phiK k x * F x = ∫ x, F x ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  rw [pi_gauss, integral_withDensity_eq_integral_toReal_smul (measurable_phiK k).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (phiK_nonneg k x)]

end KG

namespace KG

open scoped RealInnerProductSpace

/-- One-dimensional absolute moments of the standard Gaussian. -/
lemma gauss_abs_moment (q : ℝ) (hq : -1 < q) :
    ∫ t, |t| ^ q ∂(gaussianReal 0 1) =
      2 * ((1 / Real.sqrt (2 * π)) * ((1 / 2 : ℝ) ^ (-(q + 1) / 2) * (1 / 2) * Gamma ((q + 1) / 2))) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h1 : ∀ t : ℝ, gaussianPDFReal 0 1 t • |t| ^ q =
      (fun u : ℝ => (1 / Real.sqrt (2 * π)) * (u ^ q * Real.exp (-(1 / 2) * u ^ (2 : ℝ)))) |t| := by
    intro t
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [Real.rpow_two, sq_abs]
    ring_nf
  simp_rw [h1]
  rw [integral_comp_abs (f := fun u : ℝ => (1 / Real.sqrt (2 * π)) * (u ^ q * Real.exp (-(1 / 2) * u ^ (2 : ℝ))))]
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hq (by norm_num)]

lemma gauss_abs_one : ∫ t, |t| ∂(gaussianReal 0 1) = Real.sqrt (2 / π) := by
  have h := gauss_abs_moment 1 (by norm_num)
  simp only [Real.rpow_one] at h
  rw [h]
  norm_num [Real.Gamma_one]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hp : Real.sqrt π ≠ 0 := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith [hs]

end KG

end

section

open GrothendieckLB KG MeasureTheory ProbabilityTheory Filter Finset Real
open PrivateAgnosticHalfspace.Gaussian
open scoped RealInnerProductSpace

namespace FiberChaos

noncomputable abbrev G (d : ℕ) := Measure.pi fun _ : Fin d => gaussianReal 0 1

lemma gauss_eq {d : ℕ} (F : (Fin d → ℝ) → ℝ) :
    gaussExp F = ∫ z, F z ∂(G d) := by
  change (∫ z, F z * phiK d z) = _
  simp_rw [mul_comm (F _) (phiK _ _)]
  exact integral_phiK d F

noncomputable def coordH {d : ℕ} (κ : Fin d → ℕ) (z : Fin d → ℝ) :=
  hermite d κ (WithLp.toLp 2 z)
noncomputable def coef {d : ℕ} (u : (Fin d → ℝ) → ℝ) (κ : Fin d → ℕ) :=
  gaussExp (fun z => u z * coordH κ z)

lemma coordH_meas {d : ℕ} (κ : Fin d → ℕ) : Measurable (coordH κ) := by
  unfold coordH hermite AMPLowDeg.RankOne.hermNorm
  fun_prop

lemma coordH_int {d : ℕ} (κ : Fin d → ℕ) : Integrable (coordH κ) (G d) := by
  letI : IsProbabilityMeasure (gaussian d) := (inferInstance : IsProbabilityMeasure (stdGaussian (Vec d)))
  have hp : MeasurePreserving (WithLp.toLp 2) (G d) (gaussian d) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact hp.integrable_comp_of_integrable (((lemma_B_8 d).2.1 κ).integrable (by norm_num))

lemma exp_to_vec {d : ℕ} (F : Vec d → ℝ) (hm : Measurable F) :
    gaussExp (fun z => F (WithLp.toLp 2 z)) = ∫ z, F z ∂(gaussian d) := by
  have hl : HasLaw (WithLp.toLp 2) (gaussian d) (G d) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact (gauss_eq _).trans (hl.integral_comp hm.aestronglyMeasurable)

theorem coeffs_bessel {d : ℕ} (u : (Fin d → ℝ) → ℝ) (C : ℝ)
    (hu : Measurable u) (ub : ∀ z, |u z| ≤ C) (s : Finset (Fin d → ℕ)) :
    ∑ κ ∈ s, coef u κ ^ 2 ≤ gaussExp (fun z => u z ^ 2) := by
  classical
  let U : Vec d → ℝ := fun z => u (WithLp.ofLp z)
  have hU : Measurable U := hu.comp (by fun_prop)
  let μ := gaussian d
  letI : IsProbabilityMeasure μ := (inferInstance : IsProbabilityMeasure (stdGaussian (Vec d)))
  have hU2 : MemLp U 2 μ := MemLp.of_bound hU.aestronglyMeasurable C
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using ub (WithLp.ofLp z))
  let X := hU2.toLp U
  have hX : (fun z => X z) =ᵐ[μ] U := hU2.coeFn_toLp
  obtain ⟨b, hb⟩ := (lemma_B_8 d).2.2.1
  let A := fun κ => ⟪b κ, X⟫
  have hherm (κ : Fin d → ℕ) : Measurable (hermite d κ) := by
    unfold hermite AMPLowDeg.RankOne.hermNorm
    fun_prop
  have hA (κ : Fin d → ℕ) : A κ =
      gaussExp (fun z => u z * hermite d κ (WithLp.toLp 2 z)) := by
    rw [exp_to_vec (fun z => U z * hermite d κ z) (hU.mul (hherm κ))]
    change ⟪b κ, X⟫ = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hb κ, hX] with z hz hzx
    rw [hz, hzx]
    rfl
  have hNorm : ‖X‖ ^ 2 = gaussExp (fun z => u z ^ 2) := by
    rw [exp_to_vec (fun z => U z ^ 2) (hU.pow_const _),
      ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hX] with z hz
    rw [hz]
    simp [sq, U]
  have hB := b.orthonormal.sum_inner_products_le X (s := s)
  change (∑ κ ∈ s, ‖A κ‖ ^ 2) ≤ _ at hB
  simpa only [Real.norm_eq_abs, sq_abs, hA, hNorm, coef, coordH] using hB


end FiberChaos

end

section

open MeasureTheory ProbabilityTheory GrothendieckLB KG FiberChaos Filter Finset Real
open PrivateAgnosticHalfspace.Gaussian

namespace FiberChaos

lemma stdExp_eq (F : ℝ → ℝ) : stdExp F = ∫ s, F s ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  unfold stdExp
  simp only [smul_eq_mul]
  exact integral_congr_ae (Eventually.of_forall fun s => mul_comm _ _)

lemma he_eq_normalized (j : Fin 4) (s : ℝ) : he j s = AMPLowDeg.RankOne.hermNorm j.val s := by
  fin_cases j <;> norm_num [he, AMPLowDeg.RankOne.hermNorm, Polynomial.hermite,
    Polynomial.derivative_mul, Nat.factorial] <;> ring

lemma he_meas (j : Fin 4) : Measurable (he j) := by
  simp_rw [funext (he_eq_normalized j)]
  unfold AMPLowDeg.RankOne.hermNorm; fun_prop

lemma he_int (j : Fin 4) : Integrable (he j) (gaussianReal 0 1) := by
  let μ := gaussianReal 0 1
  have T := (measurePreserving_funUnique μ (Fin 1)).symm.integrable_comp_of_integrable
    (coordH_int (d := 1) (fun _ => j.val))
  apply T.congr
  exact Eventually.of_forall fun s => by
    simpa [Function.comp_def, coordH, hermite, Fintype.prod_unique] using (he_eq_normalized j s).symm

end FiberChaos

end

section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

namespace GaussianBand

noncomputable def band (r s : ℝ) : ℝ := if |s| ≤ r then 1 else 0

lemma measurable_band (r : ℝ) : Measurable (band r) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_const measurable_const

lemma band_bound (r s : ℝ) : 0 ≤ band r s ∧ band r s ≤ 1 := by
  unfold band; split_ifs <;> norm_num

lemma central_mass (r : ℝ) (hr : 0 ≤ r) :
    ∫ s, band r s ∂(gaussianReal 0 1) = 2 * cdf (gaussianReal 0 1) r - 1 := by
  let μ := gaussianReal 0 1
  have hsym : μ.map (fun s : ℝ => -s) = μ := by simp [μ, gaussianReal_map_neg]
  have ht : μ.real (Iio (-r)) = μ.real (Ioi r) := by
    calc μ.real (Iio (-r)) = (μ.map (fun s : ℝ => -s)).real (Iio (-r)) := by rw [hsym]
      _ = _ := by
        rw [measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iio, measureReal_def]
        congr 2
        ext s
        simp
  have hd : Disjoint (Iio (-r)) (Icc (-r) r) :=
    Set.disjoint_left.mpr fun _ h1 h2 => (not_lt_of_ge h2.1) h1
  have hu := measureReal_union (μ := μ) hd measurableSet_Icc
  rw [Iio_union_Icc_eq_Iic (by linarith : -r ≤ r), ht] at hu
  have hc := measureReal_add_measureReal_compl (μ := μ) (measurableSet_Iic (a := r))
  rw [compl_Iic] at hc
  change _ = 2 * cdf μ r - 1
  rw [cdf_eq_real]
  have eqb : band r = (Icc (-r) r).indicator (1 : ℝ → ℝ) := by
    funext s
    simp only [band, Set.indicator, Set.mem_Icc, abs_le, Pi.one_apply]
  rw [eqb, integral_indicator_one measurableSet_Icc]
  change μ.real (Icc (-r) r) = _
  have hone : μ.real Set.univ = 1 := by simp [μ]
  linarith

lemma weighted_mass (r : ℝ) (hr : 0 ≤ r) :
    ∫ s : ℝ, |s| * band r s ∂(gaussianReal 0 1) =
      ABPOnline.cG * (1 - Real.exp (-(r ^ 2 / 2))) := by
  let w := fun t : ℝ => t * Real.exp (-(t ^ 2 / 2))
  have hw : Continuous w := by dsimp [w]; fun_prop
  have dw (t : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-(t ^ 2 / 2))) (w t) t := by
    convert! (((hasDerivAt_pow 2 t).div_const 2).neg.exp.neg) using 1 <;> dsimp [w] <;> ring
  have hfront : (∫ t in Set.Ioi (0 : ℝ), (Set.Iic r).indicator w t) =
      1 - Real.exp (-(r ^ 2 / 2)) := by
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.inter_comm, Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le hr,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => dw t) (hw.intervalIntegrable _ _)]
    simp; ring
  have hfun (s : ℝ) : gaussianPDFReal 0 1 s • (|s| * band r s) =
      (Real.sqrt (2 * Real.pi))⁻¹ * (Set.Iic r).indicator w |s| := by
    by_cases hs : |s| ≤ r
    · rw [Set.indicator_of_mem (show |s| ∈ Set.Iic r from hs)]
      simp only [band, if_pos hs, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
        w, sq_abs]
      ring
    · rw [Set.indicator_of_notMem (show |s| ∉ Set.Iic r from hs)]
      simp [band, hs]
  have hconst : (Real.sqrt (2 * π))⁻¹ * 2 = ABPOnline.cG := by
    unfold ABPOnline.cG
    have hpos : 0 < Real.sqrt (2 * π) := by positivity
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * π)
    have hs' := Real.sq_sqrt (by positivity : 0 ≤ 2 / π)
    rw [← div_eq_inv_mul, div_eq_iff hpos.ne']
    nlinarith [Real.sqrt_nonneg (2 / π), mul_nonneg (Real.sqrt_nonneg (2 / π)) hpos.le,
      show (Real.sqrt (2 / π) * Real.sqrt (2 * π)) ^ 2 = 4 by
        rw [mul_pow, hs, hs']; field_simp <;> ring]
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [hfun, integral_const_mul]
  rw [integral_comp_abs, hfront, ← mul_assoc, hconst]

end GaussianBand

end

section

open GrothendieckLB MeasureTheory ProbabilityTheory Real Set Filter
namespace GaussianBand

lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {w : Ω → ℝ} (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1) : Integrable w μ :=
  memLp_one_iff_integrable.mp (MemLp.of_bound hw.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb z))

theorem bathtub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S w : Ω → ℝ} (hS : Measurable S) (hlaw : HasLaw S (gaussianReal 0 1) μ)
    (hw : Measurable w) (hb : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (budget : ∫ z, |S z| * w z ∂μ ≤ ABPOnline.cG * (1 - x)) :
    ∫ z, w z ∂μ ≤ Pfun x := by
  have hwb (z) : ‖w z‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hb z).1]; exact (hb z).2
  have hwi : Integrable w μ := bounded_integrable hw hwb
  have hSi : Integrable (fun z => |S z|) μ :=
    (hlaw.measurePreserving hS).integrable_comp_of_integrable
      (show Integrable (fun s : ℝ => |s|) (gaussianReal 0 1) from IsGaussian.integrable_id.abs)
  have hWS := hSi.mul_bdd hw.aestronglyMeasurable (Eventually.of_forall hwb)
  let r := Real.sqrt (-2 * Real.log x)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = -2 * Real.log x :=
    Real.sq_sqrt (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (Real.log_nonpos hx.le hx1))
  have he : Real.exp (-(r ^ 2 / 2)) = x := by
    rw [hr2, show -(-2 * Real.log x / 2) = Real.log x by ring, Real.exp_log hx]
  let b := fun z => band r (S z)
  have hbm : Measurable b := (measurable_band r).comp hS
  have hbb (z) : ‖b z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (band_bound _ _).1]; exact (band_bound _ _).2
  have hbi : Integrable b μ := bounded_integrable hbm hbb
  have hBS := hSi.mul_bdd hbm.aestronglyMeasurable (Eventually.of_forall hbb)
  have hB : (∫ z, b z ∂μ) = Pfun x := by
    unfold Pfun
    rw [if_neg hx.ne']
    exact (hlaw.integral_comp (measurable_band r).aestronglyMeasurable).trans (central_mass r hr)
  have hBS' : (∫ z, |S z| * b z ∂μ) = ABPOnline.cG * (1 - x) := by
    rw [← he]
    exact (hlaw.integral_comp (measurable_abs.mul (measurable_band r)).aestronglyMeasurable).trans
      (weighted_mass r hr)
  by_cases hpos : 0 < r
  · have point (z) : r * w z - r * b z ≤ |S z| * w z - |S z| * b z := by
      have h : 0 ≤ (|S z| - r) * (w z - b z) := by
        by_cases hz : |S z| ≤ r
        · apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hz)
          simpa [b, band, hz] using (sub_nonpos.mpr (hb z).2)
        · apply mul_nonneg (sub_nonneg.mpr (le_of_not_ge hz))
          simpa [b, band, hz] using (hb z).1
      linarith
    have hi := integral_mono ((hwi.const_mul r).sub (hbi.const_mul r)) (hWS.sub hBS) point
    simp only [Pi.sub_apply] at hi
    rw [integral_sub (hwi.const_mul r) (hbi.const_mul r), integral_sub hWS hBS,
      integral_const_mul, integral_const_mul, hB, hBS'] at hi
    exact (mul_le_mul_iff_right₀ hpos).mp (by linarith only [hi, budget])
  · have hr0 := le_antisymm (le_of_not_gt hpos) hr
    have hx' : x = 1 := by rw [← he, hr0]; norm_num
    rw [hx'] at budget
    have hIntZero : (∫ z, |S z| * w z ∂μ) = 0 := le_antisymm
      (by linarith only [budget]) (integral_nonneg fun z => mul_nonneg (abs_nonneg _) (hb z).1)
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun z => mul_nonneg (abs_nonneg (S z)) (hb z).1) hWS).mp hIntZero
    letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    have hne : ∀ᵐ z ∂μ, S z ≠ 0 := (hlaw.ae_iff (p := fun s => s ≠ 0)
      (measurableSet_setOfPred.mp (measurableSet_singleton (0 : ℝ)).compl)).mpr
        ((gaussianReal 0 1).ae_ne 0)
    have hw0 : w =ᵐ[μ] 0 := by
      filter_upwards [hae, hne] with z hz hNz
      exact (mul_eq_zero.mp hz).resolve_left (abs_ne_zero.mpr hNz)
    rw [integral_congr_ae hw0, ← hB]
    simp only [Pi.zero_apply, integral_zero]
    exact integral_nonneg fun z => (band_bound _ _).1

end GaussianBand

end

section

open GrothendieckLB FiberChaos MeasureTheory ProbabilityTheory Filter Finset Real
namespace OneFiber

noncomputable abbrev γ := gaussianReal 0 1
noncomputable abbrev ν := ABPOnline.cG

lemma ternary_le {u : ℝ → ℝ} (hu : IsTernaryFn u) (s : ℝ) :
    |u s| ≤ 1 ∧ u s ^ 2 ≤ 1 ∧ |u s| = u s ^ 2 := by
  rcases hu.2 s with h | h | h <;> norm_num [h]

lemma budget_eq (u : ℝ → ℝ) : GrothendieckLB.beta u = ∫ s, |s| * u s ^ 2 ∂γ := stdExp_eq _
lemma weight_int {u : ℝ → ℝ} (hu : IsTernaryFn u) :
    Integrable (fun s => |s| * u s ^ 2) γ :=
  (show Integrable (fun s : ℝ => |s|) γ from IsGaussian.integrable_id.abs).mul_bdd
    (hu.1.pow_const _).aestronglyMeasurable (Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u s))] using (ternary_le hu s).2.1)

lemma budget_bounds {u : ℝ → ℝ} (hu : IsTernaryFn u) : 0 ≤ GrothendieckLB.beta u ∧ GrothendieckLB.beta u ≤ ν := by
  rw [budget_eq]
  refine ⟨integral_nonneg (fun s => mul_nonneg (abs_nonneg _) (sq_nonneg _)), ?_⟩
  refine (integral_mono (weight_int hu) (show Integrable (fun s : ℝ => |s|) γ from
    IsGaussian.integrable_id.abs) (fun s => ?_)).trans_eq KG.gauss_abs_one
  simpa using mul_le_mul_of_nonneg_left (ternary_le hu s).2.1 (abs_nonneg s)

lemma bessel1 {u : ℝ → ℝ} (hu : IsTernaryFn u) : V u ≤ ∫ s, u s ^ 2 ∂γ := by
  classical
  let index := fun (j : Fin 4) (_ : Fin 1) => j.val
  let U := fun z : Fin 1 → ℝ => u (z 0)
  let S := univ.image index
  have h := coeffs_bessel U 1 (hu.1.comp (measurable_pi_apply 0)) (fun z => (ternary_le hu _).1) S
  have hp := measurePreserving_funUnique γ (Fin 1)
  have law : HasLaw (fun z : Fin 1 → ℝ => z 0) γ (G 1) := ⟨(measurable_pi_apply 0).aemeasurable, hp.map_eq⟩
  have hidx : Function.Injective index := fun _ _ h => Fin.ext (congrFun h 0)
  have co (j : Fin 4) : coef U (index j) = stdExp (fun s => u s * he j s) := by
    rw [coef, gauss_eq, stdExp_eq]
    refine Eq.trans ?_ (law.integral_comp (f := fun s => u s * he j s)
      (hu.1.mul (he_meas j)).aestronglyMeasurable)
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [index, U, coordH, PrivateAgnosticHalfspace.Gaussian.hermite, Function.comp_def,
      Fintype.prod_unique, he_eq_normalized]
  rw [show S = univ.image index by rfl, sum_image (fun _ _ _ _ he => hidx he), gauss_eq] at h
  simp only [co] at h
  exact h.trans_eq (law.integral_comp (hu.1.pow_const 2).aestronglyMeasurable)

end OneFiber

end

section

open MeasureTheory ProbabilityTheory Filter Set Finset Real
open scoped Topology

namespace HighBudget

abbrev r₀ : ℝ := 1.081596
abbrev c₀ : ℝ := 0.993405
noncomputable abbrev ν := ABPOnline.cG
noncomputable def E (t : ℝ) := Real.exp (-(t^2/2))
noncomputable def gap (r : ℝ) := ν * (2 - E r - E r ^ 2) - ∫ s in (0:ℝ)..r, E s

lemma ν_pos : 0 < ν := Real.sqrt_pos.mpr (by positivity)
lemma ν_low : (0.7978 : ℝ) ≤ ν := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith only [Real.pi_lt_d6]
lemma dE (t : ℝ) : HasDerivAt E (-(t * E t)) t := by
  convert! (((hasDerivAt_pow 2 t).div_const 2).neg.exp) using 1 <;> dsimp [E] <;> ring

private noncomputable def A (i : ℕ) : ℝ := (-1 : ℝ)^i / (2^i * i.factorial)
private noncomputable def T (t : ℝ) := ∑ i ∈ range 10, A i * t^(2*i)

private lemma taylor_bound (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ r₀) :
    |E t - T t| ≤ 0.0000004 := by
  have hh : |-(t ^ 2 / 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have hu : t ^ 2 ≤ r₀ ^ 2 := pow_le_pow_left₀ ht ht' 2
    norm_num [r₀] at hu
    linarith
  have h := Real.exp_bound (x := -(t ^ 2 / 2)) hh (n := 10) (by norm_num)
  have heq : (∑ m ∈ range 10, (-(t^2/2))^m / (m.factorial : ℝ)) = T t := by
    refine sum_congr rfl fun i _ => ?_
    rw [show -(t^2/2) = (-1) * (t^2/2) by ring, mul_pow, div_pow, ← pow_mul]
    unfold A
    ring
  rw [heq] at h
  refine h.trans ?_
  have hw : |-(t ^ 2 / 2)| ^ 10 ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg _) hh 10
  norm_num [Nat.factorial] at *
  linarith

lemma e0_bounds : (0.557147 : ℝ) ≤ E r₀ ∧ E r₀ ≤ 0.557149 := by
  have h := abs_le.mp (taylor_bound r₀ (by norm_num) le_rfl)
  norm_num [T, A, r₀, Finset.sum_range_succ, Nat.factorial] at h ⊢
  constructor <;> linarith

private lemma integral_taylor (r : ℝ) :
    (∫ t in (0:ℝ)..r, T t) = ∑ i ∈ range 10, A i * (r ^ (2*i+1) / (2*i+1)) := by
  unfold T
  rw [intervalIntegral.integral_finsetSum (f := fun i (t : ℝ) => A i * t ^ (2*i)) (fun i _ => (continuous_const.mul (continuous_id.pow _)).intervalIntegrable 0 r)]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  simp

private lemma gap0 : 0 ≤ gap r₀ := by
  have hbound : (∫ t in (0:ℝ)..r₀, E t) ≤ ∫ t in (0:ℝ)..r₀, T t + 0.0000004 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((show Continuous E by unfold E; fun_prop).intervalIntegrable _ _)
      ((show Continuous (fun t => T t + 0.0000004) by unfold T; fun_prop).intervalIntegrable _ _)
    intro t ht
    linarith only [(abs_le.mp (taylor_bound t ht.1 ht.2)).2]
  rw [intervalIntegral.integral_add ((show Continuous T by unfold T; fun_prop).intervalIntegrable _ _)
    (intervalIntegrable_const), intervalIntegral.integral_const, integral_taylor] at hbound
  have hin : (∫ t in (0:ℝ)..r₀, E t) ≤ 0.903100 := by
    norm_num [A, r₀, Finset.sum_range_succ, Nat.factorial] at hbound
    linarith only [hbound]
  have hE : E r₀ ^ 2 ≤ (0.557149:ℝ)^2 := pow_le_pow_left₀ (Real.exp_pos _).le e0_bounds.2 2
  have ht : (2 - (0.557149:ℝ) - (0.557149:ℝ)^2) ≤ 2 - E r₀ - E r₀ ^ 2 := by
    linarith only [hE, e0_bounds.2]
  have hm := mul_le_mul ν_low ht (by norm_num) ν_pos.le
  unfold gap
  exact sub_nonneg.mpr (hin.trans ((by norm_num : (0.903100:ℝ) ≤
    0.7978 * (2 - (0.557149:ℝ) - (0.557149:ℝ)^2)).trans hm))

lemma gap_nonneg (r : ℝ) (hr : r₀ ≤ r) : 0 ≤ gap r := by
  have cm : Continuous E := by unfold E; fun_prop
  have deriv (t : ℝ) : HasDerivAt gap
      (E t * (ν * t * (1 + 2 * E t) - 1)) t := by
    have hI : HasDerivAt (fun b => ∫ s in (0:ℝ)..b, E s) (E t) t :=
      intervalIntegral.integral_hasDerivAt_right (cm.intervalIntegrable _ _) cm.aestronglyMeasurable.stronglyMeasurableAtFilter cm.continuousAt
    convert! (((((hasDerivAt_const t (2:ℝ)).sub (dE t)).sub ((dE t).pow 2)).const_mul ν).sub hI) using 1 <;>
      dsimp [gap] <;> ring
  have hmon : MonotoneOn gap (Ici r₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (fun t _ => (deriv t).continuousAt.continuousWithinAt)
      (fun t _ => (deriv t).differentiableAt.differentiableWithinAt)
    intro t ht
    have h1 : 1 ≤ t := le_trans (by norm_num : (1 : ℝ) ≤ r₀) (interior_subset ht)
    rw [(deriv t).deriv]
    apply mul_nonneg (Real.exp_pos _).le
    have epos : 0 ≤ E t := (Real.exp_pos _).le
    by_cases hbig : (4/3 : ℝ) ≤ t
    · have hprod := mul_le_mul ν_low hbig (by norm_num) ν_pos.le
      have he := mul_nonneg (mul_nonneg ν_pos.le (by linarith only [h1] : 0 ≤ t)) epos
      nlinarith only [hprod, he]
    · have ht2 : t ^ 2 ≤ (4/3:ℝ)^2 := pow_le_pow_left₀ (by linarith only [h1]) (le_of_not_ge hbig) 2
      have he : (1/3:ℝ) ≤ E t := by
        calc (1/3:ℝ) ≤ (Real.exp 1)⁻¹ := by
              rw [← one_div, div_le_div_iff₀ (by norm_num) (Real.exp_pos _)]; linarith only [Real.exp_one_lt_d9]
          _ = Real.exp (-1) := (Real.exp_neg 1).symm
          _ ≤ E t := Real.exp_le_exp.mpr (by linarith only [ht2])
      have hprod := mul_le_mul ν_low h1 (by norm_num) ν_pos.le
      have hh := mul_le_mul hprod (show 1 + 2*(1/3:ℝ) ≤ 1+2*E t by linarith only [he])
        (by norm_num) (mul_nonneg ν_pos.le (by linarith only [h1] : 0 ≤ t))
      linarith only [hh]
  exact gap0.trans (hmon (mem_Ici.mpr le_rfl) (mem_Ici.mpr hr) hr)

lemma splice : 1 - 3/2 * (1 - c₀ / Real.sqrt (1+c₀^2)) ≤ E r₀ := by
  have hs : (1.4095578:ℝ) ≤ Real.sqrt (1+c₀^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    norm_num [c₀]
  have he : c₀ / Real.sqrt (1+c₀^2) ≤ c₀ / 1.4095578 := by
    gcongr
  linarith only [he, e0_bounds.1]

end HighBudget

end

section

open MeasureTheory ProbabilityTheory GrothendieckLB FiberChaos Filter Set Real GaussianBand
open scoped Topology
namespace HighBudget

lemma central_integral (r : ℝ) (hr : 0 ≤ r) :
    (∫ s, band r s ∂(gaussianReal 0 1)) = ν * ∫ t in (0:ℝ)..r, E t := by
  have hfun (s : ℝ) : gaussianPDFReal 0 1 s • band r s =
      (Real.sqrt (2 * Real.pi))⁻¹ * (Set.Iic r).indicator E |s| := by
    by_cases hs : |s| ≤ r
    · rw [Set.indicator_of_mem (show |s| ∈ Set.Iic r from hs)]
      simp [band, hs, E, gaussianPDFReal, sq_abs]
      exact Or.inl (by ring)
    · rw [Set.indicator_of_notMem (show |s| ∉ Set.Iic r from hs)]
      simp [band, hs]
  have hconst : (Real.sqrt (2 * π))⁻¹ * 2 = ν := by
    change _ = Real.sqrt (2 / π)
    rw [← div_eq_inv_mul, div_eq_iff (by positivity)]
    rw [← Real.sqrt_mul (by positivity), div_mul_eq_mul_div]
    have he : 2 * (2 * π) / π = 4 := by field_simp; ring
    rw [he]; norm_num
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [hfun, integral_const_mul]
  rw [integral_comp_abs, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Set.inter_comm, Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le hr, ← mul_assoc, hconst]

theorem high_case {u : ℝ → ℝ} (hu : IsTernaryFn u)
    (hhi : 3*ν/2 * (1 - c₀ / Real.sqrt (1+c₀^2)) ≤ GrothendieckLB.beta u) :
    V u ≤ 3*ν * GrothendieckLB.beta u - GrothendieckLB.beta u ^ 2 := by
  let b := GrothendieckLB.beta u
  have hb := OneFiber.budget_bounds hu
  change 0 ≤ b ∧ b ≤ ν at hb
  have bes := OneFiber.bessel1 hu
  change _ ≤ 3*ν*b-b^2
  by_cases h : b = ν
  · rw [h]
    apply bes.trans
    have hi : Integrable (fun s => u s ^ 2) (gaussianReal 0 1) :=
      bounded_integrable (hu.1.pow_const _) fun s => by
        rw [abs_of_nonneg (sq_nonneg _)]; exact (OneFiber.ternary_le hu s).2.1
    have h1 : (∫ s, u s ^ 2 ∂(gaussianReal 0 1)) ≤ 1 := by
      simpa using integral_mono (g := fun _ => (1:ℝ)) hi (integrable_const _) fun s => (OneFiber.ternary_le hu s).2.1
    exact h1.trans (by nlinarith only [ν_low, sq_nonneg (ν-(0.7978:ℝ))])
  · let x := 1-b/ν
    have hx : 0 < x := sub_pos.mpr ((div_lt_one ν_pos).mpr (lt_of_le_of_ne hb.2 h))
    have hx1 : x ≤ 1 := sub_le_self _ (div_nonneg hb.1 ν_pos.le)
    have hbx : b = ν*(1-x) := by dsimp [x]; rw [sub_sub_cancel]; field_simp [ν_pos.ne']
    have H := GaussianBand.bathtub (S := id) measurable_id (HasLaw.id (μ := gaussianReal 0 1))
      (hu.1.pow_const 2) (fun s => ⟨sq_nonneg _, (OneFiber.ternary_le hu s).2.1⟩) x hx hx1
      ((OneFiber.budget_eq u).symm.trans hbx).le
    let r := Real.sqrt (-2*Real.log x)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = -2 * Real.log x :=
      Real.sq_sqrt (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (Real.log_nonpos hx.le hx1))
    have he : E r = x := by
      unfold E
      rw [hr2, show -(-2 * Real.log x / 2) = Real.log x by ring, Real.exp_log hx]
    have hx0 : x ≤ E r₀ := by
      apply le_trans _ splice
      change _ ≤ b at hhi
      rw [hbx] at hhi
      apply (mul_le_mul_iff_right₀ ν_pos).mp
      linarith only [hhi]
    have hr0 : r₀ ≤ r := by
      rw [← he] at hx0
      have hlog := Real.exp_le_exp.mp hx0
      have hh : -(r ^ 2 / 2) ≤ -(r₀ ^ 2 / 2) := hlog
      exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hr
        ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)).mp (neg_le_neg_iff.mp hh))
    have hP : Pfun x = ν * ∫ t in (0:ℝ)..r, E t := by
      rw [Pfun, if_neg hx.ne', ← central_mass r hr, central_integral]
      exact hr
    apply bes.trans (H.trans _)
    rw [hP, hbx, ← he]
    have hgap := gap_nonneg r hr0
    have hle : (∫ t in (0:ℝ)..r, E t) ≤ ν*(2 - E r - E r ^ 2) := sub_nonneg.mp hgap
    calc ν * (∫ t in (0:ℝ)..r, E t) ≤ ν * (ν * (2 - E r - E r ^ 2)) :=
          mul_le_mul_of_nonneg_left hle ν_pos.le
      _ = _ := by ring

end HighBudget

end

section

open MeasureTheory ProbabilityTheory GrothendieckLB FiberChaos OneFiber Filter Finset Real
namespace FiberDual

noncomputable def poly (a : Fin 4 → ℝ) (s : ℝ) : ℝ := ∑ j, a j * he j s
noncomputable def mom (u : ℝ → ℝ) (j : Fin 4) := stdExp (fun s => u s * he j s)
noncomputable def J (a : Fin 4 → ℝ) (c : ℝ) :=
  stdExp (fun s => max (|poly a s| - c*|s|) 0)
noncomputable def R := 3 * ABPOnline.cG / 2

lemma poly_int (a : Fin 4 → ℝ) : Integrable (poly a) γ :=
  integrable_finsetSum _ fun j _ => (he_int j).const_mul (a j)

lemma priced_bound {u : ℝ → ℝ} (hu : IsTernaryFn u) (a : Fin 4 → ℝ) (c : ℝ) :
    ∑ j, a j * mom u j ≤ J a c + c * GrothendieckLB.beta u := by
  let p := poly a
  have huH (j) : Integrable (fun s => u s * he j s) γ :=
    (he_int j).bdd_mul hu.1.aestronglyMeasurable (Eventually.of_forall fun s => (ternary_le hu s).1)
  have heq : (∑ j, a j * mom u j) = ∫ s, u s * p s ∂γ := by
    simp only [mom, stdExp_eq, ← integral_const_mul]
    rw [← integral_finsetSum _ (fun j _ => (huH j).const_mul (a j))]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    change (∑ j, a j * (u s * he j s)) = u s * ∑ j, a j * he j s
    rw [Finset.mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have hq : Integrable (fun s => max (|p s| - c*|s|) 0) γ :=
    ((poly_int a).abs.sub ((show Integrable (fun s : ℝ => |s|) γ from IsGaussian.integrable_id.abs).const_mul c)).sup (integrable_const 0)
  have hp := (poly_int a).bdd_mul hu.1.aestronglyMeasurable (Eventually.of_forall fun s => (ternary_le hu s).1)
  have hw := (weight_int hu).const_mul c
  rw [heq, J, stdExp_eq, budget_eq, ← integral_const_mul, ← integral_add hq hw]
  apply integral_mono hp (hq.add hw)
  intro s
  change u s * p s ≤ max (|p s| - c*|s|) 0 + c * (|s| * u s ^ 2)
  rcases hu.2 s with hs | hs | hs
  all_goals rw [hs]
  all_goals first
    | simpa only [zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using (le_max_right (|p s| - c*|s|) 0)
    | norm_num only [neg_one_mul, neg_one_sq, one_pow, mul_one, one_mul]; linarith only [le_abs_self (p s), neg_le_abs (p s), le_max_left (|p s|-c*|s|) 0]

lemma zero_budget {u : ℝ → ℝ} (hu : IsTernaryFn u) (hb : GrothendieckLB.beta u = 0) : V u = 0 := by
  letI : NullSingletonClass γ := nullSingletonClass_gaussianReal one_ne_zero
  rw [budget_eq] at hb
  have h0 := (integral_eq_zero_iff_of_nonneg (fun s => mul_nonneg (abs_nonneg _) (sq_nonneg (u s))) (weight_int hu)).mp hb
  have hz : u =ᵐ[γ] 0 := by
    filter_upwards [h0, γ.ae_ne 0] with s hs hne
    have hs' := (mul_eq_zero.mp hs).resolve_left (abs_ne_zero.mpr hne)
    exact pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp hs'
  have hco (j : Fin 4) : stdExp (fun s => u s * he j s) = 0 := by
    rw [stdExp_eq]
    have h : (fun s => u s * he j s) =ᵐ[γ] (fun _ => 0) := by
      filter_upwards [hz] with s h
      change u s = 0 at h
      simp [h]
    rw [integral_congr_ae h, integral_zero]
  simp [V, hco]

lemma low_case {u : ℝ → ℝ} (hu : IsTernaryFn u) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (gate : ∀ a : Fin 4 → ℝ, ∑ j, a j ^ 2 = 1 → ∀ c, c₀ ≤ c →
      J a c ≤ R * (Real.sqrt (1+c^2) - c))
    (low : GrothendieckLB.beta u ≤ R * (1-c₀/Real.sqrt (1+c₀^2))) :
    V u ≤ 3*ν*GrothendieckLB.beta u - GrothendieckLB.beta u ^ 2 := by
  let b := GrothendieckLB.beta u
  have hb := budget_bounds hu
  change 0 ≤ b ∧ b ≤ ν at hb
  change b ≤ _ at low
  have hn : 0 < ν := Real.sqrt_pos.mpr (by positivity)
  have hR : 0 < R := by dsimp [R]; linarith only [hn]
  by_cases hb0 : b = 0
  · rw [zero_budget hu hb0]; change (0:ℝ) ≤ 3*ν*b-b^2; rw [hb0]; norm_num
  have hb' : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
  have ht : 0 < R-b := by dsimp [R]; linarith only [hb.2, hn]
  let q := Real.sqrt (b*(2*R-b))
  have hprod : 0 < b*(2*R-b) := mul_pos hb' (by linarith only [ht,hR])
  have hq : 0 < q := Real.sqrt_pos.mpr hprod
  have hq2 : q^2 = b*(2*R-b) := Real.sq_sqrt hprod.le
  let c := (R-b)/q
  have hc : 0 < c := div_pos ht hq
  have hc0 : c₀ ≤ c := by
    let D := Real.sqrt (1+c₀^2)
    have hD : 0 < D := Real.sqrt_pos.mpr (by positivity)
    have hD2 : D^2 = 1+c₀^2 := Real.sq_sqrt (by positivity)
    have l : R*c₀ ≤ (R-b)*D := by
      change b ≤ R*(1-c₀/D) at low
      have hh := mul_le_mul_of_nonneg_right low hD.le
      field_simp at hh
      nlinarith only [hh]
    have ls := pow_le_pow_left₀ (mul_nonneg hR.le hc₀.le) l 2
    rw [mul_pow, mul_pow, hD2] at ls
    apply (le_div_iff₀ hq).mpr
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) ht.le
    rw [mul_pow, hq2]
    nlinarith only [ls]
  have hconj : R*(Real.sqrt (1+c^2)-c)+c*b = q := by
    have he : Real.sqrt (1+c^2) = R/q := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg hR.le hq.le)).mpr
      dsimp [c]
      field_simp
      nlinarith only [hq2]
    rw [he]
    dsimp [c]
    field_simp
    nlinarith only [hq2]
  let m := Real.sqrt (V u)
  have hV0 : 0 ≤ V u := sum_nonneg fun _ _ => sq_nonneg _
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hm2 : m^2 = ∑ j, mom u j ^ 2 := Real.sq_sqrt hV0
  have hmV : m^2 = V u := Real.sq_sqrt hV0
  have hmq : m ≤ q := by
    by_cases hm0 : m = 0
    · simpa only [hm0] using hq.le
    let a := fun j => mom u j/m
    have ha : ∑ j, a j ^ 2 = 1 := by
      simp only [a, div_pow, ← sum_div, ← hm2]
      exact div_self (pow_ne_zero _ hm0)
    have hma : ∑ j, a j * mom u j = m := by
      simp only [a, div_mul_eq_mul_div, ← sq, ← sum_div, ← hm2]
      field_simp
    have hbase := priced_bound hu a c
    rw [hma] at hbase
    calc m ≤ J a c + c*b := hbase
      _ ≤ R * (Real.sqrt (1+c^2)-c) + c*b := by linarith only [gate a ha c hc0]
      _ = q := hconj
  have hs := pow_le_pow_left₀ hm hmq 2
  rw [hmV, hq2] at hs
  change V u ≤ 3*ν*b - b^2
  dsimp [R] at hs
  linarith only [hs]

end FiberDual

end

section

open MeasureTheory ProbabilityTheory GrothendieckLB FiberDual Real
theorem solution {u : ℝ → ℝ} (hu : IsTernaryFn u) :
    V u ≤ 3 * ABPOnline.cG * GrothendieckLB.beta u - GrothendieckLB.beta u ^ 2 := by
  by_cases high : R * (1 - HighBudget.c₀ / Real.sqrt (1 + HighBudget.c₀ ^ 2)) ≤ GrothendieckLB.beta u
  · exact HighBudget.high_case hu high
  · apply low_case hu HighBudget.c₀ (by norm_num) _ (le_of_not_ge high)
    intro a ha c hc
    by_cases hm : c ≤ 12
    · exact fiber_dual_medium a ha c (by convert hc using 1 <;> norm_num [HighBudget.c₀]) hm
    · exact fiber_dual_tail a ha c (le_of_not_ge hm)

end
