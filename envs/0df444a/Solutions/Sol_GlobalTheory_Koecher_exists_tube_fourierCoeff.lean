-- Prove2me | solution 1 for GlobalTheory.Koecher.exists_tube_fourierCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:30:39.799987+00:00
-- url     : https://prove2.me/submissions/4d2b103f-81fb-40c3-80f7-f3e79eba14ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Theorems.Thm_GlobalTheory_Koecher_norm_le_tsum_of_cube_fourierCoeff_le
import Theorems.Thm_GlobalTheory_Koecher_setIntegral_unitCube_tube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.Koecher
namespace GlobalTheory.Koecher
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℂ) → ℂ} {U : Set (ι → ℂ)} (hU : IsOpen U) (hU' : IsPreconnected U)
    (htube : ∀ z ∈ U, ∀ t : ι → ℝ, (fun i => (t i : ℂ)) + z ∈ U) (hf : DifferentiableOn ℂ f U)
    (hper : ∀ z ∈ U, ∀ i, f (z + Pi.single i 1) = f z) :
    ∃ a : (ι → ℤ) → ℝ, (∀ m, 0 ≤ a m) ∧
      (∀ z ∈ U, ∀ M : ℝ, (∀ t : ι → ℝ, ‖f ((fun i => (t i : ℂ)) + z)‖ ≤ M) →
        ∀ m, a m * Real.exp (-(2 * π * ∑ i, (m i : ℝ) * (z i).im)) ≤ M) ∧
      (∀ z ∈ U, ∀ b : (ι → ℤ) → ℝ, Summable b →
        (∀ m, a m * Real.exp (-(2 * π * ∑ i, (m i : ℝ) * (z i).im)) ≤ b m) →
          ‖f z‖ ≤ ∑' m, b m) := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · exact ⟨0, fun _ => le_rfl, fun z hz => hz.elim, fun z hz => hz.elim⟩
  set G : (ι → ℤ) → (ι → ℂ) → ℂ :=
    fun m z => f z * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * z i) with hG
  have key : ∀ m, ∀ w ∈ U, ‖∫ x in Set.Icc (0 : ι → ℝ) 1, f ((fun i => (x i : ℂ)) + w) *
        cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))‖ =
      ‖∫ x in Set.Icc (0 : ι → ℝ) 1, G m ((fun i => (x i : ℂ)) + w₀)‖ *
        Real.exp (-(2 * π * ∑ i, (m i : ℝ) * (w i).im)) := by
    intro m w hw
    have h := setIntegral_unitCube_tube (f := G m) hU hU' htube
      (hf.mul (Differentiable.differentiableOn (by fun_prop))) (fun z hz i => by
        simp only [hG]
        rw [hper z hz]
        congr 1
        have e : ∑ j, (m j : ℂ) * (z + (Pi.single i 1 : ι → ℂ)) j
            = ∑ j, (m j : ℂ) * z j + m i := by
          simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
        rw [e, mul_add, Complex.exp_add]
        have : cexp (-(2 * Real.pi * I) * (m i : ℂ)) = 1 := by
          have := Complex.exp_int_mul_two_pi_mul_I (-m i)
          rw [← this]
          congr 1
          push_cast
          ring
        rw [this, mul_one]) hw₀ hw
    have e : Real.exp (-(2 * π * ∑ i, (m i : ℝ) * (w i).im)) =
        ‖cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i)‖ := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.im_sum]
    rw [h, e, ← norm_mul, ← integral_mul_const]
    congr 2
    funext x
    simp only [hG]
    rw [mul_assoc (f _), ← Complex.exp_add]
    congr 2
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  refine ⟨fun m => ‖∫ x in Set.Icc (0 : ι → ℝ) 1, G m ((fun i => (x i : ℂ)) + w₀)‖,
    fun _ => norm_nonneg _, fun z hz M hM m => ?_, fun z hz b hb hle => ?_⟩
  · rw [← key m z hz]
    have hv : (volume : Measure (ι → ℝ)).real (Set.Icc (0 : ι → ℝ) 1) = 1 := by
      simp [measureReal_def, Real.volume_Icc_pi]
    refine le_of_le_of_eq (norm_setIntegral_le_of_norm_le_const (C := M)
      isCompact_Icc.measure_lt_top fun x _ => ?_) (by rw [hv, mul_one])
    rw [norm_mul, Complex.norm_exp]
    have : (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.im_sum]
    rw [this, Real.exp_zero, mul_one]
    exact hM x
  · have := norm_le_tsum_of_cube_fourierCoeff_le
      (A := fun x : ι → ℝ => f ((fun i => (x i : ℂ)) + z))
      (hf.continuousOn.comp_continuous (by fun_prop) fun x => htube z hz x) (fun i x => by
        rw [← hper _ (htube z hz x) i]
        congr 1
        funext j
        by_cases hij : j = i
        · subst hij; simp; ring
        · simp [hij]) hb (fun m => by rw [key m z hz]; exact hle m) 0
    have h1 : (fun i => (((0 : ι → ℝ) i : ℝ) : ℂ)) + z = z := by
      funext j; simp
    rwa [h1] at this
end GlobalTheory.Koecher
