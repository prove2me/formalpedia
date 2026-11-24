-- Prove2me | solution 1 for GlobalTheory.Koecher.norm_le_tsum_of_cube_fourierCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:26.955296+00:00
-- url     : https://prove2.me/submissions/2109d3b3-ea0b-402a-991f-129c165157a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Theorems.Thm_GlobalTheory_apply_add_intCast_vec_of_unit_periods


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
    {A : (ι → ℝ) → ℂ} (hc : Continuous A)
    (hA : ∀ (i : ι) x, A (x + Pi.single i 1) = A x) {b : (ι → ℤ) → ℝ} (hb : Summable b)
    (h : ∀ m : ι → ℤ, ‖∫ x in Set.Icc (0 : ι → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))‖ ≤ b m) (y : ι → ℝ) :
    ‖A y‖ ≤ ∑' m, b m := by
  set p : (ι → ℝ) → UnitAddTorus ι := fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus ι → ℂ := fun z ↦ A (Function.surjInv hq.surjective z) with hf₀
  have hfp : ∀ x, f₀ (p x) = A x := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : ∀ i, ∃ n : ℤ, (n : ℝ) = x' i - x i := fun i ↦ by
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      exact ⟨n, by simpa using hn⟩
    choose n hn using h2
    rw [← apply_add_intCast_vec_of_unit_periods hA n x]
    change A x' = _
    congr 1
    funext i
    simp [hn]
  let f : C(UnitAddTorus ι, ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A from funext hfp]; exact hc⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier (-n) (p x) =
      cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ)) := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  have hcoeff : ∀ n, ‖UnitAddTorus.mFourierCoeff f n‖ ≤ b n := fun n ↦ by
    refine le_of_eq_of_le ?_ (h n)
    congr 1
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0]
    simp only [Pi.zero_apply, zero_add]
    have h2 : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ fun i ↦ Set.Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i) := by
      ext x; simp
    rw [h2, MeasureTheory.setIntegral_congr_set
      (μ := MeasureTheory.volume) MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp, smul_eq_mul, mul_comm]
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (Summable.of_norm_bounded hb hcoeff) (p y)
  change HasSum _ (f₀ (p _)) at hsum
  rw [hfp] at hsum
  refine hsum.norm_le_of_bounded hb.hasSum fun n => ?_
  rw [norm_smul]
  have := (UnitAddTorus.mFourier n).norm_coe_le_norm (p y)
  rw [UnitAddTorus.mFourier_norm] at this
  calc _ ≤ ‖UnitAddTorus.mFourierCoeff f n‖ * 1 := by gcongr
    _ ≤ b n := by rw [mul_one]; exact hcoeff n
end GlobalTheory.Koecher
