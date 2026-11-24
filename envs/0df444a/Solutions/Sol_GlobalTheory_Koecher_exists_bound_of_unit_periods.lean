-- Prove2me | solution 1 for GlobalTheory.Koecher.exists_bound_of_unit_periods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:47.127181+00:00
-- url     : https://prove2.me/submissions/f279d79c-5cd8-4f6f-9141-a664d7f687c8

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
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
namespace GlobalTheory.Koecher
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : (ι → ℝ) → ℂ} (hc : Continuous A) (hA : ∀ (i : ι) x, A (x + Pi.single i 1) = A x) :
    ∃ M, ∀ x, ‖A x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨M, fun x => ?_⟩
  have h := apply_add_intCast_vec_of_unit_periods hA (fun i => ⌊x i⌋) fun i => Int.fract (x i)
  have e : ((fun i => Int.fract (x i)) + fun i => ((⌊x i⌋ : ℤ) : ℝ)) = x := by
    funext i; simp
  rw [e] at h
  rw [h]
  exact hM _ ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
end GlobalTheory.Koecher
