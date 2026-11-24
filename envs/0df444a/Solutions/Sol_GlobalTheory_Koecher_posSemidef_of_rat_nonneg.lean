-- Prove2me | solution 1 for GlobalTheory.Koecher.posSemidef_of_rat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:30.816973+00:00
-- url     : https://prove2.me/submissions/54a6e626-073e-47a1-93ba-45717b5644df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe

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
theorem _root_.solution {g : ℕ} {T : Matrix (Fin g) (Fin g) ℤ} (hT : T.IsSymm)
    (h : ∀ v : Fin g → ℚ, 0 ≤ v ⬝ᵥ (T.map (Int.cast : ℤ → ℚ)).mulVec v) :
    (T.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp [hT.apply i j]
  · rw [star_trivial]
    have hd : DenseRange (Pi.map fun (_ : Fin g) => (Rat.cast : ℚ → ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on x (isClosed_le continuous_const (by fun_prop)) fun v => ?_
    have := h v
    simp only [dotProduct, mulVec, Matrix.map_apply, Pi.map_apply] at this ⊢
    exact_mod_cast this
end GlobalTheory.Koecher
