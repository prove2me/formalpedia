-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.sc_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:23.481815+00:00
-- url     : https://prove2.me/submissions/766f901c-aee3-44e5-908e-064490c5aa19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open LaurentPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution {α : Type} [Fintype α] (M N : Matrix α α K) (p q q' s : α → ℤ) (hq : ∀ a, q a + q' a = 0) :
    sc M p q * sc N q' s = sc (M * N) p s := by
  ext1 a b
  simp only [sc, Matrix.mul_apply, Matrix.of_apply, map_sum, Finset.sum_mul, map_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : p a + s b = (p a + q c) + (q' c + s b) := by linear_combination -hq c
  rw [this, T_add (p a + q c)]
  ring
end GlobalTheory.DegCnt.PosJ
