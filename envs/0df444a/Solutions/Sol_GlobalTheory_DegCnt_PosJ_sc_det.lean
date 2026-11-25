-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.sc_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:48.896787+00:00
-- url     : https://prove2.me/submissions/1702b2ef-bfa4-445e-b102-5f978a662dc6

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
theorem _root_.solution {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α K) (p : α → ℤ) :
    (sc M p p).det = C M.det * T (2 * ∑ a, p a) := by
  have hT : ∏ a, (T (p a) : K[T;T⁻¹]) = T (∑ a, p a) := by
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, T_add, ih]
  have h : sc M p p = Matrix.of fun a b => T (p a) *
      (Matrix.of fun a b => T (p b) * ((C : K →+* K[T;T⁻¹]).mapMatrix M) a b) a b := by
    ext1 a b
    simp only [sc, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, T_add]
    ring
  rw [h, Matrix.det_mul_column, Matrix.det_mul_row, ← RingHom.map_det, hT, two_mul, T_add]
  ring
end GlobalTheory.DegCnt.PosJ
