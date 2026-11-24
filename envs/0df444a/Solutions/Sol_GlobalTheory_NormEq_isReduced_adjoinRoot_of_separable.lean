-- Prove2me | solution 1 for GlobalTheory.NormEq.isReduced_adjoinRoot_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:41.914965+00:00
-- url     : https://prove2.me/submissions/80d5f3ff-a444-4544-8231-17f4c31a04c4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
import Theorems.Thm_GlobalTheory_ReducedAdjoinRootSeparable_isReduced_adjoinRoot_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution {k : Type} [Field k] {f : k[X]} (hf : f.Separable) :
    IsReduced (AdjoinRoot f) := by
  first
  | exact @_root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable
  | exact _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable
  | (apply _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> assumption)
  | (intros; apply _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable ..)
end GlobalTheory.NormEq
