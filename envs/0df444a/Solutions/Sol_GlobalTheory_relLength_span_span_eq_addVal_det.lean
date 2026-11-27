-- Prove2me | solution 1 for GlobalTheory.relLength_span_span_eq_addVal_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:38.100511+00:00
-- url     : https://prove2.me/submissions/4cf1505a-80d9-4be1-867b-52d08fed7b17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsDualNeZeroCompEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthSelfEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsLinearEquivMapLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthOfCommonLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_relLength_span_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {a v : ι → V} (ha : LinearIndependent R a)
    (P : Matrix ι ι R) (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      addVal R P.det := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_8 h_9; revert R h_1 h_2 h_3 V h_5 h_6 ι h_8 h_9 a v ha P hv; exact @_root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq)
  | exact @_root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq
  | exact _root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq
  | (apply _root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq ..)
end GlobalTheory
