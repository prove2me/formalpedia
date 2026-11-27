-- Prove2me | solution 1 for GlobalTheory.signedLength_eq_log_ordFrac_det_of_bases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:21.326455+00:00
-- url     : https://prove2.me/submissions/f360aecf-cef3-4eb4-9a22-37a260688452

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
import Theorems.Thm_GlobalTheory_SignedLengthLogDet_signedLength_eq_log_ordFrac_det


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
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {A B : Submodule R V} (a : Basis ι R A)
    (b : Basis ι R B) (g : Matrix ι ι K) (hg : g.det ≠ 0)
    (hb : ∀ j, (b j : V) = ∑ i, g i j • (a i : V)) :
    LengthCommensurable A B ∧ signedLength A B = WithZero.log (Ring.ordFrac R g.det) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14 h_15; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 ι h_14 h_15 A B a b g hg hb; exact @_root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det)
  | exact @_root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det
  | exact _root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det
  | (apply _root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det ..)
end GlobalTheory
