-- Prove2me | solution 1 for GlobalTheory.SmallPoint.exists_root_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:50.743807+00:00
-- url     : https://prove2.me/submissions/d193d0be-3a31-48f3-9be7-a0d846673761

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit
import Theorems.Thm_GlobalTheory_RootNormLowerBound_exists_root_norm_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open GlobalTheory
open GlobalTheory.SmallPoint
namespace GlobalTheory.SmallPoint
theorem _root_.solution {F : ℂ[X]} (hF : F.Monic) {ε : ℝ} (hε : 0 < ε)
    (h : ‖F.coeff 0‖ < ε ^ F.natDegree) : ∃ t, F.IsRoot t ∧ ‖t‖ < ε := by
  first
  | exact @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | (apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt ..)
end GlobalTheory.SmallPoint
