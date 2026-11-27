-- Prove2me | solution 1 for GlobalTheory.relLength_map_eq_addVal_det_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:06.898855+00:00
-- url     : https://prove2.me/submissions/4e16e6fe-6b92-42ae-b96a-afbc916b7cdd

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
import Theorems.Thm_GlobalTheory_LengthCokernelInjective_relLength_map_eq_addVal_det


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
theorem _root_.solution {A : Submodule R V} [Module.Free R A]
    [Module.Finite R A] (g : V →ₗ[R] V) (hg : ∀ x ∈ A, g x ∈ A) :
    relLength A (A.map g) = addVal R (LinearMap.det (g.restrict hg)) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_8 h_9; revert R h_1 h_2 h_3 V h_5 h_6 A h_8 h_9 g hg; exact @_root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det)
  | exact @_root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det
  | exact _root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det ..)
end GlobalTheory
