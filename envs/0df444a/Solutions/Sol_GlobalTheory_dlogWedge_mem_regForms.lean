-- Prove2me | solution 1 for GlobalTheory.dlogWedge_mem_regForms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:46.148553+00:00
-- url     : https://prove2.me/submissions/a5094fe9-8082-4184-a6d6-ae9ba3230a13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_P2M_GlobalTheory__Multi_mem_regForms_c782fe77fe92
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_dlog_unit_mem_range
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti
attribute [local simp] GlobalTheory.dlogWedge_empty

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}
variable {V : Type*} [CommRing V] [Algebra K V] [Algebra V F] [IsScalarTower K V F]
namespace GlobalTheory
theorem _root_.solution (S : Finset (Fin p)) (x : Fin p → V)
    (hS : ∀ k ∈ S, IsUnit (x k)) :
    dlogWedge K S (fun k => algebraMap V F (x k)) ∈ regForms K V F p := by
  refine ιMulti_mem_regForms K F _ fun k => ?_
  split_ifs with hk
  · obtain ⟨u, hu⟩ := hS k hk
    simp only [← hu]
    exact dlog_unit_mem_range K u
  · exact ⟨D K V (x k), map_D ..⟩
end GlobalTheory
