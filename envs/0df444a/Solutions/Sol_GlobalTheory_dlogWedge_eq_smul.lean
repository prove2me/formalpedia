-- Prove2me | solution 1 for GlobalTheory.dlogWedge_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:23.898387+00:00
-- url     : https://prove2.me/submissions/a30646cb-dabd-4396-9034-609d9ffa74f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
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

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}
namespace GlobalTheory
theorem _root_.solution (S : Finset (Fin p)) (x : Fin p → F) :
    dlogWedge K S x = (∏ k ∈ S, x k)⁻¹ • dWedge K x := by
  have : (fun k => if k ∈ S then (x k)⁻¹ • D K F (x k) else D K F (x k))
      = fun k => (if k ∈ S then (x k)⁻¹ else 1) • D K F (x k) := by
    funext k
    split_ifs <;> simp
  rw [dlogWedge, this, AlternatingMap.map_smul_univ, dWedge]
  congr 1
  simp [Finset.prod_ite_mem]
end GlobalTheory
