-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.toE_ofE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:52.626408+00:00
-- url     : https://prove2.me/submissions/735d579c-bf26-47f4-9414-d1fea95a94aa

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_toE_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
variable {L : Type} [NontriviallyNormedField L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution (t : (Fin n → L) ≃ₗ[L] (Fin n → L)) : toE (ofE t) = t := by
  ext1 x
  rw [toE_apply]
  simp [ofE, LinearMap.toMatrix'_mulVec]
end GlobalTheory.CompanionTheory.CartanU
