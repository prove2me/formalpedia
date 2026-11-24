-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.toE_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:33.792929+00:00
-- url     : https://prove2.me/submissions/207f691f-8159-4be2-853b-b79bc792ac3a

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_toE_ofE
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_mem_UG_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
variable {L : Type} [NontriviallyNormedField L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (t : (Fin n → L) ≃ₗ[L] (Fin n → L))
    (ht : IsIso (form s J) t) : ∃ g : UG s J, toE g.1 = t :=
  ⟨⟨ofE t, (mem_UG_iff s J _).2 (by rwa [toE_ofE])⟩, toE_ofE t⟩
end GlobalTheory.CompanionTheory.CartanU
