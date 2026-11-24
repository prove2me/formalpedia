-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.mem_UG_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:39:28.95872+00:00
-- url     : https://prove2.me/submissions/01d8478e-2059-4d96-a628-b5558e92f0dd

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_form_toE
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
theorem _root_.solution (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (g : GL (Fin n) L) :
    g ∈ UG s J ↔ IsIso (form s J) (toE g) := by
  have hm : g ∈ UG s J ↔ (g.1.map s).transpose * J * g.1 = J := Iff.rfl
  rw [hm]
  constructor
  · intro h x y
    rw [form_toE, h, form]
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [form_toE, form] at this
    have hsi : s ∘ (Pi.single i 1 : Fin n → L) = Pi.single i 1 := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [hsi] at this
    simpa using this
end GlobalTheory.CompanionTheory.CartanU
