-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.form_toE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:22:53.493951+00:00
-- url     : https://prove2.me/submissions/db56a8dd-deb7-4466-ac93-0202dc0ae517

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
theorem _root_.solution (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (g : GL (Fin n) L) (x y : Fin n → L) :
    form s J (toE g x) (toE g y) = dotProduct (s ∘ x) (((g.1.map s).transpose * J * g.1).mulVec y) := by
  have h1 : s ∘ (g.1.mulVec x) = (g.1.map s).mulVec (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s g.1 x i
  simp only [form, toE_apply, h1]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (s ∘ x),
    Matrix.vecMul_transpose]
end GlobalTheory.CompanionTheory.CartanU
