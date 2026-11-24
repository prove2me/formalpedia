-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.form_isHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:21:43.259392+00:00
-- url     : https://prove2.me/submissions/86be91a1-3232-4400-b88e-cc870504ec5b

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
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
theorem _root_.solution (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (hs : ∀ x, s (s x) = x)
    (hJ : (J.map s).transpose = J) (hd : J.det ≠ 0) : IsHerm s (form s J) := by
  refine ⟨fun x y z => ?_, fun a x y => ?_, fun x y => ?_, fun x hx => ?_⟩
  · simp [form, Matrix.mulVec_add, dotProduct_add]
  · simp [form, Matrix.mulVec_smul, dotProduct_smul]
  · have hJ' : ∀ i j, s (J i j) = J j i := fun i j => by
      have := congrFun (congrFun hJ j) i
      simpa [Matrix.transpose_apply, Matrix.map_apply] using this
    simp only [form, dotProduct, Matrix.mulVec, Function.comp, map_sum, map_mul, hs, Finset.mul_sum, hJ']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · have h1 : Matrix.vecMul (s ∘ x) J = 0 := by
      funext j
      have := hx (Pi.single j 1)
      simpa [form, Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.single_apply] using this
    have h2 : s ∘ x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hd h1
    funext i
    have h3 := congrFun h2 i
    have h4 : s (x i) = 0 := h3
    simpa using h4
end GlobalTheory.CompanionTheory.CartanU
