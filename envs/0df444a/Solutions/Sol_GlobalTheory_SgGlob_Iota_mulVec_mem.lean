-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:28.34765+00:00
-- url     : https://prove2.me/submissions/46739054-3191-4ec7-b872-71eeca4da06d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mem_frameLat
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mulVec_eq_add
import Theorems.Thm_GlobalTheory_SgGlob_mem_mulLat
import Theorems.Thm_GlobalTheory_SgGlob_mulLat_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
namespace GlobalTheory.SgGlob.Iota
theorem _root_.solution (hg : (g : E) ≠ 0) (hΛ : pairLat g P P' ≤ Λ) {a : Fin (r + 1) → E}
    (ha : ∀ b : Fin (r + 1), a b ∈ dInv E (r - (b : ℕ))) :
    P *ᵥ a ∈ Λ ∧ P' *ᵥ a ∈ Λ ∧ P' *ᵥ a - P *ᵥ a ∈ mulLat g Λ := by
  have h1 : P *ᵥ a ∈ Λ := hΛ (Submodule.mem_sup_left ((mem_frameLat _ _).2 ⟨a, ha, rfl⟩))
  have h2 : P' *ᵥ a - P *ᵥ a ∈ mulLat g Λ :=
    (mem_mulLat g Λ _).2 ⟨_, hΛ (Submodule.mem_sup_right ((mem_frameLat _ _).2 ⟨a, ha, rfl⟩)), by
      rw [mulVec_eq_add hg P P' a, add_sub_cancel_left]⟩
  refine ⟨h1, ?_, h2⟩
  rw [← add_sub_cancel (P *ᵥ a) (P' *ᵥ a)]
  exact add_mem h1 (mulLat_le g Λ h2)
end GlobalTheory.SgGlob.Iota
