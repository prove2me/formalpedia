-- Prove2me | solution 1 for GlobalTheory.Doubling.exists_leviElt_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:06:13.998954+00:00
-- url     : https://prove2.me/submissions/e6a8c784-6577-4329-bb36-e83bbf1122d1

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_leviElt_mem_UJ
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
variable [Invertible (2 : A)]
namespace GlobalTheory.Doubling
theorem _root_.solution {σ : A →+* A} (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hJ : cT σ J = J)
    (hu : IsUnit J.det) (α : GL n A) : ∃ β : GL n A, leviElt e (α, β) ∈ UJ σ (dblGram e J) := by
  have hc : ∀ X : Matrix n n A, cT σ (cT σ X) = X := fun X => by ext i j; exact hσ _
  obtain ⟨U, rfl⟩ := (isUnit_iff_isUnit_det J).2 hu
  let γ : GL n A := U * α⁻¹ * U⁻¹
  let β : GL n A := ⟨cT σ γ.1, cT σ γ⁻¹.1, by rw [← cT_mul, Units.inv_mul, cT_one], by rw [← cT_mul, Units.mul_inv, cT_one]⟩
  have h1 : cT σ β.1 * U.1 * α.1 = U.1 := by
    rw [show cT σ β.1 = γ.1 from hc _, ← Units.val_mul, ← Units.val_mul]
    simp [γ]
  refine ⟨β, leviElt_mem_UJ e h1 ?_⟩
  have := congrArg (cT σ) h1
  rwa [cT_mul, cT_mul, hc, hJ, ← Matrix.mul_assoc] at this
end GlobalTheory.Doubling
