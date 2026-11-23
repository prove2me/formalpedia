-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.dvd_of_dvd_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:17.887671+00:00
-- url     : https://prove2.me/submissions/882793f7-e9b7-44bb-9ae5-00a4a83bdcc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ConjIdeal
variable {O : Type*} [CommRing O]
namespace GlobalTheory.ConjIdeal
theorem _root_.solution (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, bar x • d y = M • z) (y : X) : ∃ z : Y, d y = M • z := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
  obtain ⟨z₁, hz₁⟩ := h₁ j hj y
  obtain ⟨z₂, hz₂⟩ := h₂ (bar i) (Ideal.mem_map_of_mem bar hi) y
  rw [hbar] at hz₂
  refine ⟨z₂ + z₁, ?_⟩
  rw [smul_add, ← hz₁, ← hz₂, map_smul, ← add_smul, hij, one_smul]
end GlobalTheory.ConjIdeal
