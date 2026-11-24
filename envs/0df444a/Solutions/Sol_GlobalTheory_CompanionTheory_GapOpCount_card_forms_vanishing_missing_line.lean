-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:18.436801+00:00
-- url     : https://prove2.me/submissions/17b7d4d1-6c2c-46a5-b2bd-d38072b2147d

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpCount
namespace GlobalTheory.CompanionTheory.GapOpCount
theorem _root_.solution : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
    Module.finrank k M + (j + 1) = n + 1 →
    (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by
  intro k _ _ n j M hM hdim
  let E := dotProductEquiv k (Fin (n + 1))
  have hE : ∀ a x : Fin (n + 1) → k, E a x = a ⬝ᵥ x := fun a x => by
    simp [E, dotProductEquiv]
  let W : Submodule k (Fin (n + 1) → k) := M ⊔ Submodule.span k {e0 k n}
  let T : Submodule k (Fin (n + 1) → k) := W.dualAnnihilator.comap E.toLinearMap
  have hT : ∀ a, a ∈ T ↔ a ⬝ᵥ e0 k n = 0 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0 := by
    intro a
    simp only [T, W, Submodule.mem_comap, Submodule.mem_dualAnnihilator, LinearEquiv.coe_coe, hE]
    constructor
    · intro h
      exact ⟨h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
        fun x hx => h x (Submodule.mem_sup_left hx)⟩
    · rintro ⟨h0, h1⟩ w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [dotProduct_add, dotProduct_smul, h0, h1 x hx, smul_zero, add_zero]
  have hfr : Module.finrank k T = j := by
    have hmap : T.map E.toLinearMap = W.dualAnnihilator :=
      Submodule.map_comap_eq_of_surjective E.surjective _
    have h1 : Module.finrank k T = Module.finrank k W.dualAnnihilator := by
      rw [← hmap]
      exact (LinearEquiv.finrank_map_eq E T).symm
    have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    have h3 : Module.finrank k W = Module.finrank k M + 1 := Submodule.finrank_sup_span_singleton hM
    have h4 : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
    omega
  obtain ⟨f, hf0, hfM⟩ := Submodule.exists_le_ker_of_notMem hM
  obtain ⟨b, rfl⟩ := E.surjective f
  have hb0 : b ⬝ᵥ e0 k n ≠ 0 := by rwa [← hE]
  have hbM : ∀ x ∈ M, b ⬝ᵥ x = 0 := fun x hx => by
    rw [← hE]
    exact hfM hx
  let a0 : Fin (n + 1) → k := (b ⬝ᵥ e0 k n)⁻¹ • b
  have ha0 : a0 ⬝ᵥ e0 k n = 1 := by
    simp only [a0, smul_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ hb0
  have ha0M : ∀ x ∈ M, a0 ⬝ᵥ x = 0 := fun x hx => by
    simp only [a0, smul_dotProduct, hbM x hx, smul_zero]
  have hcard : (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card
      = (Finset.univ : Finset T).card := by
    refine Finset.card_bij' (fun a ha => ⟨a - a0, ?_⟩) (fun t _ => t.1 + a0) ?_ ?_ ?_ ?_
    · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 ha
      refine (hT _).2 ⟨?_, fun x hx => ?_⟩
      · rw [sub_dotProduct, h1, ha0, sub_self]
      · rw [sub_dotProduct, h2 x hx, ha0M x hx, sub_self]
    · intro a ha
      exact Finset.mem_univ _
    · intro t _
      obtain ⟨h1, h2⟩ := (hT t.1).1 t.2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, fun x hx => ?_⟩
      · rw [add_dotProduct, h1, ha0, zero_add]
      · rw [add_dotProduct, h2 x hx, ha0M x hx, add_zero]
    · intro a ha
      simp
    · intro t _
      ext1
      simp
  rw [hcard, Finset.card_univ, Module.card_eq_pow_finrank (K := k) (V := T), hfr]
end GlobalTheory.CompanionTheory.GapOpCount
