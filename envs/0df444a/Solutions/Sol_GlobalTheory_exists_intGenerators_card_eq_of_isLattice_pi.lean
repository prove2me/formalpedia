-- Prove2me | solution 1 for GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:06.335464+00:00
-- url     : https://prove2.me/submissions/3f363353-7dc2-480f-bedc-e757361ae49d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntGeneratorsCardEqOfIsLatticePi
import Theorems.Thm_GlobalTheory_mem_ratSpan_of_isLattice_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E : Type) [Field E] [NumberField E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) :
    ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E,
      (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧ Submodule.span ℚ (Set.range u) = ⊤ := by
  classical
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hΛ))
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  have : Module.Free ℤ Λ := inferInstance
  let b := Module.Free.chooseBasis ℤ Λ
  let f : Λ →ₗ[ℤ] (Fin n → E) := Λ.subtype.toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  let v : Module.Free.ChooseBasisIndex ℤ Λ → Fin n → E := f ∘ b
  have hZ : LinearIndependent ℤ v := b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
  have hspan : ∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range v) := by
    intro x
    have h := congrArg (Submodule.map f) b.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top] at h
    change x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range (f ∘ b))
    rw [h]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  have hQ : Submodule.span ℚ (Set.range v) = ⊤ :=
    eq_top_iff.2 fun x _ => mem_ratSpan_of_isLattice_pi E n Λ hΛ _
      (fun y hy => Submodule.span_le_restrictScalars ℤ ℚ _ ((hspan y).1 hy)) x
  have hQi : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hZ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = Module.finrank ℚ E * n := by
    rw [← finrank_span_eq_card hQi, hQ, finrank_top, Module.finrank_pi_fintype]
    simp [mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  have hr : Set.range (v ∘ e.symm) = Set.range v := e.symm.surjective.range_comp v
  exact ⟨v ∘ e.symm, by rw [hr]; exact hspan, by rw [hr]; exact hQ⟩
end GlobalTheory
