-- Prove2me | solution 1 for LosslessCond.section_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:00:49.918699+00:00
-- url     : https://prove2.me/submissions/602fe98a-2644-47eb-a1df-0aec85e855bc

import Mathlib
import Definitions.Def_LosslessCond_domain

namespace Aux_LosslessCond32
open LosslessCond

theorem bobBits_nonempty {X : Type} : ∀ {s : ℕ} (P : PartialProtocol X s), Nonempty P.BobBits
  | _, .leaf _ => ⟨()⟩
  | _, .alice _ p₀ p₁ => ⟨((bobBits_nonempty p₀).some, (bobBits_nonempty p₁).some)⟩
  | _, .bob p₀ p₁ => ⟨(true, (bobBits_nonempty p₀).some, (bobBits_nonempty p₁).some)⟩

end Aux_LosslessCond32

open LosslessCond in
theorem solution {X Y : Type} (M : X → Y → Bool) :
    (∀ (b : Bool) (U : Set X),
      domain M (PartialProtocol.leaf b) U = {y | ∀ x ∈ U, M x y = b}) ∧
    (∀ (s : ℕ) (f : X → Bool) (p₀ p₁ : PartialProtocol X s) (U : Set X),
      domain M (PartialProtocol.alice f p₀ p₁) U =
        domain M p₀ (U ∩ {x | f x = false}) ∩ domain M p₁ (U ∩ {x | f x = true})) ∧
    (∀ (s : ℕ) (p₀ p₁ : PartialProtocol X s) (U : Set X),
      domain M (PartialProtocol.bob p₀ p₁) U = domain M p₀ U ∪ domain M p₁ U) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b U
    ext y
    simp only [domain, Set.mem_setOf_eq, PartialProtocol.run]
    constructor
    · rintro ⟨_, h⟩ x hx
      exact (h x hx).symm
    · intro h
      exact ⟨(), fun x hx => (h x hx).symm⟩
  · intro s f p₀ p₁ U
    ext y
    simp only [domain, Set.mem_setOf_eq, Set.mem_inter_iff, PartialProtocol.run]
    constructor
    · rintro ⟨β, h⟩
      refine ⟨⟨β.1, fun x hx => ?_⟩, ⟨β.2, fun x hx => ?_⟩⟩
      · have := h x hx.1
        have hf : f x = false := hx.2
        simpa [hf] using this
      · have := h x hx.1
        have hf : f x = true := hx.2
        simpa [hf] using this
    · rintro ⟨⟨β₀, h₀⟩, ⟨β₁, h₁⟩⟩
      refine ⟨(β₀, β₁), fun x hx => ?_⟩
      cases hfx : f x
      · simpa [hfx] using h₀ x ⟨hx, hfx⟩
      · simpa [hfx] using h₁ x ⟨hx, hfx⟩
  · intro s p₀ p₁ U
    ext y
    simp only [domain, Set.mem_setOf_eq, Set.mem_union, PartialProtocol.run]
    constructor
    · rintro ⟨⟨c, β₀, β₁⟩, h⟩
      cases c
      · left; exact ⟨β₀, fun x hx => by simpa using h x hx⟩
      · right; exact ⟨β₁, fun x hx => by simpa using h x hx⟩
    · rintro (⟨β₀, h₀⟩ | ⟨β₁, h₁⟩)
      · exact ⟨(false, β₀, (Aux_LosslessCond32.bobBits_nonempty p₁).some),
          fun x hx => by simpa using h₀ x hx⟩
      · exact ⟨(true, (Aux_LosslessCond32.bobBits_nonempty p₀).some, β₁),
          fun x hx => by simpa using h₁ x hx⟩
