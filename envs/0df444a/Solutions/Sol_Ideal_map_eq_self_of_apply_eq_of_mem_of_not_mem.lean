-- Prove2me | solution 1 for Ideal.map_eq_self_of_apply_eq_of_mem_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/95e329b2-fbf5-5380-bb23-fb193899851d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem

set_option autoImplicit false

theorem solution
    {S : Type*} [CommRing S] (γ : S ≃+* S) {P₁ P₂ : Ideal S}
    (h₁ : P₁.map (γ : S →+* S) = P₁ ∨ P₁.map (γ : S →+* S) = P₂)
    (h₂ : P₂.map (γ : S →+* S) = P₁ ∨ P₂.map (γ : S →+* S) = P₂)
    {a : S} (hγa : γ a = a) (ha₁ : a ∈ P₁) (ha₂ : a ∉ P₂) :
    P₁.map (γ : S →+* S) = P₁ ∧ P₂.map (γ : S →+* S) = P₂ := by
  have hmem : a ∈ P₁.map (γ : S →+* S) := by
    rw [← hγa]; exact Ideal.mem_map_of_mem _ ha₁
  have hP₁ : P₁.map (γ : S →+* S) = P₁ := by
    rcases h₁ with h | h
    · exact h
    · exact absurd (h ▸ hmem) ha₂
  refine ⟨hP₁, ?_⟩
  rcases h₂ with h | h
  ·
    exfalso
    have hinj : Function.Injective (Ideal.map (γ : S →+* S)) := fun I J hIJ => by
      have := congrArg (Ideal.map ((γ.symm : S ≃+* S) : S →+* S)) hIJ
      rwa [Ideal.map_map, Ideal.map_map, show ((γ.symm : S ≃+* S) : S →+* S).comp (γ : S →+* S) = RingHom.id S
        from by ext x; simp, Ideal.map_id, Ideal.map_id] at this
    have : P₂ = P₁ := hinj (h.trans hP₁.symm)
    exact ha₂ (this ▸ ha₁)
  · exact h

end S_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem
end P2MW
export P2MW.S_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem (solution)
