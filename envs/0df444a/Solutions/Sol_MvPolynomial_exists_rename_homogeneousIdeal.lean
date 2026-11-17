-- Prove2me | solution 1 for MvPolynomial.exists_rename_homogeneousIdeal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:02.677522+00:00
-- url     : https://prove2.me/submissions/43b186c6-f1e3-48a2-bbbc-f2387fe8d82d

import Mathlib

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial

/-- Renaming coordinates transports a homogeneous ideal and its vanishing
conditions over every coefficient ring. -/
theorem _root_.solution {R S T : Type} [CommRing R]
    (e : S ≃ T) (I : HomogeneousIdeal (homogeneousSubmodule S R)) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule T R),
      ∀ (A : Type) [CommRing A] (f : R →+* A) (z : T → A),
        (∀ p ∈ J.toIdeal, eval₂ f z p = 0) ↔
          ∀ p ∈ I.toIdeal, eval₂ f (z ∘ e) p = 0 := by
  let J := I.toIdeal.comap (rename e.symm).toRingHom
  have hJ : J.IsHomogeneous (homogeneousSubmodule T R) := by
    have heq : (J.homogeneousCore (homogeneousSubmodule T R)).toIdeal = J := by
      apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
      intro p hp
      rw [← sum_homogeneousComponent p]
      apply Ideal.sum_mem
      intro n hn
      apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
        ⟨n, homogeneousComponent_isHomogeneous n p⟩
      change rename e.symm (homogeneousComponent n p) ∈ I.toIdeal
      rw [rename_homogeneousComponent]
      exact homogeneousComponent_mem_of_mem I.isHomogeneous hp n
    rw [← heq]
    exact (J.homogeneousCore (homogeneousSubmodule T R)).isHomogeneous
  refine ⟨⟨J, hJ⟩, ?_⟩
  intro A _ f z
  constructor
  · intro h p hp
    have hp' : rename e p ∈ J := by
      change rename e.symm (rename e p) ∈ I.toIdeal
      simpa only [rename_rename, Equiv.symm_comp_self, rename_id, AlgHom.id_apply] using hp
    simpa only [eval₂_rename] using h (rename e p) hp'
  · intro h p hp
    have he := h (rename e.symm p) hp
    simpa only [eval₂_rename, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id] using he

end MvPolynomial
