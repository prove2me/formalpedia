-- Prove2me | solution 1 for InverseGalois.exists_regularFractionField_embedding_complex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T01:51:14.436761+00:00
-- url     : https://prove2.me/submissions/ac4152d3-82f5-4a1b-b6ae-7402e91124af

import Definitions.Def_InverseGalois_regular_action
import Theorems.Thm_InverseGalois_exists_algebraicallyIndependent_complex_family

open InverseGalois

universe u

theorem solution (G : Type u) [Fintype G] [Group G] :
    Nonempty (RegularFractionField G →ₐ[ℚ] ℂ) := by
  obtain ⟨x, hx⟩ :=
    exists_algebraicallyIndependent_complex_family (Shrink.{0} G)
  let eval : RegularPolynomialRing G →ₐ[ℚ] ℂ := MvPolynomial.aeval x
  refine ⟨IsFractionRing.liftAlgHom (g := eval) ?_⟩
  intro p q hpq
  apply hx.aevalEquiv.injective
  apply Subtype.ext
  exact hpq
