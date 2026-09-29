-- Prove2me | solution 1 for InverseGalois.inverse_galois_problem_over_some_number_field
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T01:55:07.453218+00:00
-- url     : https://prove2.me/submissions/cc6f7586-bf5b-4f18-9a98-1167a7d3bd8e

import Mathlib
import Definitions.Def_InverseGalois_realizability
import Definitions.Def_InverseGalois_regular_action
import Theorems.Thm_InverseGalois_exists_regularFractionField_faithfulAction
import Theorems.Thm_InverseGalois_exists_regularFractionField_embedding_complex
import Theorems.Thm_InverseGalois_fixedPoints_fieldRange_isRealizable

open InverseGalois

theorem solution {G : Type*} [Fintype G] [Group G] :
    ∃ K : IntermediateField ℚ ℂ, IsRealizable K G := by
  obtain ⟨action, hfaith⟩ := exists_regularFractionField_faithfulAction G
  letI : MulSemiringAction G (RegularFractionField G) := action
  letI : FaithfulSMul G (RegularFractionField G) := hfaith
  obtain ⟨ψ⟩ := exists_regularFractionField_embedding_complex G
  let φ : FixedPoints.subfield G (RegularFractionField G) →ₐ[ℚ] ℂ :=
    { ψ.toRingHom.comp
        (FixedPoints.subfield G (RegularFractionField G)).subtype with
      commutes' := by
        intro q
        simp }
  exact ⟨φ.fieldRange,
    fixedPoints_fieldRange_isRealizable G (RegularFractionField G) φ⟩
