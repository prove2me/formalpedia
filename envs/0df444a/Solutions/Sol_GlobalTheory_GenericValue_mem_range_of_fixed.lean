-- Prove2me | solution 1 for GlobalTheory.GenericValue.mem_range_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:06:27.753328+00:00
-- url     : https://prove2.me/submissions/0ede498e-f3ff-426e-943d-aeef6e933bae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GenericValue_exists_algHom_of_isTranscendenceBasis
import Theorems.Thm_GlobalTheory_GenericValue_algebraicIndependent_add_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.GenericValue
theorem _root_.solution [IsAlgClosed K] {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (a : Ω)
    (h : ∀ j : Ω →ₐ[K] Ω, j a = a) : a ∈ Set.range (algebraMap K Ω) := by
  by_contra ha
  have ht : Transcendental K a := fun hal => ha <| by
    have := minpoly.mem_range_of_degree_eq_one K a
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hal.isIntegral))
    exact this
  have hi : AlgebraicIndepOn K id ({a} : Set Ω) := by
    unfold AlgebraicIndepOn
    exact (algebraicIndependent_singleton_iff (⟨a, rfl⟩ : ({a} : Set Ω))).2 ht
  obtain ⟨t, hst, hb⟩ := exists_isTranscendenceBasis_superset hi
  obtain ⟨j, hj⟩ := exists_algHom_of_isTranscendenceBasis hb (algebraicIndependent_add_one hb.1)
  have := (h j).symm.trans (hj ⟨a, hst rfl⟩)
  simp at this
end GlobalTheory.GenericValue
