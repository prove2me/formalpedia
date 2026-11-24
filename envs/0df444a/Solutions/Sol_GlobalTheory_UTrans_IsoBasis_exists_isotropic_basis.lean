-- Prove2me | solution 1 for GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:17:57.510805+00:00
-- url     : https://prove2.me/submissions/f34363d0-be5f-499e-8a72-895f83eeb573

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors
import Theorems.Thm_GlobalTheory_UTrans_IsoBasis_hf_symm
import Theorems.Thm_GlobalTheory_UTrans_IsoBasis_hfL_ne
import Theorems.Thm_GlobalTheory_UTrans_IsoBasis_exists_isotropic_avoid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.IsoBasis
variable {E : Type} [Field E] {n : ℕ}
namespace GlobalTheory.UTrans.IsoBasis
theorem _root_.solution (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) (x y : Fin n → E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧
      ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  let S : Set (Fin n → E) := {z | hf σ G z z = 0 ∧ hf σ G x z ≠ 0 ∧ hf σ G y z ≠ 0}
  have hspan : Submodule.span E S = ⊤ := by
    by_contra h
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
    obtain ⟨z, hz0, hz1⟩ := exists_isotropic_avoid hG hz ![g, hfL σ G x, hfL σ G y] (by
      intro i
      fin_cases i
      · by_contra h
        push_neg at h
        exact hg0 (LinearMap.ext h)
      · exact hfL_ne hG hx
      · exact hfL_ne hG hy)
    have hzS : z ∈ S := by
      refine ⟨hz0, fun h => hz1 1 ?_, fun h => hz1 2 ?_⟩
      · show hf σ G z x = 0
        rw [← hf_symm hG, h, map_zero]
      · show hf σ G z y = 0
        rw [← hf_symm hG, h, map_zero]
    exact hz1 0 (hg (Submodule.subset_span hzS))
  obtain ⟨v, hvS, -, hv⟩ := Submodule.exists_fun_fin_finrank_span_eq E S
  have hn : n = Module.finrank E (Submodule.span E S) := by
    rw [hspan]; simp
  exact ⟨v ∘ Fin.cast hn, hv.comp _ (Fin.cast_injective hn), fun i => hvS _⟩
end GlobalTheory.UTrans.IsoBasis
