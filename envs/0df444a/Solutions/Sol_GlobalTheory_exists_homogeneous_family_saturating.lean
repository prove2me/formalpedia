-- Prove2me | solution 1 for GlobalTheory.exists_homogeneous_family_saturating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:49:50.643698+00:00
-- url     : https://prove2.me/submissions/38f4fe34-a9ea-459a-be26-ddeeff8c3146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomogeneousFamilySaturating
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ], (∀ i : ι, ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M)) → ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) ∧ ∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ hT
  choose T hT using hT
  choose S hS using fun m : M => _root_.GlobalTheory.exists_sum_grProj ℳ m
  classical
  let G : Finset (ℤ × M) := (Finset.univ.biUnion T).biUnion fun t =>
    (S t).image fun j => (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t)
  refine ⟨G.card, fun l => (G.equivFin.symm l).1.1, fun l => (G.equivFin.symm l).1.2,
    fun l => ?_, fun i y => ?_⟩
  · have hmem := (G.equivFin.symm l).2
    obtain ⟨t, -, hj⟩ := Finset.mem_biUnion.1 hmem
    obtain ⟨j, -, hjeq⟩ := Finset.mem_image.1 hj
    show (G.equivFin.symm l : ℤ × M).2 ∈ ℳ (G.equivFin.symm l : ℤ × M).1
    rw [← hjeq]
    exact _root_.GlobalTheory.GradedHilbert.proj_mem ℳ j t
  · obtain ⟨k, hk⟩ := hT i y
    refine ⟨k, Submodule.span_le.2 ?_ hk⟩
    intro t ht
    rw [← hS t]
    refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ?_
    have hG : (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t) ∈ G :=
      Finset.mem_biUnion.2 ⟨t, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩,
        Finset.mem_image.2 ⟨j, hj, rfl⟩⟩
    exact ⟨G.equivFin ⟨_, hG⟩, by simp⟩
end _root_.GlobalTheory
end GlobalTheory
