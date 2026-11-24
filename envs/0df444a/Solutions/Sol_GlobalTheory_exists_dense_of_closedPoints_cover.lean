-- Prove2me | solution 1 for GlobalTheory.exists_dense_of_closedPoints_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:07.633883+00:00
-- url     : https://prove2.me/submissions/e175c589-b486-40e5-a6a1-e08efa181500

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
namespace GlobalTheory
theorem _root_.solution [IrreducibleSpace T] {ι : Type*} [Finite ι]
    (S : ι → Set T) (h : ∀ x, IsClosed ({x} : Set T) → ∃ i, x ∈ S i) : ∃ i, Dense (S i) := by
  have hc : (⋃ i, closure (S i)) = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints (X := T),
      (isClosed_iUnion_of_finite fun i => isClosed_closure).closure_subset_iff]
    intro x hx
    obtain ⟨i, hi⟩ := h x hx
    exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
  classical
  have := Fintype.ofFinite ι
  obtain ⟨Z, hZ, hZ'⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ T) (Finset.univ.image fun i => closure (S i))
    (by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact isClosed_closure)
    (by
      intro x _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc ▸ Set.mem_univ x : x ∈ ⋃ i, closure (S i))
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ
  exact ⟨i, fun x => hZ' (Set.mem_univ x)⟩
end GlobalTheory
