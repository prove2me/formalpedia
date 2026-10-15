-- Prove2me | solution 1 for OAI.CompactBanach.finite_coordinate_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:21:37.248456+00:00
-- url     : https://prove2.me/submissions/75b418ce-bef6-4813-ae75-35896dc154fb

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/CoordinateSupport.lean:L69-L85
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.finite_coordinate_support. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport

-- ---- from OAI.Geometry.DoublingHilbert.CoordinateSupport ----
namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach
open DoublingHilbert

                                                                        
theorem point_apply_of_not_mem_support (p : Base) (w : Tuple) {i : ℕ}
    (hi : i ∉ pointSupport w) : point p w i = 0 := by
  classical
  have h0 : i ≠ 0 := by intro h; subst i; simp [pointSupport] at hi
  have h1 : i ≠ 1 := by intro h; subst i; simp [pointSupport] at hi
  have hj (j : ℕ) (hj : j ∈ w.support) : i ≠ coordinate j (w j - 1) := by
    intro he
    apply hi
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨j, hj, he.symm⟩
  simp only [point, lp.coeFn_add, Pi.add_apply, baseVector, tupleVector, lp.coeFn_sum,
    Finset.sum_apply, levelVector]
  simp only [lp.single_apply_ne _ _ _ h0, lp.single_apply_ne _ _ _ h1, zero_add]
  exact Finset.sum_eq_zero fun level hlevel => lp.single_apply_ne _ _ _ (hj level hlevel)

theorem finite_coordinate_support (X : Finset RealL2)
    (hX : ∀ z ∈ X, z ∈ constructedSet) :
    ∃ I : Finset ℕ, ∀ z ∈ X, ∀ i ∉ I, z i = 0 := by
  classical
  have h : ∀ z : X, ∃ I : Finset ℕ, ∀ i ∉ I, (z : RealL2) i = 0 := by
    intro z
    obtain ⟨p, w, _, he⟩ := hX z z.property
    refine ⟨pointSupport w, ?_⟩
    intro i hi
    rw [he]
    exact point_apply_of_not_mem_support p w hi
  choose I hI using h
  refine ⟨Finset.univ.biUnion I, ?_⟩
  intro z hz i hi
  apply hI ⟨z, hz⟩ i
  intro hmem
  exact hi (Finset.mem_biUnion.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, hmem⟩)

end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open DoublingHilbert


theorem solution : type_of% @_root_.OAI.CompactBanach.finite_coordinate_support := @_root_.OAI.CompactBanach.finite_coordinate_support
