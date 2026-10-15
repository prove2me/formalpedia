-- Prove2me | solution 1 for OAI.CompactBanach.coordinateMap_single
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:23:17.241798+00:00
-- url     : https://prove2.me/submissions/a9990412-7e3f-4cea-933f-3994d9af9428

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/CoordinateMap.lean:L19-L42
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.coordinateMap_single. The node keeps its source
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
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap

-- ---- from OAI.Geometry.DoublingHilbert.CoordinateMap ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach
open DoublingHilbert

theorem coordinateMap_single {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (I : Finset ℕ) (v : I → B) (hv : ∀ i, ‖v i‖ ≤ 1) (j : ℕ) (a : ℝ) :
    ‖coordinateMap I v (lp.single 2 j a)‖ ≤ |a| := by
  classical
  change ‖∑ i : I, (lp.single 2 j a : RealL2) i • v i‖ ≤ |a|
  by_cases hj : j ∈ I
  · have he : (∑ i : I, (lp.single 2 j a : RealL2) i • v i) = a • v ⟨j, hj⟩ := by
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp [lp.single_apply]
      · intro i _ hi
        have hne : (i : ℕ) ≠ j := by
          intro heq
          exact hi (Subtype.ext heq)
        rw [lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 j a hne, zero_smul]
      · simp
    rw [he, norm_smul, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left (hv ⟨j, hj⟩) (abs_nonneg a)
  · have he : (∑ i : I, (lp.single 2 j a : RealL2) i • v i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hne : (i : ℕ) ≠ j := by rintro rfl; exact hj i.property
      rw [lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 j a hne, zero_smul]
    rw [he, norm_zero]
    exact abs_nonneg a

end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators
open DoublingHilbert


theorem solution : type_of% @_root_.OAI.CompactBanach.coordinateMap_single := @_root_.OAI.CompactBanach.coordinateMap_single
