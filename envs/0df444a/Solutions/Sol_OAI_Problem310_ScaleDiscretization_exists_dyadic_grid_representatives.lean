-- Prove2me | solution 1 for OAI.Problem310.ScaleDiscretization.exists_dyadic_grid_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:13:15.684861+00:00
-- url     : https://prove2.me/submissions/881db5c0-3f20-4c94-be54-7f38edf3d238

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean:L141-L163
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.ScaleDiscretization.exists_dyadic_grid_representatives. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_unit_affine_floor_representatives

-- ---- from OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- The padding bound controls the scale-parameter slope of each finest grid key. -/
lemma dyadic_grid_slope_le (B n L : ℕ) (h : B ≤ n + L) :
    (2 : ℝ) ^ B * ((2 : ℝ)⁻¹) ^ n ≤ (2 : ℝ) ^ L := by
  rw [inv_pow, ← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

/-- Simultaneous representatives for the finest dyadic grid keys in a family of
local routing tests. Only the padding inequalities are needed. -/
theorem exists_dyadic_grid_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊(2 : ℝ) ^ B i * (x + t' * ((2 : ℝ)⁻¹) ^ n i)⌋ =
          ⌊(2 : ℝ) ^ B i * (x + t * ((2 : ℝ)⁻¹) ^ n i)⌋ := by
  let u : ι → ℝ := fun i => (2 : ℝ) ^ B i * x
  let v : ι → ℝ := fun i => (2 : ℝ) ^ B i * ((2 : ℝ)⁻¹) ^ n i
  have hv (i : ι) : 0 ≤ v i := by dsimp [v]; positivity
  have hD (i : ι) : v i ≤ ((2 ^ L : ℕ) : ℝ) := by
    simpa [v] using dyadic_grid_slope_le (B i) (n i) L (hspan i)
  obtain ⟨R, hR, hcard, hrep⟩ :=
    exists_unit_affine_floor_representatives u v (2 ^ L) hv hD
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  refine ⟨t', ht', ?_⟩
  intro i
  convert heq i using 1 <;> congr 1 <;> dsimp [u, v] <;> ring

end Problem310.ScaleDiscretization

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.ScaleDiscretization
open scoped BigOperators


theorem solution.{u_ι} : type_of% @_root_.OAI.Problem310.ScaleDiscretization.exists_dyadic_grid_representatives.{u_ι} := @_root_.OAI.Problem310.ScaleDiscretization.exists_dyadic_grid_representatives.{u_ι}
