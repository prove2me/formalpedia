-- Prove2me | solution 1 for OAI.Problem310.ScaleDiscretization.exists_unit_affine_floor_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:11:54.843599+00:00
-- url     : https://prove2.me/submissions/b8af7f4e-38bf-476e-859e-2da34039fd29

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean:L109-L131
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.ScaleDiscretization.exists_unit_affine_floor_representatives. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_affine_floor_representatives

-- ---- from OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- A uniform displacement bound gives a particularly convenient natural-valued
cardinality estimate for the normalized scale interval. -/
theorem exists_unit_affine_floor_representatives {ι : Type u_ι} [Fintype ι]
    (u v : ι → ℝ) (D : ℕ) (hv : ∀ i, 0 ≤ v i) (hD : ∀ i, v i ≤ (D : ℝ)) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * D ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by
  classical
  obtain ⟨R, hR, hcard, hrep⟩ :=
    exists_affine_floor_representatives 1 2 (by norm_num) u v hv
  refine ⟨R, hR, hcard.trans ?_, hrep⟩
  have hi (i : ι) : ⌈v i * (2 - 1)⌉ ≤ (D : ℤ) := by
    apply Int.ceil_le.mpr
    norm_num
    exact hD i
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hsum : 1 + ∑ i, ⌈v i * (2 - 1)⌉ ≤ (1 + Fintype.card ι * D : ℕ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    push_cast
    linarith
  exact (Int.toNat_le_toNat hsum).trans_eq (Int.toNat_natCast _)

end Problem310.ScaleDiscretization

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.ScaleDiscretization
open scoped BigOperators


theorem solution.{u_ι} : type_of% @_root_.OAI.Problem310.ScaleDiscretization.exists_unit_affine_floor_representatives.{u_ι} := @_root_.OAI.Problem310.ScaleDiscretization.exists_unit_affine_floor_representatives.{u_ι}
