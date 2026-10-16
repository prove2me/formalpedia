-- Prove2me | solution 2 for OAI.Problem310.ScaleDiscretization.exists_affine_floor_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:10:23.276715+00:00
-- url     : https://prove2.me/submissions/5484436b-e6a4-4efd-b1ac-423cfacd3387

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean:L79-L107
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.ScaleDiscretization.exists_affine_floor_representatives. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_monotone_representatives

-- ---- from OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- An integer floor can increase by at most the ceiling of the displacement. -/
lemma floor_sub_floor_le_ceil (x y : ℝ) : ⌊y⌋ - ⌊x⌋ ≤ ⌈y - x⌉ := by
  have hy := Int.floor_le y
  have hx := Int.lt_floor_add_one x
  have hc := Int.le_ceil (y - x)
  have h : ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) < (⌈y - x⌉ : ℝ) + 1 := by
    push_cast
    linarith
  have hi : ⌊y⌋ - ⌊x⌋ < ⌈y - x⌉ + 1 := by exact_mod_cast h
  omega

/-- Simultaneous floor keys on an affine path admit at most one plus the sum of
their (rounded-up) displacements many representatives. -/
theorem exists_affine_floor_representatives {ι : Type u_ι} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (u v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ (1 + ∑ i, ⌈v i * (b - a)⌉).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by
  classical
  let f : ℝ → ι → ℤ := fun t i => ⌊u i + v i * t⌋
  have hf : MonotoneOn f (Set.Icc a b) := by
    intro x hx y hy hxy i
    apply Int.floor_le_floor
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (hv i))
  obtain ⟨R, hR, hcard, hrep⟩ := exists_monotone_representatives a b hab f hf
  refine ⟨R, hR, hcard.trans ?_, ?_⟩
  · apply Int.toNat_le_toNat
    have hi (i : ι) : f b i - f a i ≤ ⌈v i * (b - a)⌉ := by
      have h := floor_sub_floor_le_ceil (u i + v i * a) (u i + v i * b)
      convert h using 1
      congr 1
      ring
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_sub_distrib] at hs
    linarith
  · intro t ht
    obtain ⟨t', ht', heq⟩ := hrep t ht
    exact ⟨t', ht', fun i => congrFun heq i⟩

end Problem310.ScaleDiscretization

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.ScaleDiscretization
open scoped BigOperators


theorem solution.{u_ι} : type_of% @_root_.OAI.Problem310.ScaleDiscretization.exists_affine_floor_representatives.{u_ι} := @_root_.OAI.Problem310.ScaleDiscretization.exists_affine_floor_representatives.{u_ι}
