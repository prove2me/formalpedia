-- Prove2me | solution 1 for OAI.Problem310.WindowLocalFactor.exists_uniform_window_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:16:38.99307+00:00
-- url     : https://prove2.me/submissions/615933f0-dec6-45ec-ab43-a3ce36dd677f

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowLocalFactor.lean:L15-L44
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowLocalFactor.exists_uniform_window_representatives. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_dyadic_grid_representatives
import Theorems.Thm_OAI_Problem310_ScaleDiscretization_periodic_floor_eq_of_floor_eq

-- ---- from OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- Periodic versions of all finest keys agree at one of the same representatives. -/
theorem exists_periodic_dyadic_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊(2 : ℝ) ^ B i * Int.fract (x + t' * ((2 : ℝ)⁻¹) ^ n i)⌋ =
          ⌊(2 : ℝ) ^ B i * Int.fract (x + t * ((2 : ℝ)⁻¹) ^ n i)⌋ := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_dyadic_grid_representatives x B n L hspan
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  exact ⟨t', ht', fun i => periodic_floor_eq_of_floor_eq (B i) (heq i)⟩

/-- Deterministic representatives simultaneously work for every assignment of local
predicates that factors through the indicated periodic keys. In particular the
representatives do not depend on the random selector or terminal tables. -/
theorem exists_local_predicate_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : ι → ℝ → Bool,
          (∀ i y z, ⌊(2 : ℝ) ^ B i * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ B i * Int.fract z⌋ → Q i y = Q i z) →
          ∀ i, Q i (x + t' * ((2 : ℝ)⁻¹) ^ n i) =
            Q i (x + t * ((2 : ℝ)⁻¹) ^ n i) := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_periodic_dyadic_representatives x B n L hspan
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  exact ⟨t', ht', fun Q hQ i => hQ i _ _ (heq i)⟩

end Problem310.ScaleDiscretization

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowLocalFactor ----
namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.WindowLocalFactor

-- [generator] trimmed: open RoutingPath GridSeparation LocalPredicateFactor
open RoutingPath GridSeparation

/-- Padded equal-length child windows provide a common representative set for
all outcomes and all local predicates factoring through their subtree grids.
The representatives are selected before the outcome or predicates. -/
theorem exists_uniform_window_representatives {Ω : Type u_Ω} (M r : ℕ)
    (a B : Fin M → ℕ) (hpadding : ∀ i, B i + 1 ≤ a i + 2 * r)
    (x : ℝ) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * r * 2 ^ (2 * r + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : Ω → Fin M → ℝ → Bool,
          (∀ ω i y z, ⌊(2 : ℝ) ^ (B i + 2) * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ (B i + 2) * Int.fract z⌋ → Q ω i y = Q ω i z) →
          ∀ ω (i : Fin M) (j : Fin r),
            Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (a i + j.val)) =
              Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (a i + j.val)) := by
  have hspan (ij : Fin M × Fin r) : B ij.1 + 2 ≤
      (a ij.1 + ij.2.val) + (2 * r + 2) := by
    have h := hpadding ij.1
    omega
  obtain ⟨R, hR, hcard, hrep⟩ := ScaleDiscretization.exists_local_predicate_representatives
    x (fun ij : Fin M × Fin r => B ij.1 + 2)
    (fun ij : Fin M × Fin r => a ij.1 + ij.2.val) (2 * r + 2) hspan
  refine ⟨R, hR, ?_, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hcard
  · intro t ht
    obtain ⟨t', ht', hsame⟩ := hrep t ht
    refine ⟨t', ht', ?_⟩
    intro Q hQ ω i j
    exact hsame (fun ij z => Q ω ij.1 z) (fun ij y z h => hQ ω ij.1 y z h) (i, j)

end Problem310.WindowLocalFactor

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowLocalFactor
open RoutingPath GridSeparation


theorem solution.{u_Ω} : type_of% @_root_.OAI.Problem310.WindowLocalFactor.exists_uniform_window_representatives.{u_Ω} := @_root_.OAI.Problem310.WindowLocalFactor.exists_uniform_window_representatives.{u_Ω}
