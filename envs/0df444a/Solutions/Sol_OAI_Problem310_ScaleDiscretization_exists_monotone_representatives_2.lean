-- Prove2me | solution 2 for OAI.Problem310.ScaleDiscretization.exists_monotone_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:09:05.253812+00:00
-- url     : https://prove2.me/submissions/3603c63e-d17c-49bf-b14c-4b2aba519db3

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean:L30-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.ScaleDiscretization.exists_monotone_representatives. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- On a chain of integer vectors, the sum of the coordinates determines the vector. -/
lemma vector_eq_of_sum_eq {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    {s : Set α} {f : α → ι → ℤ} (hf : MonotoneOn f s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hs : (∑ i, f x i) = ∑ i, f y i) : f x = f y := by
  classical
  rcases le_total x y with hxy | hyx
  · funext i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hf hx hy hxy i)).mp hs i
      (Finset.mem_univ i)
  · funext i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hf hy hx hyx i)).mp hs.symm i
      (Finset.mem_univ i)).symm

/-- A monotone family of finitely many integer-valued functions has a small common
representative set. Unlike a breakpoint construction, this also handles every boundary
value without a separate endpoint convention. -/
theorem exists_monotone_representatives {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    (a b : α) (hab : a ≤ b) (f : α → ι → ℤ)
    (hf : MonotoneOn f (Set.Icc a b)) :
    ∃ R : Finset α,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ ((∑ i, f b i) + 1 - ∑ i, f a i).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R, f t' = f t := by
  classical
  let rank : α → ℤ := fun t => ∑ i, f t i
  let rep : ℤ → α := fun k =>
    if h : ∃ t, t ∈ Set.Icc a b ∧ rank t = k then Classical.choose h else a
  have rep_mem (k : ℤ) : rep k ∈ Set.Icc a b := by
    dsimp [rep]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact ⟨le_rfl, hab⟩
  have rep_rank {k : ℤ} (h : ∃ t, t ∈ Set.Icc a b ∧ rank t = k) :
      rank (rep k) = k := by
    dsimp [rep]
    rw [dite_eq_left h]
    exact (Classical.choose_spec h).2
  refine ⟨(Finset.Icc (rank a) (rank b)).image rep, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact rep_mem k
  · exact (Finset.card_image_le).trans_eq (Int.card_Icc _ _)
  · intro t ht
    have hlow : rank a ≤ rank t := by
      exact Finset.sum_le_sum fun i _ => hf ⟨le_rfl, hab⟩ ht ht.1 i
    have hhigh : rank t ≤ rank b := by
      exact Finset.sum_le_sum fun i _ => hf ht ⟨hab, le_rfl⟩ ht.2 i
    refine ⟨rep (rank t), Finset.mem_image.mpr ⟨rank t, ?_, rfl⟩, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hlow, hhigh⟩
    · exact vector_eq_of_sum_eq hf (rep_mem _) ht (rep_rank ⟨t, ht, rfl⟩)

end Problem310.ScaleDiscretization

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.ScaleDiscretization
open scoped BigOperators


theorem solution.{u_α,u_ι} : type_of% @_root_.OAI.Problem310.ScaleDiscretization.exists_monotone_representatives.{u_α,u_ι} := @_root_.OAI.Problem310.ScaleDiscretization.exists_monotone_representatives.{u_α,u_ι}
