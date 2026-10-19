-- Prove2me | solution 2 for OAI.FiniteTrails.exists_cycle_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:14:55.884639+00:00
-- url     : https://prove2.me/submissions/1b6c2f71-5ffd-4d1f-9ea6-6e973a2dfaa4

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/FiniteTrails.lean:L32-L57
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteTrails.exists_cycle_nonzero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails

-- ---- from OAI.Probability.CriticalZ3.FiniteTrails ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uD uV

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

/-! Finite balanced directed boundaries admit closed edge-simple trails.
This is used only for the planar contour dependency of the main proof. -/
open Classical Function
namespace FiniteTrails
variable {D : Type uD} {V : Type uV} [Fintype D]

/-- Some cycle class has nonzero weight whenever the total weight does. -/
theorem exists_cycle_nonzero (σ : Equiv.Perm D) (w : D → ℤ)
    (hw : ∑ d, w d ≠ 0) :
    ∃ d, (∑ e : D, if σ.SameCycle d e then w e else 0) ≠ 0 := by
  let Q := Quotient (Equiv.Perm.SameCycle.setoid σ)
  let q : D → Q := Quotient.mk _
  have hs : ∑ c : Q, (∑ e : D, if q e = c then w e else 0) = ∑ e, w e := by
    calc
      _ = ∑ e : D, ∑ c : Q, if q e = c then w e else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        exact (Finset.sum_ite_eq Finset.univ (q e) (fun _ => w e)).trans (ite_eq_left (Finset.mem_univ _))
  by_contra! h
  have hz : (∑ c : Q, ∑ e : D, if q e = c then w e else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    obtain ⟨d,rfl⟩ := Quotient.exists_rep c
    convert h d using 1
    apply Finset.sum_congr rfl
    intro e _
    have he : q e = Quotient.mk (Equiv.Perm.SameCycle.setoid σ) d ↔ σ.SameCycle d e := by
      rw [Quotient.eq]
      exact Equiv.Perm.sameCycle_comm
    simp only [he]
  exact hw (hs.symm.trans hz)

end FiniteTrails

end OAI

-- ---- platform node ----
open OAI OAI.FiniteTrails
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Classical Function


theorem solution.{uD} : type_of% @_root_.OAI.FiniteTrails.exists_cycle_nonzero.{uD} := @_root_.OAI.FiniteTrails.exists_cycle_nonzero.{uD}
