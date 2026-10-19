-- Prove2me | solution 2 for OAI.FiniteTrails.exists_closed_trail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:16:32.707317+00:00
-- url     : https://prove2.me/submissions/cf3c2db2-2671-4418-9687-6c88b49b7a0c

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/FiniteTrails.lean:L84-L110
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteTrails.exists_closed_trail. The node keeps its source
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
import Theorems.Thm_OAI_FiniteTrails_exists_cycle_nonzero

-- ---- from OAI.Probability.CriticalZ3.FiniteTrails ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem successor_tail (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (d : D) : tail (successor tail head hbal d) = head d := by
  exact (Fintype.equivOfCardEq (hbal (head d)) ⟨d,rfl⟩).property

/-- A closed trail has distinct edges and retains the nonzero marked crossing sum. -/
theorem exists_closed_trail (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (w : D → ℤ) (hw : ∑ d, w d ≠ 0) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → D, Function.Injective e ∧
      (∀ i : Fin n, tail (e (next hn i)) = head (e i)) ∧ (∑ i, w (e i)) ≠ 0 := by
  let σ := successor tail head hbal
  obtain ⟨d,hd⟩ := exists_cycle_nonzero σ w hw
  let n := minimalPeriod σ d
  have hn : 0 < n := period_pos σ d
  let e : Fin n → D := fun i => σ^[i.val] d
  refine ⟨n,hn,e,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp hij
  · intro i
    have he : e (next hn i) = σ (e i) := by
      change σ^[(i.val+1)%n] d = σ (σ^[i.val] d)
      rw [iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']
    rw [he]
    exact successor_tail tail head hbal (e i)
  · have hs := (cycleEquiv σ d).sum_comp (fun z : {e // σ.SameCycle d e} => w z.val)
    have ht : (∑ z : {e // σ.SameCycle d e}, w z.val) =
        ∑ e : D, if σ.SameCycle d e then w e else 0 := by
      rw [←Finset.sum_filter]; exact (Finset.sum_subtype _ (by simp) w).symm
    rw [ht] at hs
    exact hs.symm ▸ hd

end FiniteTrails

end OAI

-- ---- platform node ----
open OAI OAI.FiniteTrails
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Classical Function


theorem solution.{uD,uV} : type_of% @_root_.OAI.FiniteTrails.exists_closed_trail.{uD,uV} := @_root_.OAI.FiniteTrails.exists_closed_trail.{uD,uV}
