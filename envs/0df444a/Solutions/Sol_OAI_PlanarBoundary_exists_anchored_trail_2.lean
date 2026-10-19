-- Prove2me | solution 2 for OAI.PlanarBoundary.exists_anchored_trail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:23:53.490776+00:00
-- url     : https://prove2.me/submissions/974f91e6-9aa0-4ace-9102-63c35fcc6e06

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean:L262-L290
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.exists_anchored_trail. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Theorems.Thm_OAI_FiniteTrails_exists_closed_trail
import Theorems.Thm_OAI_PlanarBoundary_balanced
import Theorems.Thm_OAI_PlanarBoundary_boundary_flux
import Theorems.Thm_OAI_PlanarBoundary_coordinate_diameter

-- ---- from OAI.Probability.CriticalZ3.PlanarBoundary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Oriented planar edge boundary with exact nearest-neighbor conventions. -/
open Classical
namespace PlanarBoundary
end PlanarBoundary

namespace PlanarBoundary
open Classical

theorem side_neighbor (cell : Point) (d : Direction) :
    Neighbor (cell+tailOffset d) (cell+headOffset d) := by
  refine ⟨d+1,?_⟩
  fin_cases d <;> ext <;> simp [headOffset,tailOffset,outward]

theorem head_neighbor {X : Finset Point} (e : Boundary X) : Neighbor (tail e) (head e) :=
  side_neighbor _ _

theorem rayFlux_eq_lineFlux {a b : Point} (h : Neighbor a b) :
    rayFlux a b = if 0 < a.1 then lineFlux a b else 0 := by
  obtain ⟨d,rfl⟩ := h
  rcases a with ⟨x,y⟩
  fin_cases d <;> simp [outward,rayFlux,lineFlux] <;> split_ifs <;> omega

theorem next_eq_rotate {n : ℕ} (hn : 0 < n) (i : Fin n) :
    FiniteTrails.next hn i = finRotate n i := by
  ext
  simp [FiniteTrails.next,finRotate_apply,Fin.add_def,Nat.add_mod_mod]

theorem lineFlux_sum_zero {n : ℕ} (hn : 0 < n) (v : Fin n → Point) :
    (∑ i, lineFlux (v i) (v (FiniteTrails.next hn i))) = 0 := by
  simp only [lineFlux,Finset.sum_sub_distrib,next_eq_rotate]
  exact sub_eq_zero.mpr (Equiv.sum_comp (finRotate n) (fun i => if 1 ≤ (v i).2 then (1 : ℤ) else 0))

/-- Nonzero positive-ray flux forces a crossing on each side of the vertical axis. -/
theorem two_sides {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i)))
    (hw : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) ≠ 0) :
    (∃ i, 0 < (v i).1 ∧ rayFlux (v i) (v (FiniteTrails.next hn i)) ≠ 0) ∧
      ∃ j, (v j).1 ≤ 0 := by
  constructor
  · obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    refine ⟨i,?_,hi⟩
    by_contra! hh
    exact hi (by rw [rayFlux_eq_lineFlux (hedge i),ite_eq_right (not_lt.mpr hh)])
  · by_contra! hh
    have he : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) = 0 := by
      simp_rw [rayFlux_eq_lineFlux (hedge _),ite_eq_left (hh _)]
      exact lineFlux_sum_zero hn v
    exact hw he

/-- Every finite region containing zero contains an edge-simple closed boundary
trail with a positive-ray anchor of coordinate less than 2n. This deliberately
uses a harmless overcount rather than an unformalized Jordan theorem. -/
theorem exists_anchored_trail (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧
      (∀ i, tail (e (FiniteTrails.next hn i)) = head (e i)) ∧
      ∃ i, 0 < (tail (e i)).1 ∧ (tail (e i)).1 < 2*(n : ℤ) ∧
        rayFlux (tail (e i)) (head (e i)) ≠ 0 := by
  have hw : (∑ e : Boundary X, rayFlux (tail e) (head e)) ≠ 0 := by
    rw [boundary_flux,ite_eq_left hX]
    norm_num
  obtain ⟨n,hn,e,he,hnext,hsum⟩ :=
    FiniteTrails.exists_closed_trail tail head (fun v => by
      simpa only [←Nat.card_eq_fintype_card] using balanced X v) (fun e => rayFlux (tail e) (head e)) hw
  let v : Fin n → Point := fun i => tail (e i)
  have hed : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i)) := by
    intro i
    dsimp [v]
    rw [hnext]
    exact head_neighbor _
  have hs : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) ≠ 0 := by
    simpa only [v,hnext] using hsum
  obtain ⟨⟨i,hi,hir⟩,j,hj⟩ := two_sides hn v hed hs
  have hd := coordinate_diameter hn v hed i j
  change (tail (e i)).1-(tail (e j)).1 < 2*(n : ℤ) at hd
  change (tail (e j)).1 ≤ 0 at hj
  refine ⟨n,hn,e,he,hnext,i,hi,by omega,?_⟩
  simpa only [v,hnext] using hir

end PlanarBoundary

namespace PlanarBoundary
open Classical

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical
open Classical


theorem solution : type_of% @_root_.OAI.PlanarBoundary.exists_anchored_trail := @_root_.OAI.PlanarBoundary.exists_anchored_trail
