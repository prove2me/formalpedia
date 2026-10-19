-- Prove2me | solution 2 for OAI.PlanarBoundary.exists_boundary_code
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:25:48.987395+00:00
-- url     : https://prove2.me/submissions/1dced0f4-581e-46ea-8e04-692ccc398c3c

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean:L369-L399
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.exists_boundary_code. The node keeps its source
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
import Theorems.Thm_OAI_PlanarBoundary_exists_anchored_trail

-- ---- from OAI.Probability.CriticalZ3.PlanarBoundary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

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

end PlanarBoundary

namespace PlanarBoundary
open Classical

theorem trace_succ {n : ℕ} (c : Code n) (k : ℕ) :
    tracePosition c (k+1) = tracePosition c k+displacement (wordAt c.2.2 k) := by
  simp only [tracePosition,Finset.sum_range_succ,add_assoc]

theorem trace_reconstruct {n : ℕ} (hn : 0 < n) {X : Finset Point}
    (e : Fin n → Boundary X) (he : ∀ i, tail (e (FiniteTrails.next hn i)) = head (e i))
    (c : Code n) (hanchor : anchor c = tail (e ⟨0,hn⟩))
    (hword : ∀ i, c.2.2 i = (e i).val.2) :
    ∀ i, traceSide c i = (e i).val := by
  have ht (k : ℕ) (hk : k < n) : tracePosition c k = tail (e ⟨k,hk⟩) := by
    induction k with
    | zero => simpa only [tracePosition,Finset.range_zero,Finset.sum_empty,add_zero] using hanchor
    | succ k ih =>
      have hkn : k < n := Nat.lt_trans (Nat.lt_succ_self _) hk
      rw [trace_succ,ih hkn]
      simp only [wordAt,dite_eq_left hkn,hword,displacement]
      have hx := he ⟨k,hkn⟩
      have hnxt : FiniteTrails.next hn ⟨k,hkn⟩ = (⟨k+1,hk⟩ : Fin n) := by
        ext
        exact Nat.mod_eq_of_lt hk
      rw [hnxt] at hx
      rw [hx]
      simp only [tail,head]
      abel
  intro i
  rw [traceSide,ht,hword]
  apply Prod.ext
  · exact add_sub_cancel_right _ _
  · rfl

theorem shiftIndex_injective {n : ℕ} (hn : 0 < n) (a : Fin n) :
    Function.Injective (shiftIndex hn a) := by
  intro i j he
  have h : (i+a : Fin n) = j+a := by
    apply Fin.ext
    exact congrArg Fin.val he
  exact add_right_cancel h

theorem shiftIndex_next {n : ℕ} (hn : 0 < n) (a i : Fin n) :
    shiftIndex hn a (FiniteTrails.next hn i) = FiniteTrails.next hn (shiftIndex hn a i) := by
  ext
  simp only [shiftIndex,FiniteTrails.next,Nat.mod_add_mod]
  congr 1
  omega

theorem rayFlux_ne_zero_height {a b : Point} (h : rayFlux a b ≠ 0) : a.2 = 0 ∨ a.2 = 1 := by
  unfold rayFlux at h
  split_ifs at h <;> aesop

/-- Every actual boundary supplies one of these finitely encoded trails. -/
theorem exists_boundary_code (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ _hn : 0 < n, ∃ c : Code n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧ ∀ i, traceSide c i = (e i).val := by
  obtain ⟨n,hn,e,he,hnext,a,ha0,haN,ha⟩ := exists_anchored_trail X hX
  let e' : Fin n → Boundary X := fun i => e (shiftIndex hn a i)
  have he' : Function.Injective e' := he.comp (shiftIndex_injective hn a)
  have hs' (i : Fin n) : tail (e' (FiniteTrails.next hn i)) = head (e' i) := by
    dsimp [e']
    rw [shiftIndex_next,hnext]
  have hz : e' ⟨0,hn⟩ = e a := by
    dsimp [e']
    congr 1
    apply Fin.ext
    simpa only [shiftIndex,Nat.zero_add] using Nat.mod_eq_of_lt a.isLt
  let x := (tail (e a)).1
  have hx0 : 0 ≤ x := le_of_lt ha0
  have hxn : x.toNat < 2*n := by omega
  obtain hy | hy := rayFlux_ne_zero_height ha
  · let c : Code n := (⟨x.toNat,hxn⟩,true,fun i => (e' i).val.2)
    refine ⟨n,hn,c,e',he',trace_reconstruct hn e' hs' c ?_ (fun _ => rfl)⟩
    rw [hz]
    apply Prod.ext
    · exact Int.toNat_of_nonneg hx0
    · exact hy.symm
  · let c : Code n := (⟨x.toNat,hxn⟩,false,fun i => (e' i).val.2)
    refine ⟨n,hn,c,e',he',trace_reconstruct hn e' hs' c ?_ (fun _ => rfl)⟩
    rw [hz]
    apply Prod.ext
    · exact Int.toNat_of_nonneg hx0
    · exact hy.symm

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical
open Classical


theorem solution : type_of% @_root_.OAI.PlanarBoundary.exists_boundary_code := @_root_.OAI.PlanarBoundary.exists_boundary_code
