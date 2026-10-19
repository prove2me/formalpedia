-- Prove2me | solution 1 for OAI.LatticeRelay.thirteen_interfaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:11:14.78073+00:00
-- url     : https://prove2.me/submissions/7dbc8800-4630-45f6-8d13-5e5320567435

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Relay.lean:L241-L274
-- (upload_full_project.md Phase 4): solution for node OAI.LatticeRelay.thirteen_interfaces. The node keeps its source
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
import Theorems.Thm_OAI_LatticeRelay_contraction_face
import Theorems.Thm_OAI_LatticeRelay_translation_face

-- ---- from OAI.Probability.CriticalZ3.Relay ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace LatticeRelay
open Set
theorem contraction_cube {r a : ℤ} (_hr : 0 ≤ r) (ha : 0 ≤ a)
    (ha' : 6*r+a < 10*r) (h : Fin 3) {u : Vertex}
    (hu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a) :
    Cube u (2*r) ⊆ Prism r := by
  intro x hx
  have hu' (i : Fin 3) : |u i| ≤ 4*r+a := by
    have hu' := hu i
    split_ifs at hu' <;> omega
  have hxi (i : Fin 3) : |x i| < 10*r := by
    have hxu := hx i
    change |x i-u i| ≤ 2*r at hxu
    have huu := hu' i
    rw [abs_le] at hxu huu
    rw [abs_lt]
    omega
  have h0 := (abs_lt.mp (hxi 0))
  refine ⟨by omega,by omega,?_⟩
  intro i _
  exact (hxi i).le

theorem translation_cube {r R a s w : ℤ}
    (_hR : 0 < R) (hr : 100*(R+1) < r)
    (ha0 : 0 ≤ a) (ha : a ≤ 18*r) (hw : w ≤ 2*r+13*R) (hs : s ≤ 2*r+1)
    {u : Vertex} (hu : u ∈ Cube (axisCenter a) w) :
    Cube u s ⊆ Prism r := by
  intro x hx
  have bounds (i : Fin 3) : -(w+s) ≤ x i-axisCenter a i ∧
      x i-axisCenter a i ≤ w+s := by
    have hu' := (abs_le.mp (hu i))
    have hx' := (abs_le.mp (hx i))
    dsimp at hu' hx'
    omega
  have h0 := bounds 0
  simp only [axisCenter,ite_true] at h0
  refine ⟨by omega,by omega,?_⟩
  intro i hi
  have h := bounds i
  simp only [axisCenter,hi,ite_false,sub_zero] at h
  rw [abs_le]
  constructor <;> omega

theorem contraction_interface {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {t : ℕ} (ht : t < 3) :
    HasInterface r R 0 (contractionWidths r R t)
      (Rect 0 (contractionWidths r R (t+1))) := by
  intro u hu
  let h : Fin 3 := ⟨t,ht⟩
  let a : ℤ := (t+1)*R
  have ht' : (t : ℤ) < 3 := by exact_mod_cast ht
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha3 : a ≤ 3*R := by dsimp [a]; nlinarith
  have huu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a := by
    intro i
    have hh := hu i
    change |u i-0| ≤ (if i.val < t then 2*r+(t : ℤ)*R else 4*r+(t : ℤ)*R)+R at hh
    change |u i| ≤ if i.val < t then 2*r+a else 4*r+a
    dsimp [a]
    rw [add_mul]
    by_cases hi : i.val < t <;> simp only [hi,ite_true,ite_false,sub_zero,one_mul] at * <;> omega
  refine ⟨2*r,by simp,contraction_cube (by omega) ha0 (by omega) h huu,h,inward u,?_⟩
  intro x hx i
  have hb := contraction_face (by omega) ha0 h huu hx i
  change |x i-0| ≤ if i.val < t+1 then 2*r+(↑(t+1) : ℤ)*R else 4*r+(↑(t+1) : ℤ)*R
  have hi : (i ≤ h) ↔ i.val < t+1 := by change (i.val ≤ t) ↔ _; omega
  simpa only [hi,a,Nat.cast_add,Nat.cast_one,Pi.zero_apply] using hb

theorem translation_interface {r R a s w : ℤ}
    (hR : 0 < R) (hr : 100*(R+1) < r)
    (ha0 : 0 ≤ a) (ha : a ≤ 18*r) (hw : w ≤ 2*r+13*R)
    (hs : s = 2*r ∨ s = 2*r+1) (hsw : s ≤ w) :
    HasInterface r R (axisCenter a) (fun _ => w-R) (Cube (axisCenter (a+s)) w) := by
  intro u hu
  have huu : u ∈ Cube (axisCenter a) w := by
    intro i
    simpa only [Expand,Rect,sub_add_cancel] using hu i
  refine ⟨s,?_,translation_cube hR hr ha0 ha hw (by rcases hs with rfl|rfl <;> omega) huu,
    0,forwardInward u,translation_face hsw huu⟩
  rcases hs with rfl|rfl <;> simp

theorem routeCenter_translation {r : ℤ} {i : ℕ} (hi : 3 ≤ i) (hi' : i ≤ 12) :
    routeCenter r i = axisCenter (2*r*(i-3 : ℕ)) := by
  by_cases h : i ≤ 3
  · have : i = 3 := by omega
    subst i
    simp [routeCenter]
  · simp [routeCenter,h,hi']

theorem routeWidths_translation {r R : ℤ} {i : ℕ} (hi : 3 ≤ i) :
    routeWidths r R i = fun _ => 2*r+(i : ℤ)*R := by
  by_cases h : i ≤ 3
  · have : i = 3 := by omega
    subst i
    funext j
    simp [routeWidths,contractionWidths,j.isLt]
  · simp [routeWidths,h]

theorem routeCenter_next {r : ℤ} {i : ℕ} (hi : 3 ≤ i) (hi' : i ≤ 12) :
    routeCenter r (i+1) = axisCenter (2*r*(i-3 : ℕ)+stepSize r i) := by
  by_cases h : i < 12
  · rw [routeCenter_translation (by omega) (by omega)]
    congr 1
    simp only [stepSize,h,ite_true,Nat.cast_sub (by omega : 3 ≤ i),
      Nat.cast_sub (by omega : 3 ≤ i+1),Nat.cast_add,Nat.cast_one]
    ring
  · have : i = 12 := by omega
    subst i
    simp only [routeCenter,show ¬13 ≤ 3 by omega,ite_false,show ¬13 ≤ 12 by omega,
      stepSize,lt_self_iff_false]
    congr 1
    norm_num
    ring

theorem thirteen_interfaces {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {i : ℕ} (hi : i < 13) :
    HasInterface r R (routeCenter r i) (routeWidths r R i) (P r R (i+1)) := by
  by_cases hi3 : i < 3
  · simpa only [P,routeCenter,routeWidths,show i ≤ 3 by omega,show i+1 ≤ 3 by omega,
      ite_true] using contraction_interface hR hr hi3
  · have hil : 3 ≤ i := by omega
    have hii : i ≤ 12 := by omega
    rw [routeCenter_translation hil hii,routeWidths_translation hil]
    unfold P
    rw [routeCenter_next hil hii,routeWidths_translation (by omega)]
    let a : ℤ := 2*r*(i-3 : ℕ)
    let w : ℤ := 2*r+(↑(i+1) : ℤ)*R
    have hir : (i : ℤ) ≤ 12 := by exact_mod_cast hii
    have hilr : (3 : ℤ) ≤ i := by exact_mod_cast hil
    have hr0 : 0 ≤ r := by omega
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha : a ≤ 18*r := by
      dsimp [a]
      rw [Nat.cast_sub hil]
      norm_num
      nlinarith
    have hw : w ≤ 2*r+13*R := by dsimp [w]; nlinarith
    have hs : stepSize r i = 2*r ∨ stepSize r i = 2*r+1 := by
      unfold stepSize; split_ifs <;> simp
    have hsw : stepSize r i ≤ w := by
      dsimp [w]
      rcases hs with h|h <;> rw [h] <;> nlinarith
    have he : (fun _ : Fin 3 => 2*r+(i : ℤ)*R) = fun _ => w-R := by
      funext j
      dsimp [w]
      ring
    rw [he]
    exact translation_interface hR hr ha0 ha hw hs hsw

end LatticeRelay

end OAI

-- ---- platform node ----
open OAI OAI.LatticeRelay
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Set


theorem solution : type_of% @_root_.OAI.LatticeRelay.thirteen_interfaces := @_root_.OAI.LatticeRelay.thirteen_interfaces
