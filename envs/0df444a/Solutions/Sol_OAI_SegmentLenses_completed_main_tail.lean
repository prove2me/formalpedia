-- Prove2me | solution 1 for OAI.SegmentLenses.completed_main_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:51:13.411976+00:00
-- url     : https://prove2.me/submissions/a3ea5f40-5801-4533-823c-11b7de91e4cc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/Completed.lean:L87-L114
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.completed_main_tail. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
import Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_Completed
import Theorems.Thm_OAI_SegmentLenses_finite_main_tail

-- ---- from OAI.Analysis.SegmentLenses.TailBudget ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Signed-product recovery and the finite midpoint tail bound
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section SignedRecovery
open scoped Classical
variable {V Ω : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V] [Fintype Ω]

end SignedRecovery

section JointLawBound
open scoped Classical
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

end JointLawBound

section HeadSupport
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

theorem dual_ext_coordinates {x y : FullDual V}
    (h : ∀ v, x (unitVector v) = y (unitVector v)) : x = y := by
  apply dual_ext_test
  intro u
  simp only [dual_apply_test, h]

theorem head_eq_iff (H : Finset V) (x : FullDual V) :
    head H x = x ↔ ∀ v ∉ H, x (unitVector v) = 0 := by
  constructor
  · intro hx v hv
    rw [← hx, head_unitVector, ite_eq_right hv]
  · intro hx
    apply dual_ext_coordinates
    intro v
    rw [head_unitVector]
    by_cases hv : v ∈ H
    · simp [hv]
    · simp [hv, hx v hv]

theorem head_eq_of_subset {H K : Finset V} (hHK : H ⊆ K)
    (x : FullDual V) (hx : head H x = x) : head K x = x := by
  apply (head_eq_iff K x).mpr
  intro v hv
  exact (head_eq_iff H x).mp hx v (fun hvH => hv (hHK hvH))

end HeadSupport

section FiniteMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end FiniteMain

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.Completed ----
namespace OAI

/-!
# Completed midpoint bounds and coordinate density
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section FiniteAncestry
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrderBot V]

theorem subset_ancestralHull (S : Finset V) : S ⊆ ancestralHull S := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_Iic.mpr le_rfl⟩

theorem ancestralHull_ancestral (S : Finset V) : Ancestral (· ≤ ·) (ancestralHull S) := by
  intro v w hv hwv
  obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_Iic.mpr (hwv.trans (Finset.mem_Iic.mp hvb))⟩

end FiniteAncestry

section LocalizingTests
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

theorem head_pairing_of_support (K : Finset V) (y : FullDual V) (u : Test V)
    (hu : u.coeff.support ⊆ K) : head K y (u : Primal V) = y (u : Primal V) := by
  rw [head_pairing]
  have he : u.coeff.filter (· ∈ K) = u.coeff := by
    ext v
    by_cases hv : v ∈ K
    · simp [hv]
    · have hz : u.coeff v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hu h))
      simp [hv, hz]
  rw [he]
  rfl

theorem tail_head_pairing (H K : Finset V) (y : FullDual V) (u : Test V)
    (hu : u.coeff.support ⊆ K) : tail H (head K y) (u : Primal V) = tail H y (u : Primal V) := by
  rw [tail_pairing, tail_pairing]
  apply head_pairing_of_support
  change (u.coeff.filter (· ∉ H)).support ⊆ K
  rw [Finsupp.support_filter]
  exact (Finset.filter_subset _ _).trans hu

end LocalizingTests

section CompletedMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

theorem completed_main_tail {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x)
    (R : ℝ) (hR : 0 ≤ R) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) := by
  apply dual_norm_le _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  intro u
  let K := ancestralHull (H ∪ u.coeff.support)
  have hK : Ancestral (· ≤ ·) K := ancestralHull_ancestral _
  have hHK : H ⊆ K := Finset.subset_union_left.trans (subset_ancestralHull _)
  have huK : u.coeff.support ⊆ K := Finset.subset_union_right.trans (subset_ancestralHull _)
  have hxK := head_eq_of_subset hHK x hx
  have hpK : ‖x + head K y‖ ≤ R := by
    have he : x + head K y = head K (x + y) := by
      change x + headLinear K y = headLinear K (x + y)
      simp only [map_add, headLinear_apply, hxK]
    rw [he]
    exact (norm_head_le hK (x + y)).trans hp
  have hmK : ‖x - head K y‖ ≤ R := by
    have he : x - head K y = head K (x - y) := by
      change x - headLinear K y = headLinear K (x - y)
      simp only [map_sub, headLinear_apply, hxK]
    rw [he]
    exact (norm_head_le hK (x - y)).trans hm
  have hb := finite_main_tail hH hK hHK x (head K y) hx (head_head K y) R hR hpK hmK
  rw [← tail_head_pairing H K y u huK]
  have hop := (tail H (head K y)).le_opNorm (u : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at hop
  exact hop.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg u))

end CompletedMain

section CoordinateNorms
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end CoordinateNorms

section CoordinateDensity
variable {V : Type*} [DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

end CoordinateDensity

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

theorem solution {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x)
    (R : ℝ) (hR : 0 ≤ R) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) := by
  first
    | exact OAI.SegmentLenses.completed_main_tail hH x y hx R hR hp hm
    | exact OAI.SegmentLenses.completed_main_tail
    | (apply OAI.SegmentLenses.completed_main_tail <;> assumption)
    | (intros; apply OAI.SegmentLenses.completed_main_tail <;> assumption)
