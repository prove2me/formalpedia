-- Prove2me | solution 1 for OAI.SegmentLenses.SegmentFamily.tail_replacement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:42:36.657979+00:00
-- url     : https://prove2.me/submissions/9404d4ae-14c8-4441-9452-2a46ce0cc3e2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/GateRecovery.lean:L225-L252
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.SegmentFamily.tail_replacement. The node keeps its source
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

-- ---- from OAI.Analysis.SegmentLenses.TreeGeometry ----
namespace OAI

/-!
# Ancestry, segment splitting, and opposite crossings
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section TreeGeometry
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem head_zero_above {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {g v : V} (hg : g ∉ H) (hgv : g ≤ v) :
    p v = 0 := by
  have _ := decidableEqV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  apply Finsupp.notMem_support_iff.mp
  intro hv
  exact hg (hH (hp hv) hgv)

theorem gates_incomparable {H : Finset V} {g g' : V}
    (hg : Gate H g) (hg' : Gate H g') (h : g ≤ g') : g = g' := by
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  by_contra hne
  exact hg.1 (hg'.2 g (lt_of_le_of_ne h hne))

theorem gate_unique_in_interval {H : Finset V} {g g' a b : V}
    (hg : Gate H g) (hg' : Gate H g')
    (hm : g ∈ Finset.Icc a b) (hm' : g' ∈ Finset.Icc a b) : g = g' := by
  rcases TreeOrder.lower_chain (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hm').2 with h | h
  · exact gates_incomparable hg hg' h
  · exact (gates_incomparable hg' hg h).symm

namespace SegmentFamily

theorem gate_unique {H : Finset V} (F : SegmentFamily V) (S : F.sets)
    {g g' : V} (hg : Gate H g) (hg' : Gate H g') (hm : g ∈ S.val) (hm' : g' ∈ S.val) :
    g = g' := by
  rw [F.repr S] at hm hm'
  exact gate_unique_in_interval hg hg' hm hm'

end SegmentFamily

end TreeGeometry

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.GateRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
# Gate coefficients, cone recovery, and energy budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section ProjectionAlgebra
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

namespace SegmentFamily

end SegmentFamily

namespace Representation

end Representation
end ProjectionAlgebra

section GateTails
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace SegmentFamily

theorem member_unique (F : SegmentFamily V) {S T : F.sets} {v : V}
    (hS : v ∈ S.val) (hT : v ∈ T.val) : S = T := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  by_contra hn
  exact Finset.disjoint_left.mp
    (F.disjoint S.property T.property (fun he => hn (Subtype.ext he))) hS hT

theorem gateTail_of_mem (F : SegmentFamily V) (H : Finset V) (S : F.sets)
    {g : V} (hg : g ∈ S.val) : F.gateTail H g = S.val \ H := by
  classical
  have hex : ∃ T : F.sets, g ∈ T.val := ⟨S, hg⟩
  rw [gateTail, dite_eq_left hex]
  rw [F.member_unique (Classical.choose_spec hex) hg]

theorem exists_gate_of_crossing (F : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (S : F.sets) (hpS : (∑ v ∈ S.val, p v) ≠ 0)
    (hne : (S.val \ H).Nonempty) : ∃ g ∈ S.val, Gate H g := by
  classical
  have ha : F.first S ∈ H := by
    by_contra hn
    apply hpS
    apply Finset.sum_eq_zero
    intro v hv
    rw [F.repr S] at hv
    exact head_zero_above hH hp hn (Finset.mem_Icc.mp hv).1
  obtain ⟨g, hg, hmin⟩ := Finset.exists_minimal hne
  refine ⟨g, (Finset.mem_sdiff.mp hg).1, (Finset.mem_sdiff.mp hg).2, ?_⟩
  intro v hvg
  have hm : g ∈ Finset.Icc (F.first S) (F.last S) := by
    rw [← F.repr S]; exact (Finset.mem_sdiff.mp hg).1
  rcases TreeOrder.lower_chain hvg.le (Finset.mem_Icc.mp hm).1 with hle | hle
  · exact hH ha hle
  · by_contra hv
    have hvS : v ∈ S.val \ H := Finset.mem_sdiff.mpr ⟨by
      rw [F.repr S]
      exact Finset.mem_Icc.mpr ⟨hle, hvg.le.trans (Finset.mem_Icc.mp hm).2⟩, hv⟩
    exact not_le_of_gt hvg (hmin hvS hvg.le)

end SegmentFamily
end GateTails

section GateRecovery
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

namespace SegmentFamily

theorem boundary_tail_expansion (F : SegmentFamily V) (H : Finset V)
    (p : V →₀ ℝ) (g : V) :
    F.boundary p g • segmentFunctional (F.gateTail H g) =
      ∑ S : F.sets, if g ∈ S.val then (∑ v ∈ S.val, p v) •
        segmentFunctional (S.val \ H) else 0 := by
  classical
  rw [boundary, Finset.sum_smul, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hg : g ∈ S.val
  · simp only [hg, ite_true, F.gateTail_of_mem H S hg]
  · simp only [hg, ite_false, zero_smul]

theorem tail_replacement (F : SegmentFamily V) {H K : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (hK : ∀ S ∈ F.sets, S ⊆ K) :
    tail H (F.replacement p).value =
      ∑ g : K.filter (Gate H), F.boundary p g.val • segmentFunctional (F.gateTail H g.val) := by
  classical
  change tailLinear H (∑ S : F.sets, (∑ v ∈ S.val, p v) • segmentFunctional S.val) = _
  rw [map_sum]
  simp only [map_smul, tailLinear_apply, tail_segmentFunctional, F.boundary_tail_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hz : (∑ v ∈ S.val, p v) = 0
  · simp [hz]
  by_cases he : S.val \ H = ∅
  · simp [he, segmentFunctional]
  obtain ⟨g, hgS, hg⟩ := F.exists_gate_of_crossing hH p hp S hz (Finset.nonempty_iff_ne_empty.mpr he)
  have hgK : g ∈ K.filter (Gate H) := Finset.mem_filter.mpr ⟨hK S.val S.property hgS, hg⟩
  rw [Finset.sum_eq_single (⟨g, hgK⟩ : K.filter (Gate H))]
  · simp [hgS]
  · intro g' hg' hne
    have hn : g'.val ∉ S.val := by
      intro hm
      apply hne
      apply Subtype.ext
      exact F.gate_unique S (Finset.mem_filter.mp g'.property).2 hg hm hgS
    simp [hn]
  · simp

end SegmentFamily
end GateRecovery

section ScaledLaws
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace Representation

end Representation

end ScaledLaws

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses OAI.SegmentLenses.SegmentFamily
open scoped BigOperators
open Finset
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem solution (F : SegmentFamily V) {H K : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (hK : ∀ S ∈ F.sets, S ⊆ K) :
    tail H (F.replacement p).value =
      ∑ g : K.filter (Gate H), F.boundary p g.val • segmentFunctional (F.gateTail H g.val) := by
  first
    | exact OAI.SegmentLenses.SegmentFamily.tail_replacement F hH p hp hK
    | exact OAI.SegmentLenses.SegmentFamily.tail_replacement
    | (apply OAI.SegmentLenses.SegmentFamily.tail_replacement <;> assumption)
    | (intros; apply OAI.SegmentLenses.SegmentFamily.tail_replacement <;> assumption)
