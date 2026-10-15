-- Prove2me | solution 1 for OAI.SegmentLenses.Representation.gate_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:34:44.618129+00:00
-- url     : https://prove2.me/submissions/7f03cca5-0929-4786-ade9-3d79fa528012

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/LawRecovery.lean:L263-L302
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.Representation.gate_energy_le. The node keeps its source
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

-- ---- from OAI.Analysis.SegmentLenses.LawRecovery ----
namespace OAI

/-!
# Exact finite-law recovery and coefficient representations
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

section LawRecovery
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end LawRecovery

namespace FiniteLaw
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end FiniteLaw

section RepresentationGates
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem Representation.apply_of_mem (A : Representation V) (S : A.family.sets)
    {g : V} (hg : g ∈ S.val) : A.value (unitVector g) = A.coeff S := by
  rw [A.apply_unitVector, Finset.sum_eq_single S]
  · simp [hg]
  · intro T hT hne
    have hn : g ∉ T.val := fun ht => Finset.disjoint_left.mp
      (A.family.disjoint T.property S.property (fun he => hne (Subtype.ext he))) ht hg
    simp [hn]
  · simp

theorem Representation.apply_nonzero (A : Representation V) {g : V}
    (hg : A.value (unitVector g) ≠ 0) : ∃ S : A.family.sets, g ∈ S.val := by
  rw [A.apply_unitVector] at hg
  by_contra h
  apply hg
  apply Finset.sum_eq_zero
  intro S hS
  have hn : g ∉ S.val := fun hS => h ⟨S, hS⟩
  simp [hn]

theorem Representation.gate_energy_le (A : Representation V) {H : Finset V}
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g) :
    (∑ g : G, A.value (unitVector g.val) ^ 2) ≤ A.energy := by
  classical
  let active : G → Prop := fun g => A.value (unitVector g.val) ≠ 0
  let Γ := {g : G // active g}
  have hS : ∀ g : Γ, ∃ S : A.family.sets, g.val.val ∈ S.val :=
    fun g => A.apply_nonzero g.property
  let select : Γ → A.family.sets := fun g => Classical.choose (hS g)
  have hmem : ∀ g : Γ, g.val.val ∈ (select g).val := fun g => Classical.choose_spec (hS g)
  have hinj : Function.Injective select := by
    intro g g' he
    apply Subtype.ext
    apply Subtype.ext
    have hm' := hmem g'
    rw [← he] at hm'
    exact A.family.gate_unique (select g) (hG _ g.val.property) (hG _ g'.val.property)
      (hmem g) hm'
  have hsum : (∑ g : G, A.value (unitVector g.val) ^ 2) =
      ∑ g : Γ, A.coeff (select g) ^ 2 := by
    have he : (∑ g : G, A.value (unitVector g.val) ^ 2) =
        ∑ g : G, if active g then A.value (unitVector g.val) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      by_cases hne : active g
      · simp [hne]
      · have hz : A.value (unitVector g.val) = 0 := not_ne_iff.mp hne
        simp [hne, hz]
    rw [he, ← Finset.sum_filter,
      Finset.sum_subtype (p := active) _ (fun g => by simp)]
    apply Finset.sum_congr rfl
    intro g hg
    rw [A.apply_of_mem (select g) (hmem g)]
  rw [hsum]
  calc
    (∑ g : Γ, A.coeff (select g) ^ 2) =
      ∑ S ∈ Finset.univ.image select, A.coeff S ^ 2 := (Finset.sum_image (s := Finset.univ) (g := select)
        (f := fun S => A.coeff S ^ 2) hinj.injOn).symm
    _ ≤ ∑ S, A.coeff S ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)

end RepresentationGates

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem solution (A : Representation V) {H : Finset V}
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g) :
    (∑ g : G, A.value (unitVector g.val) ^ 2) ≤ A.energy := by
  first
    | exact OAI.SegmentLenses.Representation.gate_energy_le A G hG
    | exact OAI.SegmentLenses.Representation.gate_energy_le
    | (apply OAI.SegmentLenses.Representation.gate_energy_le <;> assumption)
    | (intros; apply OAI.SegmentLenses.Representation.gate_energy_le <;> assumption)
