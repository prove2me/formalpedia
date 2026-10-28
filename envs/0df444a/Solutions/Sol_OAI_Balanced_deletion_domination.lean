-- Prove2me | solution 1 for OAI.Balanced.deletion_domination
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:26:48.856902+00:00
-- url     : https://prove2.me/submissions/ff49221c-7be8-4ee8-a374-4098f4272571

import Mathlib
import Definitions.Def_BalancedRyser
import Definitions.Def_OAIQ63Br004
import Theorems.Thm_OAI_Balanced_Selection_Process_exists_uniformConcentratedPath_estimate
import Theorems.Thm_OAI_Balanced_Selection_Process_selectionStatement_of_uniform_concentration_occupancy
import Theorems.Thm_OAI_Balanced_candidateGraph_proof

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateSelectionBridge
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem subtype_card_of_subset {α : Type*} [DecidableEq α]
    (s t : Finset α) (h : s ⊆ t) :
    (s.subtype (fun x => x ∈ t)).card = s.card := by
  rw [Finset.card_subtype]
  rw [Finset.filter_eq_self.mpr h]

private theorem subtype_inter {α : Type*} [DecidableEq α]
    (s t U : Finset α) :
    s.subtype (fun x => x ∈ U) ∩ t.subtype (fun x => x ∈ U) =
      (s ∩ t).subtype (fun x => x ∈ U) := by
  ext x
  simp

theorem candidateSelection_slot_eq (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (s : Slot F) :
    Selection.slotVertices (candidateSelectionInput M J) s =
      (candidateSlot M s).subtype (fun w => w ∈ candidateVertices M) := by
  ext v
  simp only [Selection.slotVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [candidateSelectionInput, candidateSlot, v.property]

theorem candidateSelection_neighbors_eq (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (v : AvailableCandidate M) :
    Selection.neighbors (candidateSelectionInput M J) v =
      (candidateNeighbors M v.val).subtype (fun w => w ∈ candidateVertices M) := by
  ext w
  simp only [Selection.neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [candidateSelectionInput, actualCandidateGraph,
    candidateNeighbors, w.property]

theorem candidateSelection_slot_card (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (s : Slot F) :
    (Selection.slotVertices (candidateSelectionInput M J) s).card =
      (candidateSlot M s).card := by
  rw [candidateSelection_slot_eq]
  exact subtype_card_of_subset _ _ (Finset.filter_subset _ _)

theorem candidateSelection_neighbors_card (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (v : AvailableCandidate M) :
    (Selection.neighbors (candidateSelectionInput M J) v).card =
      (candidateNeighbors M v.val).card := by
  rw [candidateSelection_neighbors_eq]
  exact subtype_card_of_subset _ _ (Finset.filter_subset _ _)

theorem candidateSelection_neighbor_slot_card (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (v : AvailableCandidate M) (s : Slot F) :
    ((Selection.neighbors (candidateSelectionInput M J) v) ∩
      Selection.slotVertices (candidateSelectionInput M J) s).card =
      ((candidateNeighbors M v.val) ∩ candidateSlot M s).card := by
  rw [candidateSelection_neighbors_eq, candidateSelection_slot_eq, subtype_inter]
  apply subtype_card_of_subset
  exact Finset.Subset.trans Finset.inter_subset_left (Finset.filter_subset _ _)

theorem candidateSelection_common_neighbors_card (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (v w : AvailableCandidate M) :
    ((Selection.neighbors (candidateSelectionInput M J) v) ∩
      Selection.neighbors (candidateSelectionInput M J) w).card =
      ((candidateNeighbors M v.val) ∩ candidateNeighbors M w.val).card := by
  rw [candidateSelection_neighbors_eq, candidateSelection_neighbors_eq, subtype_inter]
  apply subtype_card_of_subset
  exact Finset.Subset.trans Finset.inter_subset_left (Finset.filter_subset _ _)

theorem candidateGraphGood_selection {M : MergedPairs F} {c C : ℝ}
    (hgood : CandidateGraphGood M c C) :
    ∃ J : AvailableCandidate M → Finset (CandidateVertex F),
      Selection.GraphBounds (candidateSelectionInput M J) (Fintype.card F) c C := by
  rcases hgood with ⟨hslots, hvertices, hexceptions, _hmult, _hoccup⟩
  choose J hJ using (fun v : AvailableCandidate M => hexceptions v.val v.property)
  refine ⟨J, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Slot, Direction, Fintype.card_prod, Nat.mul_comm]
  · intro v w hslot hadj
    exact hadj.2.2.1 hslot
  · intro i
    rw [candidateSelection_slot_card]
    exact hslots i
  · intro v
    rw [candidateSelection_neighbors_card]
    exact (hvertices v.val v.property).1
  · intro v i
    have hc := candidateSelection_neighbor_slot_card M J v i
    have h := (hvertices v.val v.property).2 i
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp
  · intro v
    change (((J v).subtype (fun w => w ∈ candidateVertices M)).card : ℝ) ≤ _
    rw [subtype_card_of_subset _ _ (hJ v).1]
    exact (hJ v).2.1
  · intro v w hw
    have hw' : w.val ∉ J v := by
      simpa [candidateSelectionInput] using hw
    have h := (hJ v).2.2.2 w.val w.property hw'
    have hc := candidateSelection_common_neighbors_card M J v w
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp
  · intro v w hw
    have hw' : w.val ∈ J v := by
      simpa [candidateSelectionInput] using hw
    rcases (hJ v).2.2.1 w.val hw' with h | h
    · exact Or.inl h
    · exact Or.inr h.symm

theorem candidateSelection_lineAssignment (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) :
    Selection.LineAssignment (candidateSelectionInput M J) (coordinatePlane F)
      (Equiv.refl (Slot F)) (fun v : AvailableCandidate M => candidateLine v.val) := by
  constructor
  · intro v
    rfl
  · intro v w hslot hline
    apply Subtype.ext
    apply Prod.ext
    · exact hslot
    · exact congrArg (fun l : Line F => l.2) hline

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

lemma initial_subset_line (l : Line F) : initial C l ⊆ linePoints l := by
  unfold initial
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

end
end Balanced.SelectionOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_SelectionAffineAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

namespace SelectionOccupancy

variable {F} (C : Configuration F)

theorem initial_trackedSets {c₀ : ℝ}
    (hsize : ∀ l, c₀ * Fintype.card F ≤ ((initial C l).card : ℝ)) :
    Selection.TrackedSets (coordinatePlane F) (initial C) c₀ := by
  intro l
  exact ⟨by simpa only [coordinatePlane_linePoints] using initial_subset_line C l, hsize l⟩

theorem candidate_good_trackedSets {c Cbound : ℝ}
    (hgood : CandidateGraphGood C.merged c Cbound) :
    Selection.TrackedSets (coordinatePlane F) (initial C) (1 / 5) :=
  initial_trackedSets C (candidate_good_initial C hgood).2

end SelectionOccupancy
end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateOccupancyBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem candidateSelection_trackedSets {M : MergedPairs F} {c C : ℝ}
    (hgood : CandidateGraphGood M c C) :
    Selection.TrackedSets (coordinatePlane F) (candidateTrackedSets M) (1 / 5) := by
  exact SelectionOccupancy.candidate_good_trackedSets
    (selectedConfiguration M (fun _ => 0)) hgood

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_Hypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartiteHypergraph

variable {r n : ℕ}

@[simp] theorem covers_empty_iff (H : PartiteHypergraph r n) :
    H.Covers ∅ ↔ H.edges = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases h e he with ⟨i, hi⟩
    exact Finset.notMem_empty _ hi
  · intro h e he
    simp [h] at he

end Balanced.PartiteHypergraph

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced
namespace DeletionAssignments

theorem card_three_assignments {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.card = 3) :
    Fintype.card (Fin 3 ≃ s) = 6 := by
  classical
  let e : Fin 3 ≃ s :=
    (Fintype.equivFinOfCardEq (by simpa using hs : Fintype.card s = 3)).symm
  rw [Fintype.card_equiv e]
  norm_num

theorem card_direction_assignments {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (D : ι → Finset α) (hD : ∀ i, (D i).card = 3) :
    Fintype.card (∀ i, Fin 3 ≃ D i) = 6 ^ Fintype.card ι := by
  classical
  rw [Fintype.card_pi]
  simp_rw [card_three_assignments _ (hD _)]
  simp

theorem exists_assignment_of_image {α : Type*} [DecidableEq α]
    (s : Finset α) (f : Fin 3 → α) (hf : Function.Injective f)
    (hs : Finset.univ.image f = s) :
    ∃ e : Fin 3 ≃ s, ∀ j, (e j).val = f j := by
  let g : Fin 3 → s := fun j => ⟨f j, by rw [← hs]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro j k h
      exact hf (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ Finset.univ.image f := by rw [hs]; exact x.property
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      exact ⟨j, Subtype.ext hj⟩
  exact ⟨Equiv.ofBijective g hg, fun _ => rfl⟩

theorem exists_assignment_of_three_image {α : Type*} [DecidableEq α]
    (s : Finset α) (hcard : s.card = 3) (f : Fin 3 → α)
    (hs : Finset.univ.image f = s) :
    ∃ e : Fin 3 ≃ s, ∀ j, (e j).val = f j := by
  have hi : Set.InjOn f (Finset.univ : Finset (Fin 3)) :=
    Finset.card_image_iff.mp (by simp [hs, hcard])
  exact exists_assignment_of_image s f
    (fun j k h => hi (Finset.mem_univ j) (Finset.mem_univ k) h) hs

theorem weighted_union_bound {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (P : Ω → Prop) (Q : I → Ω → Prop)
    [DecidablePred P] [∀ i, DecidablePred (Q i)]
    (hcover : ∀ ω, P ω → ∃ i, Q i ω)
    (c : ℝ) (hbound : ∀ i, (∑ ω, if Q i ω then w ω else 0) ≤ c) :
    (∑ ω, if P ω then w ω else 0) ≤ (Fintype.card I : ℝ) * c := by
  classical
  have hpoint : ∀ ω, (if P ω then w ω else 0) ≤
      ∑ i, if Q i ω then w ω else 0 := by
    intro ω
    by_cases hP : P ω
    · obtain ⟨i, hi⟩ := hcover ω hP
      simp only [ite_eq_left hP]
      calc
        w ω = (if Q i ω then w ω else 0) := (ite_eq_left hi).symm
        _ ≤ ∑ j, if Q j ω then w ω else 0 :=
          Finset.single_le_sum (f := fun j => if Q j ω then w ω else 0)
            (fun j _ => by split_ifs; exact hw ω; exact le_rfl) (Finset.mem_univ i)
    · simp only [ite_eq_right hP]
      exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hw ω; exact le_rfl)
  calc
    (∑ ω, if P ω then w ω else 0)
        ≤ ∑ ω, ∑ i, if Q i ω then w ω else 0 := Finset.sum_le_sum (fun ω _ => hpoint ω)
    _ = ∑ i, ∑ ω, if Q i ω then w ω else 0 := Finset.sum_comm
    _ ≤ ∑ _i : I, c := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Fintype.card I : ℝ) * c := by simp

theorem weighted_unordered_deletion_le {Ω ι α : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (A : Ω → Prop) [DecidablePred A] (roles : Ω → ι → Fin 3 → α)
    (D : ι → Finset α) (hD : ∀ i, (D i).card = 3)
    (c : ℝ)
    (hbound : ∀ e : ∀ i, Fin 3 ≃ D i,
      (∑ ω, if A ω ∧ (∀ i j, roles ω i j = (e i j).val) then w ω else 0) ≤ c) :
    (∑ ω, if A ω ∧ (∀ i, Finset.univ.image (roles ω i) = D i) then w ω else 0) ≤
      (6 : ℝ) ^ Fintype.card ι * c := by
  classical
  have hcover : ∀ ω, (A ω ∧ ∀ i, Finset.univ.image (roles ω i) = D i) →
      ∃ e : ∀ i, Fin 3 ≃ D i, A ω ∧ ∀ i j, roles ω i j = (e i j).val := by
    intro ω hω
    have he : ∀ i, ∃ e : Fin 3 ≃ D i, ∀ j, (e j).val = roles ω i j :=
      fun i => exists_assignment_of_three_image (D i) (hD i) (roles ω i) (hω.2 i)
    choose e he using he
    exact ⟨e, hω.1, fun i j => (he i j).symm⟩
  simpa only [card_direction_assignments D hD, Nat.cast_pow, Nat.cast_ofNat] using
    weighted_union_bound w hw _ _ hcover c hbound

theorem weighted_unordered_deletion_le_of_injective_roles {Ω ι α : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (roles : Ω → ι → Fin 3 → α) (hroles : Function.Injective roles)
    (D : ι → Finset α) (hD : ∀ i, (D i).card = 3)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ ω, w ω ≤ c) :
    (∑ ω, if (∀ i, Finset.univ.image (roles ω i) = D i) then w ω else 0) ≤
      (6 : ℝ) ^ Fintype.card ι * c := by
  classical
  have hprescribed : ∀ e : ∀ i, Fin 3 ≃ D i,
      (∑ ω, if True ∧ (∀ i j, roles ω i j = (e i j).val) then w ω else 0) ≤ c := by
    intro e
    by_cases hex : ∃ ω, ∀ i j, roles ω i j = (e i j).val
    · obtain ⟨ω₀, hω₀⟩ := hex
      have hsingle : (∑ ω, if True ∧ (∀ i j, roles ω i j = (e i j).val) then w ω else 0) =
          w ω₀ := by
        rw [Finset.sum_eq_single ω₀]
        · simp [hω₀]
        · intro ω _ hne
          have hn : ¬ ∀ i j, roles ω i j = (e i j).val := by
            intro heq
            apply hne
            apply hroles
            funext i j
            exact (heq i j).trans (hω₀ i j).symm
          simp [hn]
        · simp
      rw [hsingle]
      exact hbound ω₀
    · have hn : ∀ ω, ¬ ∀ i j, roles ω i j = (e i j).val := by simpa using hex
      simpa [hn] using hc
  simpa using weighted_unordered_deletion_le w hw (fun _ => True) roles D hD c hprescribed

end DeletionAssignments
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.DeletionCoordinates

open Finset

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

omit [Fintype I] in
theorem filter_direction_eq_image (S : Finset (I × A)) (i : I) :
    S.filter (fun l => l.1 = i) = (fiber S i).image (fun a => (i, a)) := by
  ext ⟨j, a⟩
  simp only [mem_filter, mem_image, mem_fiber, Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨a, h, rfl, rfl⟩
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨hb, rfl⟩

omit [Fintype I] in
theorem card_filter_direction (S : Finset (I × A)) (i : I) :
    (S.filter (fun l => l.1 = i)).card = (fiber S i).card := by
  rw [filter_direction_eq_image]
  exact card_image_of_injective _ (fun a b h => congrArg Prod.snd h)

@[simp] theorem card_assemble_direction (D : I → Finset A) (i : I) :
    ((assemble D).filter (fun l => l.1 = i)).card = (D i).card := by
  rw [card_filter_direction, fiber_assemble]

end Balanced.DeletionCoordinates

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace UniformKernel

open Finset

variable {U V W : Type*} [Fintype U] [Fintype V]

theorem fiberMass_le [Nonempty U] [Nonempty V]
    (κ : U → V → W → ℝ) (b : ℝ)
    (hκ : ∀ u v w, κ u v w ≤ b) (v : V) (w : W) :
    fiberMass κ v w ≤ b / Fintype.card V := by
  have hU : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast Fintype.card_pos
  have hV : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  unfold fiberMass
  apply (div_le_iff₀ (mul_pos hU hV)).2
  have hs : (∑ u, κ u v w) ≤ (Fintype.card U : ℝ) * b := by
    calc
      (∑ u, κ u v w) ≤ ∑ _u : U, b := sum_le_sum (fun u _ => hκ u v w)
      _ = (Fintype.card U : ℝ) * b := by simp
  calc
    (∑ u, κ u v w) ≤ (Fintype.card U : ℝ) * b := hs
    _ = b / (Fintype.card V : ℝ) *
        ((Fintype.card U : ℝ) * Fintype.card V) := by field_simp

theorem fiberMass_nonneg (κ : U → V → W → ℝ)
    (hκ : ∀ u v w, 0 ≤ κ u v w) (v : V) (w : W) :
    0 ≤ fiberMass κ v w := by
  unfold fiberMass
  exact div_nonneg (sum_nonneg (fun u _ => hκ u v w)) (by positivity)

end UniformKernel
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_ExponentialDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace BalancedRyser

theorem deletion_ratio_exponential_envelope
    {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    {q : ℕ} (hq : 1 ≤ q) :
    a⁻¹ * K ^ (2 * (q + 1)) ≤
      Real.exp ((a⁻¹ + 4 * K) * (q : ℝ)) := by
  have ha' : 0 ≤ a⁻¹ := le_of_lt (inv_pos.mpr ha)
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqa : a⁻¹ ≤ a⁻¹ * (q : ℝ) := by nlinarith
  have hpow : K ^ (2 * (q + 1)) ≤
      Real.exp K ^ (2 * (q + 1)) :=
    pow_le_pow_left₀ hK (by linarith [Real.add_one_le_exp K]) _
  have hinv : a⁻¹ ≤ Real.exp a⁻¹ := by
    linarith [Real.add_one_le_exp a⁻¹]
  calc
    a⁻¹ * K ^ (2 * (q + 1)) ≤
        Real.exp a⁻¹ * Real.exp K ^ (2 * (q + 1)) :=
      mul_le_mul hinv hpow (pow_nonneg hK _) (Real.exp_nonneg _)
    _ = Real.exp (a⁻¹ + (2 * (q + 1) : ℕ) * K) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp ((a⁻¹ + 4 * K) * (q : ℝ)) := by
      apply Real.exp_monotone
      push_cast
      nlinarith

end BalancedRyser

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionDomination2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.DeletionLaw

theorem six_mul_choose_three_le (q : ℕ) :
    6 * (Nat.choose q 3 : ℝ) ≤ (q : ℝ) ^ 3 := by
  have h := (Nat.choose_le_pow_div (α := ℝ) 3 q)
  norm_num at h
  linarith

theorem assignment_normalization_le {q : ℕ} (hq : 3 ≤ q) :
    6 / (q : ℝ) ^ 3 ≤ (Nat.choose q 3 : ℝ)⁻¹ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcpos : (0 : ℝ) < Nat.choose q 3 := by
    exact_mod_cast Nat.choose_pos hq
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (pow_pos hqpos 3) hcpos).2
  simpa using six_mul_choose_three_le q

theorem assignment_factorization (q n : ℕ) (K : ℝ) :
    (6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n) =
      (6 * K ^ 2 / (q : ℝ) ^ 3) ^ n := by
  rw [pow_mul, div_pow, ← div_pow, ← mul_pow]
  congr 1
  ring

theorem assignment_bound_le_uniform {q n : ℕ} (hq : 3 ≤ q) (K : ℝ) :
    (6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n) ≤
      K ^ (2 * n) * uniformDeletionMass q n := by
  rw [assignment_factorization]
  have hb : 6 * K ^ 2 / (q : ℝ) ^ 3 ≤
      K ^ 2 * (Nat.choose q 3 : ℝ)⁻¹ := by
    calc
      6 * K ^ 2 / (q : ℝ) ^ 3 = K ^ 2 * (6 / (q : ℝ) ^ 3) := by ring
      _ ≤ K ^ 2 * (Nat.choose q 3 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (assignment_normalization_le hq) (sq_nonneg K)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 6 * K ^ 2 / (q : ℝ) ^ 3) hb n
  simpa only [mul_pow, ← pow_mul, inv_pow, uniformDeletionMass] using hp

end Balanced.DeletionLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionFieldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.FieldTransport

variable {F G : Type*} [Field F] [Field G]

variable [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]

omit [DecidableEq F] [DecidableEq G] in
@[simp] theorem cardinal_field (e : F ≃+* G) : Fintype.card G = Fintype.card F :=
  (Fintype.card_congr e.toEquiv).symm

end Balanced.FieldTransport

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_GeometricDeletionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
namespace GeometricDeletionCounting

variable {F : Type*} [Fintype F] [DecidableEq F]

variable [Field F]

theorem card_deletionSet (k : ℕ) :
    Fintype.card (DeletionSet F k) =
      (Nat.choose (Fintype.card F) k) ^ (Fintype.card F + 1) := by
  rw [Fintype.card_congr (deletionEquivFamilies (F := F) k)]
  simp [Direction]

theorem uniformDeletionMass_eq (k : ℕ) :
    uniformDeletionMass (F := F) k =
      ((Nat.choose (Fintype.card F) k : ℝ) ^ (Fintype.card F + 1))⁻¹ := by
  simp [uniformDeletionMass, card_deletionSet]

end GeometricDeletionCounting
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Balanced.SelectedDeletion

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {c C K ρ ε : ℝ}
variable (laws : ∀ M : MergedPairs F, InitialGood M c C → FixedLaw M K ρ ε)

theorem glue_isExperiment : IsExperiment (glue laws) c C := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M s
    by_cases h : InitialGood M c C
    · simpa [glue, h] using (laws M h).nonnegative s
    · simp [glue, h]
  · intro M
    by_cases h : InitialGood M c C
    · simpa [glue, h] using (laws M h).mass_le_one
    · simp [glue, h]
  · intro M h s
    simp [glue, h]
  · intro M s hs
    by_cases h : InitialGood M c C
    · exact (laws M h).supported s (by simpa [glue, h] using hs)
    · simp [glue, h] at hs

theorem glue_fixedSuccessMass (M : MergedPairs F) (h : InitialGood M c C) :
    1 - ε ≤ fixedSuccessMass (glue laws) M := by
  simpa [fixedSuccessMass, glue, h] using (laws M h).success_lower

theorem glue_fixedCylinderMass_le (hK : 0 ≤ K) (M : MergedPairs F)
    (J : Finset (Slot F)) (prescribed : Output F) :
    fixedCylinderMass (glue laws) M J prescribed ≤
      (K / (Fintype.card F : ℝ)) ^ J.card := by
  classical
  by_cases h : InitialGood M c C
  · simpa [fixedCylinderMass, glue, h] using (laws M h).cylinder_le J prescribed
  · simp only [fixedCylinderMass, glue, h, dite_false, ite_self, sum_const_zero]
    positivity

theorem offset_sum_real : ∑ M : MergedPairs F, ((offsetLaw F) M).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun M _ => (offsetLaw F).apply_ne_top M)]
  have h : ∑ M : MergedPairs F, (offsetLaw F) M = 1 := by
    simpa only [tsum_fintype] using (offsetLaw F).tsum_coe
  rw [h]
  simp

theorem offsetEventProbability_eq_sum (P : MergedPairs F → Prop) :
    offsetEventProbability {M | P M} =
      ∑ M, if P M then ((offsetLaw F) M).toReal else 0 := by
  classical
  unfold offsetEventProbability
  rw [PMF.toOuterMeasure_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply sum_congr rfl
    intro M _
    by_cases h : P M <;> simp [Set.indicator, h]
  · intro M _
    by_cases h : P M <;> simp [Set.indicator, h, (offsetLaw F).apply_ne_top]

theorem glue_occupancyFailureMass_le (hε : 0 ≤ ε) :
    occupancyFailureMass (glue laws) ρ ≤ ε := by
  classical
  unfold occupancyFailureMass jointMass
  calc
    _ ≤ ∑ M : MergedPairs F, ((offsetLaw F) M).toReal * ε := by
      apply sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      by_cases h : InitialGood M c C
      · refine le_trans (le_of_eq ?_) (laws M h).occupancy_le
        apply sum_congr rfl
        intro output _
        by_cases hocc : (configuration M output).Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ <;>
          simp [glue, h, hocc]
      · simpa [glue, h] using hε
    _ = ε := by rw [← sum_mul, offset_sum_real, one_mul]

theorem glue_successMass_lower :
    (1 - ε) * offsetEventProbability {M : MergedPairs F | InitialGood M c C} ≤
      successMass (glue laws) := by
  classical
  rw [offsetEventProbability_eq_sum]
  unfold successMass jointMass
  rw [mul_sum]
  apply sum_le_sum
  intro M _
  by_cases h : InitialGood M c C
  · simp only [h, ite_true]
    rw [mul_comm (1 - ε)]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simpa [glue, h] using (laws M h).success_lower
  · simp [glue, h]

theorem glue_successMass_lower_half {p : ℝ} (hp : 0 ≤ p)
    (hgood : p ≤ offsetEventProbability {M : MergedPairs F | InitialGood M c C})
    (hε : ε ≤ 1 / 2) : p / 2 ≤ successMass (glue laws) := by
  have hP : 0 ≤ offsetEventProbability {M : MergedPairs F | InitialGood M c C} :=
    hp.trans hgood
  have hprod : 0 ≤ (1 / 2 - ε) *
      offsetEventProbability {M : MergedPairs F | InitialGood M c C} :=
    mul_nonneg (sub_nonneg.mpr hε) hP
  exact (by nlinarith : p / 2 ≤ (1 - ε) *
    offsetEventProbability {M : MergedPairs F | InitialGood M c C}).trans
    (glue_successMass_lower laws)

end Balanced.SelectedDeletion

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.SelectedDeletionCoordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem roles_injective : Function.Injective (@roles F) := by
  intro a b h
  apply Prod.ext
  · funext d
    simpa [roles] using congrFun (congrFun h d) (0 : Fin 3)
  · funext s
    obtain ⟨d, t⟩ := s
    cases t
    · simpa [roles] using congrFun (congrFun h d) (1 : Fin 3)
    · simpa [roles] using congrFun (congrFun h d) (2 : Fin 3)

theorem mem_selected_deletedLines (M : MergedPairs F) (f : SplitOffsets F)
    (d : Direction F) (a : F) :
    (d, a) ∈ (selectedConfiguration M f).deletedLines ↔
      a = M d true ∨ a = f (d, false) ∨ a = f (d, true) := by
  simp only [Configuration.deletedLines, Configuration.splitLines,
    selectedConfiguration, retainedChoice_line, constituent,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, Prod.mk.injEq]
  constructor
  · rintro (⟨e, b, he, ha⟩ | ⟨e, he, ha⟩)
    · subst e
      cases b
      · exact Or.inr (Or.inl ha.symm)
      · exact Or.inr (Or.inr ha.symm)
    · subst e
      exact Or.inl ha.symm
  · rintro (h | h | h)
    · exact Or.inr ⟨d, rfl, h.symm⟩
    · exact Or.inl ⟨d, false, rfl, h.symm⟩
    · exact Or.inl ⟨d, true, rfl, h.symm⟩

theorem selected_deletedLines_eq_assemble (M : MergedPairs F) (f : SplitOffsets F) :
    (selectedConfiguration M f).deletedLines =
      DeletionCoordinates.assemble
        (fun d => Finset.univ.image (roles (fun d => M d true, f) d)) := by
  ext l
  obtain ⟨d, a⟩ := l
  rw [mem_selected_deletedLines, DeletionCoordinates.mem_assemble]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
  · rintro ⟨j, hj⟩
    fin_cases j <;> simp_all [roles]

theorem selected_deletedLines_eq_iff (M : MergedPairs F) (f : SplitOffsets F)
    (D : Finset (Line F)) :
    (selectedConfiguration M f).deletedLines = D ↔
      ∀ d, Finset.univ.image (roles (fun d => M d true, f) d) =
        DeletionCoordinates.fiber D d := by
  rw [selected_deletedLines_eq_assemble]
  constructor
  · intro h
    have hf := congrArg DeletionCoordinates.fiber h
    simpa only [DeletionCoordinates.fiber_assemble, funext_iff] using hf
  · intro h
    rw [show (fun d => Finset.univ.image (roles (fun d => M d true, f) d)) =
      DeletionCoordinates.fiber D from funext h]
    exact DeletionCoordinates.assemble_fiber D

theorem jointMass_eq_uniform_average (κ : SelectedDeletion.Kernel F)
    (E : MergedPairs F → SelectedDeletion.Output F → Prop) [∀ M f, Decidable (E M f)] :
    SelectedDeletion.jointMass κ E =
      (∑ M, ∑ f, if E M f then κ M f else 0) / Fintype.card (MergedPairs F) := by
  classical
  unfold SelectedDeletion.jointMass
  simp only [offsetLaw, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  simp only [div_eq_mul_inv, Finset.mul_sum, mul_comm]
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : E M f <;> simp [h]

omit [Field F] in

theorem card_mergedPairs :
    Fintype.card (MergedPairs F) =
      Fintype.card (SingleOffsets F) * Fintype.card (SingleOffsets F) := by
  rw [← Fintype.card_congr (offsetPairEquiv (F := F)), Fintype.card_prod]

theorem sum_fiberMass {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (κ : U → V → W → ℝ) :
    (∑ v, ∑ w, UniformKernel.fiberMass κ v w) =
      (∑ u, ∑ v, ∑ w, κ u v w) /
        ((Fintype.card U : ℝ) * Fintype.card V) := by
  simp only [UniformKernel.fiberMass, ← Finset.sum_div]
  congr 1
  calc
    (∑ v, ∑ w, ∑ u, κ u v w) = ∑ v, ∑ u, ∑ w, κ u v w := by
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.sum_comm
    _ = ∑ u, ∑ v, ∑ w, κ u v w := Finset.sum_comm

theorem deletionJointMass_eq_fiber_sum (κ : SelectedDeletion.Kernel F)
    (D : DeletionSet F 3) :
    SelectedDeletion.deletionJointMass κ D =
      ∑ ω : SingleOffsets F × SplitOffsets F,
        if (∀ d, Finset.univ.image (roles ω d) = DeletionCoordinates.fiber D.val d) then
          UniformKernel.fiberMass
            (fun m₀ m₁ f => κ (offsetPairEquiv (m₀, m₁)) f) ω.1 ω.2 else 0 := by
  classical
  rw [SelectedDeletion.deletionJointMass, jointMass_eq_uniform_average]
  change (∑ M, ∑ f, if (selectedConfiguration M f).deletedLines = D.val then κ M f else 0) /
    (Fintype.card (MergedPairs F) : ℝ) = _
  rw [← (offsetPairEquiv (F := F)).sum_comp
    (fun M => ∑ f, if (selectedConfiguration M f).deletedLines = D.val then κ M f else 0)]
  rw [Fintype.sum_prod_type]
  simp_rw [selected_deletedLines_eq_iff]
  rw [card_mergedPairs, Nat.cast_mul, Fintype.sum_prod_type]
  let P := fun m₁ f => ∀ d, Finset.univ.image (roles (m₁, f) d) = DeletionCoordinates.fiber D.val d
  let W := fun m₀ m₁ f => κ (offsetPairEquiv (m₀, m₁)) f
  change (∑ m₀, ∑ m₁, ∑ f, if P m₁ f then W m₀ m₁ f else 0) /
    ((Fintype.card (SingleOffsets F) : ℝ) * Fintype.card (SingleOffsets F)) =
    ∑ m₁, ∑ f, if P m₁ f then UniformKernel.fiberMass W m₁ f else 0
  rw [← sum_fiberMass (fun m₀ m₁ f => if P m₁ f then W m₀ m₁ f else 0)]
  apply Finset.sum_congr rfl
  intro m₁ _
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : P m₁ f <;> simp [UniformKernel.fiberMass, h]

end Balanced.SelectedDeletionCoordinates

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.SelectedDeletion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem atom_le_of_fixed_cylinders {κ : Kernel F} {K : ℝ}
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (M : MergedPairs F) (f : Output F) :
    κ M f ≤ (K / Fintype.card F) ^ (2 * (Fintype.card F + 1)) := by
  classical
  have h := hcyl M Finset.univ f
  have heq : ∀ g : Output F,
      (∀ i ∈ (Finset.univ : Finset (Slot F)), g i = f i) ↔ g = f := by
    intro g
    simp only [Finset.mem_univ, forall_const, funext_iff]
  unfold fixedCylinderMass at h
  simp_rw [heq] at h
  simpa [Slot, Direction, Nat.mul_comm] using h

theorem deletionJointMass_le_of_atom_bound (κ : Kernel F)
    (hnonneg : ∀ M f, 0 ≤ κ M f) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ M f, κ M f ≤ b) (D : DeletionSet F 3) :
    deletionJointMass κ D ≤ (6 : ℝ) ^ (Fintype.card F + 1) *
      (b / (Fintype.card F : ℝ) ^ (Fintype.card F + 1)) := by
  classical
  rw [SelectedDeletionCoordinates.deletionJointMass_eq_fiber_sum]
  let W := fun m₀ m₁ f => κ (SelectedDeletionCoordinates.offsetPairEquiv (m₀, m₁)) f
  have hw : ∀ ω : SelectedDeletionCoordinates.SingleOffsets F ×
      SelectedDeletionCoordinates.SplitOffsets F,
      0 ≤ UniformKernel.fiberMass W ω.1 ω.2 := by
    intro ω
    exact UniformKernel.fiberMass_nonneg W (fun m₀ m₁ f => hnonneg _ _) _ _
  have hcard : ∀ d, (DeletionCoordinates.fiber D.val d).card = 3 := by
    intro d
    rw [← DeletionCoordinates.card_filter_direction]
    exact D.property d
  have hc : 0 ≤ b / Fintype.card (SelectedDeletionCoordinates.SingleOffsets F) :=
    div_nonneg hb (Nat.cast_nonneg _)
  have h := DeletionAssignments.weighted_unordered_deletion_le_of_injective_roles
    (fun ω : SelectedDeletionCoordinates.SingleOffsets F × SelectedDeletionCoordinates.SplitOffsets F =>
      UniformKernel.fiberMass W ω.1 ω.2) hw
    SelectedDeletionCoordinates.roles SelectedDeletionCoordinates.roles_injective
    (DeletionCoordinates.fiber D.val) hcard
    (b / Fintype.card (SelectedDeletionCoordinates.SingleOffsets F)) hc
    (fun ω => UniformKernel.fiberMass_le W b (fun _ _ _ => hbound _ _) ω.1 ω.2)
  simpa only [SelectedDeletionCoordinates.SingleOffsets, Fintype.card_fun,
    Direction, Fintype.card_option, Nat.cast_pow] using h

theorem realizesConditionalLaw_dominated {κ : Kernel F} {K a₀ : ℝ}
    (hq : 3 ≤ Fintype.card F) (hK : 0 ≤ K) (ha₀ : 0 < a₀)
    (hnonneg : ∀ M f, 0 ≤ κ M f)
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (hsuccess : a₀ ≤ successMass κ)
    (Q : PMF (DeletionSet F 3)) (hQ : RealizesConditionalLaw κ Q) :
    DeletionDominated 3 (a₀⁻¹ + 4 * K) Q := by
  intro D
  rw [hQ D]
  have hspos : 0 < successMass κ := ha₀.trans_le hsuccess
  have hraw := deletionJointMass_le_of_atom_bound κ hnonneg
    ((K / Fintype.card F) ^ (2 * (Fintype.card F + 1)))
    (by positivity) (atom_le_of_fixed_cylinders hcyl) D
  have hfinite := hraw.trans (DeletionLaw.assignment_bound_le_uniform hq K)
  have hu : 0 ≤ DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1) := by
    unfold DeletionLaw.uniformDeletionMass
    positivity
  have hcoef : 0 ≤ K ^ (2 * (Fintype.card F + 1)) := by positivity
  calc
    deletionJointMass κ D / successMass κ ≤
        (K ^ (2 * (Fintype.card F + 1)) *
          DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1)) / a₀ :=
      (div_le_div_of_nonneg_right hfinite hspos.le).trans
        (div_le_div_of_nonneg_left (mul_nonneg hcoef hu) ha₀ hsuccess)
    _ = (a₀⁻¹ * K ^ (2 * (Fintype.card F + 1))) *
          DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1) := by ring
    _ ≤ Real.exp ((a₀⁻¹ + 4 * K) * (Fintype.card F : ℝ)) *
          DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1) :=
      mul_le_mul_of_nonneg_right
        (BalancedRyser.deletion_ratio_exponential_envelope ha₀ hK (by omega)) hu
    _ = Real.exp ((a₀⁻¹ + 4 * K) * (Fintype.card F : ℝ)) *
          uniformDeletionMass (F := F) 3 := by
      rw [GeometricDeletionCounting.uniformDeletionMass_eq]
      rfl

end Balanced.SelectedDeletion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionPMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.SelectedDeletion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Kernel F} {c C : ℝ}

theorem conditionalDeletionLaw_realizes (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) :
    RealizesConditionalLaw κ (conditionalDeletionLaw hκ hsuccess) :=
  conditionalDeletionLaw_apply_toReal hκ hsuccess

theorem exists_realizing_dominated_law (hκ : IsExperiment κ c C)
    {K a₀ : ℝ} (hq : 3 ≤ Fintype.card F) (hK : 0 ≤ K) (ha₀ : 0 < a₀)
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (hsuccess : a₀ ≤ successMass κ) :
    ∃ Q : PMF (DeletionSet F 3),
      RealizesConditionalLaw κ Q ∧ DeletionDominated 3 (a₀⁻¹ + 4 * K) Q := by
  let Q := conditionalDeletionLaw hκ (ha₀.trans_le hsuccess)
  have hQ : RealizesConditionalLaw κ Q := conditionalDeletionLaw_realizes hκ _
  exact ⟨Q, hQ, realizesConditionalLaw_dominated hq hK ha₀ hκ.1 hcyl hsuccess Q hQ⟩

end Balanced.SelectedDeletion

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter Topology

theorem uniform_threshold_of_growing_sequences {X : Type*} (size : X → ℕ) (P : X → Prop)
    (h : ∀ x : ℕ → X, Tendsto (fun n => size (x n)) atTop atTop →
      ∀ᶠ n in atTop, P (x n)) :
    ∃ N : ℕ, ∀ x : X, N ≤ size x → P x := by
  classical
  by_contra hn
  push Not at hn
  choose x hsize hbad using hn
  have ht : Tendsto (fun n => size (x n)) atTop atTop :=
    tendsto_atTop_mono hsize tendsto_id
  obtain ⟨n, hn⟩ := (h x ht).exists
  exact hbad n hn

universe u

attribute [instance] FiniteFieldPresentation.field FiniteFieldPresentation.finite
  FiniteFieldPresentation.decidable

theorem candidate_graph_uniform_threshold (h : CandidateGraphResult.{u}) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], N ≤ Fintype.card F →
        |offsetEventProbability (F := F) {M | CandidateGraphGood M c C} - 1| < ε ∧
        |offsetEventProbability (F := F)
          {M | CandidateGraphGood M c C ∧ DistinctConstituents M} - Real.exp (-1)| < ε := by
  obtain ⟨c, C, hc, hC, hseq⟩ := h
  refine ⟨c, C, hc, hC, ?_⟩
  intro ε hε
  let size : FiniteFieldPresentation.{u} → ℕ := fun A => Fintype.card A.carrier
  let P : FiniteFieldPresentation.{u} → Prop := fun A =>
    |offsetEventProbability (F := A.carrier) {M | CandidateGraphGood M c C} - 1| < ε ∧
    |offsetEventProbability (F := A.carrier)
      {M | CandidateGraphGood M c C ∧ DistinctConstituents M} - Real.exp (-1)| < ε
  have hev : ∀ A : ℕ → FiniteFieldPresentation.{u},
      Tendsto (fun n => size (A n)) atTop atTop → ∀ᶠ n in atTop, P (A n) := by
    intro A hA
    have hlim := hseq (fun n => (A n).carrier) hA
    have h₁ := (Metric.tendsto_nhds.mp hlim.1) ε hε
    have h₂ := (Metric.tendsto_nhds.mp hlim.2) ε hε
    simpa only [P, Real.dist_eq] using h₁.and h₂
  obtain ⟨N, hN⟩ := uniform_threshold_of_growing_sequences size P hev
  refine ⟨N, ?_⟩
  intro F hF hFin hDec hcard
  exact hN ⟨F, hF, hFin, hDec⟩ hcard

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced.SelectedDeletion

universe u

theorem initialGood_uniform_lower (h : CandidateGraphResult.{u}) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F →
        Real.exp (-1) / 2 ≤ offsetEventProbability
          {M : MergedPairs F | InitialGood M c C} := by
  obtain ⟨c, C, hc, hC, hthreshold⟩ := candidate_graph_uniform_threshold h
  obtain ⟨N, hN⟩ := hthreshold (Real.exp (-1) / 2) (by positivity)
  refine ⟨c, C, hc, hC, N, ?_⟩
  intro F hF hFin hDec hcard
  have hnear := (hN F hcard).2
  have hlower := (abs_lt.mp hnear).1
  change Real.exp (-1) / 2 ≤ offsetEventProbability
    {M : MergedPairs F | CandidateGraphGood M c C ∧ DistinctConstituents M}
  linarith

theorem result_of_uniform_fixedLaws
    (hcandidate : CandidateGraphResult.{u})
    (hfixed : ∀ c C : ℝ, 0 < c → 0 < C →
      ∃ K ρ : ℝ, ∃ ε : ℕ → ℝ, ∃ N : ℕ,
        0 < K ∧ 0 < ρ ∧ (∀ q, 0 ≤ ε q) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
          N ≤ Fintype.card F → ∀ M : MergedPairs F,
            InitialGood M c C → Nonempty (FixedLaw M K ρ (ε (Fintype.card F)))) :
    SelectedDeletionResult.{u} := by
  classical
  obtain ⟨c, C, hc, hC, NGood, hgood⟩ := initialGood_uniform_lower hcandidate
  obtain ⟨K, ρ, ε, NSel, hK, hρ, hε, hlim, hlaws⟩ := hfixed c C hc hC
  have hevent : ∀ᶠ q in atTop, ε q < (1 / 2 : ℝ) :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨NErr, hErr⟩ := eventually_atTop.1 hevent
  let K' : ℝ := max 1 K
  let ρ' : ℝ := min ρ (1 / 2)
  let a₀ : ℝ := Real.exp (-1) / 4
  let N : ℕ := max 4 (max NGood (max NSel NErr))
  have hK' : 1 ≤ K' := le_max_left _ _
  have hK'nonneg : 0 ≤ K' := le_trans (by norm_num) hK'
  have hρ'pos : 0 < ρ' := lt_min hρ (by norm_num)
  have hρ'one : ρ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hC₀ : 0 < a₀⁻¹ + 4 * K' :=
    add_pos_of_pos_of_nonneg (inv_pos.mpr ha₀) (mul_nonneg (by norm_num) hK'nonneg)
  refine ⟨c, C, K', ρ', a₀, a₀⁻¹ + 4 * K', ε, N,
    hc, hC, hK', hρ'pos, hρ'one, ha₀, hC₀, le_max_left _ _, hε, hlim, ?_⟩
  intro F _ _ _ hlarge
  have h4 : 4 ≤ Fintype.card F := (le_max_left _ _).trans hlarge
  have hlargeGood : NGood ≤ Fintype.card F := by dsimp [N] at hlarge; omega
  have hlargeSel : NSel ≤ Fintype.card F := by dsimp [N] at hlarge; omega
  have hlargeErr : NErr ≤ Fintype.card F := by dsimp [N] at hlarge; omega
  let laws : ∀ M : MergedPairs F, InitialGood M c C →
      FixedLaw M K' ρ' (ε (Fintype.card F)) := fun M hM =>
    (Classical.choice (hlaws F hlargeSel M hM)).relax hK.le (le_max_right _ _)
      (min_le_left _ _)
  have hsuccess : a₀ ≤ successMass (glue laws) := by
    have h := glue_successMass_lower_half laws
      (show 0 ≤ Real.exp (-1) / 2 by positivity)
      (hgood F hlargeGood) (hErr _ hlargeErr).le
    dsimp [a₀]
    linarith
  refine ⟨glue laws, glue_isExperiment laws, glue_fixedSuccessMass laws,
    glue_fixedCylinderMass_le laws hK'nonneg, hsuccess,
    glue_occupancyFailureMass_le laws (hε _), ?_⟩
  exact exists_realizing_dominated_law (glue_isExperiment laws) (by omega)
    hK'nonneg ha₀ (glue_fixedCylinderMass_le laws hK'nonneg) hsuccess

end Balanced.SelectedDeletion

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionFromSelection
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.SelectedDeletion

universe u

theorem uniform_fixedLaws_of_selection (hselection : SelectionStatement.{u,u,u})
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ K ρ : ℝ, ∃ ε : ℕ → ℝ, ∃ N : ℕ,
      0 < K ∧ 0 < ρ ∧ (∀ q, 0 ≤ ε q) ∧
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → ∀ M : MergedPairs F,
          InitialGood M c C → Nonempty (FixedLaw M K ρ (ε (Fintype.card F))) := by
  classical
  obtain ⟨K, ρ, ε, N, hK, hρ, hε, hlim, hselect⟩ :=
    hselection c C (1 / 5) hc hC (by norm_num) (by norm_num)
  refine ⟨K, ρ, ε, N, hK, hρ, hε, hlim, ?_⟩
  intro F _ _ _ hlarge M hM
  obtain ⟨J, hJ⟩ := candidateGraphGood_selection hM.1
  obtain ⟨law, hsuccess, hcylinder, hoccupancy⟩ :=
    hselect (Fintype.card F) hlarge (Slot F) (AvailableCandidate M)
      (candidateSelectionInput M J) hJ
  have hocc := hoccupancy (Point F) (Direction F) (Line F) (coordinatePlane F)
    (Equiv.refl (Slot F)) (fun v : AvailableCandidate M => candidateLine v.val)
    (candidateSelection_lineAssignment M J) (candidateTrackedSets M)
    (candidateSelection_trackedSets hM.1)
  exact ⟨fixedLawOfSelection M hc hM.1 hM.2 J law hsuccess hcylinder hocc⟩

theorem result_of_candidate_and_selection
    (hcandidate : CandidateGraphResult.{u})
    (hselection : SelectionStatement.{u,u,u}) : SelectedDeletionResult.{u} :=
  result_of_uniform_fixedLaws hcandidate (uniform_fixedLaws_of_selection hselection)

end Balanced.SelectedDeletion

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BoundedDriftCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma condExp_exp_le_of_abs_le [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Y : Ω → ℝ} {a : ℝ}
    (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) (θ : ℝ) :
    μ[fun ω ↦ exp (θ * Y ω) | m] ≤ᵐ[μ]
      fun _ ↦ exp (a ^ 2 * θ ^ 2 / 2) := by
  have hIcc : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-a) a := by
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hYi : Integrable Y μ := Integrable.of_mem_Icc (-a) a (hY.measurable.aemeasurable (μ := μ)) hIcc
  have hEi : Integrable (fun ω ↦ exp (θ * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc (hY.measurable.aemeasurable (μ := μ)) hIcc
  let b : ℝ := sinh (a * θ) / a
  have hlin : Integrable (fun ω ↦ cosh (a * θ) + b * Y ω) μ :=
    (integrable_const _).add (hYi.const_mul b)
  have hpoint : (fun ω ↦ exp (θ * Y ω)) ≤ᵐ[μ]
      fun ω ↦ cosh (a * θ) + b * Y ω := by
    filter_upwards [hb] with ω hω
    have hdiv : |Y ω / a| ≤ 1 := by
      rw [abs_div, abs_of_pos ha, div_le_one ha]
      exact hω
    have he := exp_mul_le_cosh_add_mul_sinh hdiv (a * θ)
    convert he using 1
    · congr 1
      field_simp
    · dsimp [b]
      ring
  have hmono := condExp_mono (m := m) hEi hlin hpoint
  have hlinear : μ[fun ω ↦ cosh (a * θ) + b * Y ω | m] =ᵐ[μ]
      fun _ ↦ cosh (a * θ) := by
    have hAdd := condExp_add (integrable_const (cosh (a * θ))) (hYi.const_mul b) m
    have hMul := condExp_smul (μ := μ) b Y m
    filter_upwards [hAdd, hMul, hzero] with ω hA hM hZ
    change μ[fun ω ↦ b * Y ω | m] ω = b * μ[Y | m] ω at hM
    change μ[Y | m] ω = 0 at hZ
    simp only [Pi.add_def] at hA
    simpa only [condExp_const hm, hM, hZ, mul_zero, add_zero] using hA
  filter_upwards [hmono, hlinear] with ω hM hL
  rw [hL] at hM
  exact hM.trans (by simpa only [mul_pow] using cosh_le_exp_half_sq (a * θ))

lemma subGaussian_add_of_bounded_difference [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X Y : Ω → ℝ} {c : ℝ≥0} {a : ℝ}
    (hX : HasSubgaussianMGF X c μ) (hXm : StronglyMeasurable[m] X)
    (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) :
    HasSubgaussianMGF (X + Y) (c + NNReal.mk (a ^ 2) (sq_nonneg a)) μ := by
  have hEY (θ : ℝ) : Integrable (fun ω ↦ exp (θ * Y ω)) μ := by
    apply integrable_exp_mul_of_mem_Icc (hY.measurable.aemeasurable (μ := μ))
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hProd (θ : ℝ) : Integrable
      ((fun ω ↦ exp (θ * X ω)) * fun ω ↦ exp (θ * Y ω)) μ := by
    apply (hX.integrable_exp_mul θ).mul_bdd (hEY θ).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      θ * Y ω ≤ |θ * Y ω| := le_abs_self _
      _ = |θ| * |Y ω| := abs_mul _ _
      _ ≤ |θ| * a := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · intro θ
    simpa only [Pi.add_apply, mul_add, exp_add, Pi.mul_def] using hProd θ
  · intro θ
    have hPull := condExp_mul_of_stronglyMeasurable_left
      (f := fun ω ↦ exp (θ * X ω)) (g := fun ω ↦ exp (θ * Y ω))
      (by exact continuous_exp.comp_stronglyMeasurable (hXm.const_mul θ))
      (hProd θ) (hEY θ)
    have hPullInt : Integrable
        ((fun ω ↦ exp (θ * X ω)) * μ[fun ω ↦ exp (θ * Y ω) | m]) μ :=
      integrable_condExp.congr hPull
    have hcond := condExp_exp_le_of_abs_le hm ha hY hb hzero θ
    calc
      mgf (X + Y) μ θ = ∫ ω, exp (θ * X ω) * exp (θ * Y ω) ∂μ := by
        simp only [mgf, Pi.add_apply, mul_add, exp_add]
      _ = ∫ ω, exp (θ * X ω) * μ[fun ω ↦ exp (θ * Y ω) | m] ω ∂μ := by
        change (∫ ω, ((fun ω ↦ exp (θ * X ω)) * fun ω ↦ exp (θ * Y ω)) ω ∂μ) = _
        rw [← integral_condExp hm]
        exact integral_congr_ae hPull
      _ ≤ ∫ ω, exp (θ * X ω) * exp (a ^ 2 * θ ^ 2 / 2) ∂μ := by
        apply integral_mono_ae hPullInt ((hX.integrable_exp_mul θ).mul_const _)
        filter_upwards [hcond] with ω hω
        exact mul_le_mul_of_nonneg_left hω (exp_nonneg _)
      _ = mgf X μ θ * exp (a ^ 2 * θ ^ 2 / 2) := by rw [integral_mul_const]; rfl
      _ ≤ exp ((c : ℝ) * θ ^ 2 / 2) * exp (a ^ 2 * θ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (hX.mgf_le θ) (exp_nonneg _)
      _ = exp (((c + NNReal.mk (a ^ 2) (sq_nonneg a) : ℝ≥0) : ℝ) * θ ^ 2 / 2) := by
        rw [← exp_add]
        congr 1
        change (c : ℝ) * θ ^ 2 / 2 + a ^ 2 * θ ^ 2 / 2 = ((c : ℝ) + a ^ 2) * θ ^ 2 / 2
        ring

lemma subGaussian_sum_of_bounded_differences [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (n : ℕ)
    (hY : ∀ j < n, StronglyMeasurable[ℱ (j + 1)] (Y j))
    (hb : ∀ j < n, ∀ᵐ ω ∂μ, |Y j ω| ≤ a)
    (hzero : ∀ j < n, μ[Y j | ℱ j] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω)
      ((n : ℝ≥0) * NNReal.mk (a ^ 2) (sq_nonneg a)) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun j hj ↦ hY j (by omega))
      (fun j hj ↦ hb j (by omega)) (fun j hj ↦ hzero j (by omega))
    have hsum : StronglyMeasurable[ℱ n] (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      exact (hY j (by omega)).mono (ℱ.mono (by omega))
    have hnext := subGaussian_add_of_bounded_difference (ℱ.le n) hprev hsum ha
      ((hY n (by omega)).mono (ℱ.le (n + 1))) (hb n (by omega)) (hzero n (by omega))
    simpa only [Finset.sum_range_succ, Pi.add_def, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul] using hnext

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CenteredIncrements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {Y : Ω → ℝ} {L : ℝ}

theorem integrable_of_abs_le (hY : AEMeasurable Y μ)
    (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ L) : Integrable Y μ := by
  apply Integrable.of_mem_Icc (-L) L hY
  filter_upwards [hbound] with ω hω using abs_le.mp hω

omit [IsFiniteMeasure μ] in

theorem abs_sub_condExp_le (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ L) :
    ∀ᵐ ω ∂μ, |Y ω - μ[Y | m] ω| ≤ 2 * L := by
  have hc := ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) hbound
  filter_upwards [hbound, hc] with ω hω hcω
  calc
    |Y ω - μ[Y | m] ω| ≤ |Y ω| + |μ[Y | m] ω| := abs_sub _ _
    _ ≤ L + L := add_le_add hω hcω
    _ = 2 * L := by ring

theorem condExp_sub_condExp_eq_zero (hm : m ≤ mΩ) (hYi : Integrable Y μ) :
    μ[fun ω ↦ Y ω - μ[Y | m] ω | m] =ᵐ[μ] 0 := by
  have hsub := condExp_sub hYi (integrable_condExp (f := Y) (m := m)) m
  have hfix : μ[μ[Y | m] | m] = μ[Y | m] :=
    condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp
  simpa only [Pi.sub_def, hfix, sub_self] using hsub

variable {X : ℕ → Ω → ℝ} {ℱ : Filtration ℕ mΩ}

omit [IsFiniteMeasure μ] in

theorem stronglyMeasurable_centered_increment_of_measurable (j : ℕ)
    (hj : StronglyMeasurable[ℱ j] (X j))
    (hj1 : StronglyMeasurable[ℱ (j + 1)] (X (j + 1))) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω ↦ X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) := by
  exact (hj1.sub (hj.mono (ℱ.mono (Nat.le_succ j)))).sub
    (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ j)))

theorem sum_centered_increments_eq (X : ℕ → Ω → ℝ) (ℱ : Filtration ℕ mΩ)
    (μ : Measure Ω) (t : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range t, (X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω)) =
    X t ω - X 0 ω - ∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j ↦ X j ω)]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SubGaussianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {c : ℝ≥0}

lemma subGaussian_abs_tail [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * c)) := by
  have hset : {ω | u ≤ |X ω|} = {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [le_abs]
  rw [hset]
  calc
    μ.real ({ω | u ≤ X ω} ∪ {ω | u ≤ -X ω}) ≤
        μ.real {ω | u ≤ X ω} + μ.real {ω | u ≤ -X ω} := measureReal_union_le _ _
    _ ≤ exp (-u ^ 2 / (2 * c)) + exp (-u ^ 2 / (2 * c)) :=
      add_le_add (h.measure_ge_le hu) (h.neg.measure_ge_le hu)
    _ = _ := by ring

lemma subGaussian_mono_parameter (h : HasSubgaussianMGF X c μ)
    {d : ℝ≥0} (hcd : c ≤ d) : HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le θ := (h.mgf_le θ).trans (by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (c : ℝ) ≤ d from hcd) (sq_nonneg θ))
      (by norm_num))

lemma subGaussian_abs_tail_of_parameter_le [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {v u : ℝ} (hv : 0 ≤ v)
    (hcv : (c : ℝ) ≤ v) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * v)) := by
  exact subGaussian_abs_tail
    (subGaussian_mono_parameter h (d := ⟨v, hv⟩) hcv) hu

lemma subGaussian_abs_tail_horizon [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {t T : ℕ} (htT : t ≤ T)
    {L u : ℝ} (hct : (c : ℝ) ≤ 4 * t * L ^ 2) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (8 * T * L ^ 2)) := by
  have hv : 0 ≤ 4 * (T : ℝ) * L ^ 2 := by positivity
  have hcv : (c : ℝ) ≤ 4 * (T : ℝ) * L ^ 2 := hct.trans (by
    gcongr)
  have hb := subGaussian_abs_tail_of_parameter_le h hv hcv hu
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BoundedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace Balanced
open scoped _root_.Balanced

universe u

theorem boundedDriftConcentration_proof : BoundedDriftConcentration.{u} := by
  intro Ω mΩ μ hμ ℱ X T L hT hL hX hbound u hu t ht
  let Y : ℕ → Ω → ℝ := fun j ω ↦ X (j + 1) ω - X j ω -
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω
  have hmeas (j : ℕ) (hj : j < t) : StronglyMeasurable[ℱ (j + 1)] (Y j) := by
    exact stronglyMeasurable_centered_increment_of_measurable j
      (hX j (by omega)) (hX (j + 1) (by omega))
  have hb (j : ℕ) (hj : j < t) : ∀ᵐ ω ∂μ, |Y j ω| ≤ 2 * L :=
    abs_sub_condExp_le (hbound j (by omega))
  have hz (j : ℕ) (hj : j < t) : μ[Y j | ℱ j] =ᵐ[μ] 0 := by
    apply condExp_sub_condExp_eq_zero (ℱ.le j)
    apply integrable_of_abs_le
      ((((hX (j + 1) (by omega)).mono (ℱ.le (j + 1))).sub
        ((hX j (by omega)).mono (ℱ.le j))).measurable.aemeasurable)
      (hbound j (by omega))
  have hmgf := subGaussian_sum_of_bounded_differences
    (μ := μ) (ℱ := ℱ) (Y := Y) (by positivity : 0 < 2 * L) t hmeas hb hz
  have hp : (((t : ℝ≥0) * ⟨(2 * L) ^ 2, sq_nonneg (2 * L)⟩ : ℝ≥0) : ℝ)
      ≤ 4 * (t : ℝ) * L ^ 2 := by
    change (t : ℝ) * (2 * L) ^ 2 ≤ 4 * (t : ℝ) * L ^ 2
    nlinarith
  have htail := subGaussian_abs_tail_horizon hmgf ht hp hu.le
  simpa only [Y, sum_centered_increments_eq] using htail

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_DistinctRoleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal Classical

namespace Balanced.DistinctRole

variable {D F : Type*} [Field F]

variable [Fintype D] [Fintype F]

instance distinctNonempty :
    Nonempty {M : D → Bool → F // ∀ d, M d false ≠ M d true} :=
  ⟨⟨fun _ b => if b then 0 else 1, by simp⟩⟩

end Balanced.DistinctRole

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistory
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma measurable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ) :
    Measurable (stepObservable n f) := by
  have hm : Measurable (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  exact (measurable_of_countable (Function.uncurry f)).comp hm

lemma integrable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ)
    (ν : Measure (Path S)) [IsFiniteMeasure ν] : Integrable (stepObservable n f) ν := by
  have hmap : Measurable (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hi : Integrable (Function.uncurry f)
      (ν.map (fun ω : Path S => (frestrictLe n ω, ω (n + 1)))) := .of_finite
  exact hi.comp_measurable hmap

lemma map_next_traj (step : ℕ → S → PMF S) (n : ℕ) (h : Prefix S n) :
    (Kernel.traj (X := fun _ => S) (historyKernel step) n h).map (fun ω : Path S => ω (n + 1)) =
      (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure := by
  rw [← Kernel.map_apply _ (measurable_pi_apply (n + 1)), Kernel.map_traj_succ_self]
  rfl

lemma integral_stepObservable_traj (step : ℕ → S → PMF S) (n : ℕ)
    (h : Prefix S n) (f : Prefix S n → S → ℝ) :
    (∫ ω, stepObservable n f ω ∂Kernel.traj (X := fun _ => S) (historyKernel step) n h) =
      ∑ s, (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) s).toReal * f h s := by
  rw [Kernel.integral_traj h (measurable_stepObservable n f).stronglyMeasurable.aestronglyMeasurable]
  have hfreeze (ω : Path S) :
      stepObservable n f (Function.updateFinset ω (Finset.Iic n) h) = f h (ω (n + 1)) := by
    have hp : frestrictLe n (Function.updateFinset ω (Finset.Iic n) h) = h := by
      funext j
      simp [frestrictLe, Function.updateFinset, j.property]
    simp [stepObservable, hp, Function.updateFinset]
  simp_rw [hfreeze]
  rw [← integral_map (measurable_pi_apply (n + 1)).aemeasurable
    (measurable_of_countable (f h)).stronglyMeasurable.aestronglyMeasurable,
    map_next_traj, PMF.integral_eq_sum]
  rfl

theorem condExp_stepObservable (step : ℕ → S → PMF S) (s₀ : S)
    (n : ℕ) (f : Prefix S n → S → ℝ) :
    (pathLaw step s₀)[stepObservable n f | filtration n] =ᵐ[pathLaw step s₀]
      fun ω => ∑ s, (step n (ω n) s).toReal * f (frestrictLe n ω) s := by
  have h := Kernel.condExp_traj (X := fun _ => S) (κ := historyKernel step) (Nat.zero_le n)
    (x₀ := fun _ => s₀) (integrable_stepObservable n f (pathLaw step s₀))
  filter_upwards [h] with ω hω
  change (pathLaw step s₀)[stepObservable n f | filtration n] ω = _ at hω ⊢
  rw [hω, integral_stepObservable_traj]
  rfl

theorem map_prefix_pathLaw (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    (pathLaw step s₀).map (frestrictLe n) =
      Kernel.partialTraj (X := fun _ => S) (historyKernel step) 0 n (fun _ => s₀) :=
  Kernel.traj_map_frestrictLe_apply (X := fun _ => S) (κ := historyKernel step) 0 n (fun _ => s₀)

theorem map_prefix_next_pathLaw (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    (pathLaw step s₀).map (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) =
      ((pathLaw step s₀).map (frestrictLe n)) ⊗ₘ historyKernel step n := by
  rw [map_prefix_pathLaw]
  exact (Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => S) (κ := historyKernel step) (x₀ := fun _ => s₀) (Nat.zero_le n)).symm

end Balanced.FiniteHistory

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistoryAdditive
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem stronglyMeasurable_prefix (n : ℕ) (f : Prefix S n → ℝ) :
    StronglyMeasurable[filtration n] (fun ω : Path S => f (frestrictLe n ω)) := by
  apply Measurable.stronglyMeasurable
  change Measurable[Filtration.piLE n] _
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_countable f).comp (comap_measurable _)

theorem stronglyMeasurable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ) :
    StronglyMeasurable[filtration (n + 1)] (stepObservable n f) := by
  let g : Prefix S (n + 1) → ℝ := fun h =>
    f (fun i => h ⟨i.1, Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp i.2; omega)⟩)
      (h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
  exact stronglyMeasurable_prefix (n + 1) g

theorem stronglyMeasurable_additiveTrack (x₀ : ℝ)
    (f : (n : ℕ) → Prefix S n → S → ℝ) (t : ℕ) :
    StronglyMeasurable[filtration t] (additiveTrack x₀ f t) := by
  apply StronglyMeasurable.add stronglyMeasurable_const
  have hs := Finset.stronglyMeasurable_sum (Finset.range t) (fun j hj =>
    (stronglyMeasurable_stepObservable j (f j)).mono
      (filtration.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))))
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  simp only [Finset.sum_apply]

theorem condExp_additiveTrack_increment (step : ℕ → S → PMF S) (s₀ : S)
    (x₀ : ℝ) (f : (n : ℕ) → Prefix S n → S → ℝ) (t : ℕ) :
    (pathLaw step s₀)[fun ω => additiveTrack x₀ f (t + 1) ω -
      additiveTrack x₀ f t ω | filtration t] =ᵐ[pathLaw step s₀]
      fun ω => ∑ s, (step t (ω t) s).toReal * f t (frestrictLe t ω) s := by
  simpa only [additiveTrack_increment] using condExp_stepObservable step s₀ t (f t)

theorem additiveTrack_drift_nonnegative (step : ℕ → S → PMF S) (s₀ : S)
    (x₀ : ℝ) (f : (n : ℕ) → Prefix S n → S → ℝ) (T : ℕ)
    (hmean : ∀ t < T, ∀ h : Prefix S t,
      0 ≤ ∑ s, (step t (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) s).toReal * f t h s) :
    ∀ t ≤ T, ∀ᵐ ω ∂pathLaw step s₀,
      0 ≤ ∑ j ∈ Finset.range t,
        (pathLaw step s₀)[fun ω => additiveTrack x₀ f (j + 1) ω -
          additiveTrack x₀ f j ω | filtration j] ω := by
  intro t ht
  have hall := ae_all_iff.2 (fun j => condExp_additiveTrack_increment step s₀ x₀ f j)
  filter_upwards [hall] with ω hω
  apply Finset.sum_nonneg
  intro j hj
  rw [hω j]
  exact hmean j (lt_of_lt_of_le (Finset.mem_range.mp hj) ht) (frestrictLe j ω)

theorem additiveTrack_lower_tail (step : ℕ → S → PMF S) (s₀ : S)
    (x₀ : ℝ) (f : (n : ℕ) → Prefix S n → S → ℝ) (T : ℕ) (L : ℝ)
    (hT : 1 ≤ T) (hL : 0 < L)
    (hbound : ∀ j < T, ∀ h s, |f j h s| ≤ L)
    (hmean : ∀ j < T, ∀ h : Prefix S j,
      0 ≤ ∑ s, (step j (h ⟨j, Finset.mem_Iic.mpr le_rfl⟩) s).toReal * f j h s)
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ T) :
    (pathLaw step s₀).real {ω | additiveTrack x₀ f t ω ≤ x₀ - u} ≤
      2 * Real.exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  have hc := boundedDriftConcentration_proof (pathLaw step s₀) filtration
    (additiveTrack x₀ f) T L hT hL
    (fun j _ => stronglyMeasurable_additiveTrack x₀ f j)
    (fun j hj => Filter.Eventually.of_forall (fun ω => by
      simpa only [additiveTrack_increment, stepObservable] using hbound j hj (frestrictLe j ω) (ω (j + 1))))
    u hu t ht
  refine le_trans ?_ hc
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [additiveTrack_drift_nonnegative step s₀ x₀ f T hmean t ht]
    with ω hω hbad
  change additiveTrack x₀ f t ω ≤ x₀ - u at hbad
  simp only [additiveTrack_zero]
  have hneg : u ≤ -(additiveTrack x₀ f t ω - x₀ -
      ∑ j ∈ Finset.range t, (pathLaw step s₀)[fun ω =>
        additiveTrack x₀ f (j + 1) ω - additiveTrack x₀ f j ω | filtration j] ω) := by
    linarith
  exact hneg.trans (neg_le_abs _)

end Balanced.FiniteHistory

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistoryInvariant
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter Finset Preorder
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

theorem ae_pmf_nonzero (p : PMF S) : ∀ᵐ s ∂p.toMeasure, p s ≠ 0 := by
  rw [ae_iff]
  change p.toMeasure p.supportᶜ = 0
  exact (p.toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete).2
    disjoint_compl_right

theorem ae_initial_state (step : ℕ → S → PMF S) (s₀ : S) :
    ∀ᵐ ω ∂pathLaw step s₀, ω 0 = s₀ := by
  have hp : (pathLaw step s₀).map (frestrictLe 0) =
      Measure.dirac (fun _ : Iic 0 ↦ s₀) := by
    rw [map_prefix_pathLaw, Kernel.partialTraj_self, Kernel.id_apply]
  have hi : ∀ᵐ h ∂(pathLaw step s₀).map (frestrictLe 0),
      h ⟨0, mem_Iic.mpr le_rfl⟩ = s₀ := by
    rw [hp]
    exact (ae_dirac_iff MeasurableSet.of_discrete).2 rfl
  exact ae_of_ae_map (by fun_prop) hi

theorem ae_step_support (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    ∀ᵐ ω ∂pathLaw step s₀, step n (ω n) (ω (n + 1)) ≠ 0 := by
  have hp : ∀ᵐ z ∂((pathLaw step s₀).map (frestrictLe n)) ⊗ₘ historyKernel step n,
      step n (z.1 ⟨n, mem_Iic.mpr le_rfl⟩) z.2 ≠ 0 := by
    apply Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete
    apply Eventually.of_forall
    intro h
    exact ae_pmf_nonzero (step n (h ⟨n, mem_Iic.mpr le_rfl⟩))
  rw [← map_prefix_next_pathLaw] at hp
  exact ae_of_ae_map (f := fun ω : Path S ↦ (frestrictLe n ω, ω (n + 1)))
    (by fun_prop) hp

end Balanced.FiniteHistory

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternExposureBoundary
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

@[simp] theorem count_eq_zero_of_isEmpty [IsEmpty P.Label] (ω : P.Sample) :
    P.count ω = 0 := by
  simp [count]

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailProductBounds
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TailProduct

open scoped BigOperators

theorem neg_log_one_sub_le_twice {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hp : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    apply (sub_le_iff_le_add).2
    apply (inv_le_iff_one_le_mul₀ hp).2
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hl
  exact hl.trans hi

end Balanced.TailProduct

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessLaw
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSingletonClass _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSpace _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem transitionWeight_eq_draw_pushforward (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Option (State I V)) :
    transitionWeight p q t G before out =
      ∑ draw, if advance q G before draw = out then drawStepWeight p q t G before draw else 0 := by
  cases before with
  | none =>
    by_cases ho : out = none <;> simp [transitionWeight, advance, drawStepWeight, ho, eq_comm]
  | some S =>
    by_cases hp : Precheck p q t G S
    · simp [transitionWeight, stepWeight, drawStepWeight, advance, hp, Fintype.sum_option]
    · by_cases ho : out = none <;>
        simp [transitionWeight, stepWeight, drawStepWeight, advance, hp, ho, Fintype.sum_option, eq_comm]

theorem snapshotPMF_apply_real (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) :
    (snapshotPMF p q t G before out).toReal = snapshotWeight p q t G before out :=
  ENNReal.toReal_ofReal (snapshotWeight_nonnegative p q t G before out)

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistory
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem condExp_snapshot_step (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → Snapshot I V → ℝ) :
    (snapshotPathLaw p q G)[FiniteHistory.stepObservable t f | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ out, snapshotWeight p q t G (ω t) out * f (frestrictLe t ω) out := by
  have h := FiniteHistory.condExp_stepObservable
    (fun n => snapshotPMF p q n G) (initialSnapshot (I := I) (V := V)) t f
  simpa only [snapshotPathLaw, snapshotFiltration, snapshotPMF_apply_real] using h

theorem sum_snapshotWeight_response (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) (f : Snapshot I V → ℝ) :
    (∑ out, snapshotWeight p q t G before out * f out) =
      ∑ draw, drawStepWeight p q t G before.1 draw *
        f (advance q G before.1 draw, draw) := by
  simp only [Snapshot, Fintype.sum_prod_type, snapshotWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro draw _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_drawStepWeight_of_precheck (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (f : Option (Noise I V) → ℝ) :
    (∑ draw, drawStepWeight p q t G (some S) draw * f draw) =
      ∑ r : Noise I V, noiseWeight p q G S r * f (some r) := by
  simp [Fintype.sum_option, drawStepWeight, hp]

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionState
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSingletonClass _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSpace _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

private theorem exists_positive_of_sum_positive {α : Type*} [Fintype α]
    (f : α → ℝ) (h : 0 < ∑ a, f a) : ∃ a, 0 < f a := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (Finset.sum_nonpos (fun a _ => hn a))) h

theorem positive_stepWeight_exists_update (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V)
    (hpos : 0 < stepWeight p q t G S (some S')) :
    ∃ r : Noise I V, r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 ∧
      update G S r.1 r.2.1 r.2.2 = S' := by
  by_cases hp : Precheck p q t G S
  · simp only [stepWeight, hp, ite_true] at hpos
    obtain ⟨r, hr⟩ := exists_positive_of_sum_positive _ hpos
    split at hr
    · rename_i hresult
      have hvalid : r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 := by
        by_contra h
        simp only [noiseWeight, drawWeight, h, ite_false, zero_mul, lt_self_iff_false] at hr
      have hup : update G S r.1 r.2.1 r.2.2 = S' := by
        unfold performedResult at hresult
        split at hresult
        · exact Option.some.inj hresult
        · contradiction
      exact ⟨r, hvalid.1, hvalid.2, hup⟩
    · exact False.elim (lt_irrefl 0 hr)
  · simp [stepWeight, hp] at hpos

theorem positive_stepWeight_card (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (hpos : 0 < stepWeight p q t G S (some S')) :
    S'.remaining.card + 1 = S.remaining.card := by
  obtain ⟨r, hi, _, hup⟩ := positive_stepWeight_exists_update p q t G S S' hpos
  rw [← hup]
  exact Finset.card_erase_add_one hi

theorem positive_historyWeight_card_add_time (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (S : State I V) (hpos : 0 < historyWeight p q G t (some S)) :
    S.remaining.card + t = Fintype.card I := by
  induction t generalizing S with
  | zero =>
    simp only [historyWeight] at hpos
    split at hpos
    · rename_i h
      have heq : S = initialState := Option.some.inj h
      simp [heq, initialState]
    · exact False.elim (lt_irrefl 0 hpos)
  | succ t ih =>
    simp only [historyWeight] at hpos
    obtain ⟨before, hb⟩ := exists_positive_of_sum_positive _ hpos
    have hweights := (mul_pos_iff.mp hb).resolve_right (by
      intro hneg
      exact (not_lt_of_ge (historyWeight_nonnegative p q G t before)) hneg.1)
    cases before with
    | none => simp [transitionWeight] at hweights
    | some S₀ =>
      have hc := positive_stepWeight_card p q t G S₀ S hweights.2
      have ht := ih S₀ hweights.1
      omega

theorem positive_historyWeight_card (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (S : State I V) (hpos : 0 < historyWeight p q G t (some S)) :
    S.remaining.card = Fintype.card I - t := by
  have h := positive_historyWeight_card_add_time p q G t S hpos
  omega

theorem sum_snapshotWeight_state (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) (out : Option (State I V)) :
    (∑ draw, snapshotWeight p q t G before (out, draw)) =
      transitionWeight p q t G before.1 out := by
  rw [transitionWeight_eq_draw_pushforward]
  apply Finset.sum_congr rfl
  intro draw _
  simp only [snapshotWeight, eq_comm]

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionScales
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.SelectionScales

private theorem rate_bounds {P : ℝ} {q : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    0 ≤ P / q ∧ P / q ≤ 1 / 2 := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  constructor
  · exact div_nonneg hP hqR.le
  · apply (div_le_iff₀ hqR).2
    linarith

theorem domain_bounds {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) (ht : t ≤ 3 * q) :
    Real.exp (-6 * P) ≤ domain P q t ∧ domain P q t ≤ 1 := by
  obtain ⟨hx, hxhalf⟩ := rate_bounds hP hq hPq
  have hbase : 0 < 1 - P / q := by linarith
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have htR : (t : ℝ) ≤ 3 * q := by exact_mod_cast ht
  constructor
  · rw [domain, ← Real.exp_log (pow_pos hbase t)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    have hlog := Balanced.TailProduct.neg_log_one_sub_le_twice hx hxhalf
    have hmul := mul_le_mul_of_nonneg_left (show -2 * (P / q) ≤
        Real.log (1 - P / q) by linarith) (Nat.cast_nonneg t)
    have htime := mul_le_mul_of_nonpos_right htR (show -2 * (P / q) ≤ 0 by linarith)
    have heq : (3 * (q : ℝ)) * (-2 * (P / q)) = -6 * P := by
      field_simp
      ring
    rw [heq] at htime
    exact htime.trans hmul
  · exact pow_le_one₀ hbase.le (by linarith) (n := t)

end Balanced.SelectionScales

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessScales
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process.Parameters

noncomputable section

variable {p : Parameters}

theorem a_bounds (hp : p.Admissible) : 0 < p.a ∧ p.a < 1 := by
  exact ⟨hp.2.2.2.2.1, lt_of_lt_of_le hp.2.2.2.2.2 (min_le_left _ _)⟩

theorem tailSlots_le_order (hp : p.Admissible) (q : ℕ) : p.tailSlots q ≤ q := by
  unfold tailSlots
  apply Nat.ceil_le.mpr
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith [(a_bounds hp).2]

theorem eventually_scale_regime (p : Parameters) :
    ∀ᶠ q : ℕ in Filter.atTop, 2 ≤ q ∧ 2 * p.Pstar ≤ q := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * p.Pstar)
  apply Filter.eventually_atTop.mpr
  refine ⟨max 2 N, fun q hq => ?_⟩
  constructor
  · exact (le_max_left _ _).trans hq
  · have hNq : N ≤ q := (le_max_right _ _).trans hq
    exact hN.trans (by exact_mod_cast hNq)

theorem rho_pos (hp : p.Admissible) : 0 < p.rho := by
  exact div_pos (mul_pos hp.2.2.1 (Real.exp_pos _)) (by norm_num)

theorem tailSlots_le_rho_mul (hp : p.Admissible) {q : ℕ}
    (hq : 2 ≤ p.rho * q) : ((p.tailSlots q : ℕ) : ℝ) ≤ p.rho * q := by
  have ha : 0 < p.a := (a_bounds hp).1
  have harho : p.a < p.rho / 2 := (lt_min_iff.mp (lt_min_iff.mp hp.2.2.2.2.2).2).1
  have hceil := Nat.ceil_lt_add_one (mul_nonneg ha.le (Nat.cast_nonneg q))
  have hmul := mul_le_mul_of_nonneg_right harho.le (Nat.cast_nonneg q)
  change (Nat.ceil (p.a * q) : ℝ) ≤ p.rho * q
  nlinarith

theorem eventually_occupancy_regime (hp : p.Admissible) :
    ∀ᶠ q : ℕ in Filter.atTop, 0 < q ∧ 2 * p.Bstar ≤ q ∧ 2 ≤ p.rho * q := by
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (2 * p.Bstar)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (2 / p.rho)
  apply Filter.eventually_atTop.mpr
  refine ⟨max 1 (max N₁ N₂), fun q hq => ?_⟩
  have hqone : 1 ≤ q := (le_max_left _ _).trans hq
  have h₁ : N₁ ≤ q := (le_max_left N₁ N₂).trans ((le_max_right _ _).trans hq)
  have h₂ : N₂ ≤ q := (le_max_right N₁ N₂).trans ((le_max_right _ _).trans hq)
  refine ⟨hqone, hN₁.trans (by exact_mod_cast h₁), ?_⟩
  have hdiv : 2 / p.rho ≤ (q : ℝ) := hN₂.trans (by exact_mod_cast h₂)
  have hmul := (div_le_iff₀ (rho_pos hp)).1 hdiv
  simpa only [mul_comm] using hmul

end
end Balanced.Selection.Process.Parameters

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailCompletion
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.Tail

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in

theorem complete_agrees_recorded (G : Input I V) (S : State I V) (fixed : I → V)
    (hprefix : ∀ i ∉ S.remaining, S.recorded i = some (fixed i))
    (a : Slots.Assignment (Domain G S)) (i : I) (hi : i ∉ S.remaining) :
    S.recorded i = some (complete G S fixed a i) := by
  rw [complete_recorded G S fixed a i hi]
  exact hprefix i hi

end Balanced.Selection.Process.Tail

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFinalLaw
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

section Nonempty
variable [Nonempty V]

theorem occupancyFailureMass_finalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) (ρ : ℝ) :
    occupancyFailureMass (finalLaw p q G hno) A line T ρ =
      ∑ out, mainStageWeight p q G out *
        occupancyFailureMass (sourceTerminalOutcomeLaw p q G hno out) A line T ρ := by
  unfold occupancyFailureMass finalLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

end Nonempty

theorem graphBounds_vertex_nonempty (G : Input I V) (q : ℕ) (c C : ℝ)
    (hc : 0 < c) (hq : 0 < q) (hG : GraphBounds G q c C) : Nonempty V := by
  have hi : 0 < Fintype.card I := by rw [hG.1]; omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hi
  have hs : 0 < ((slotVertices G i).card : ℝ) :=
    (mul_pos hc (by exact_mod_cast hq)).trans_le (hG.2.2.1 i).1
  have hn : (slotVertices G i).Nonempty := Finset.card_pos.mp (by exact_mod_cast hs)
  obtain ⟨v, _⟩ := hn
  exact ⟨v⟩

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistoryMarginal
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem integrable_stateObservable (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (f : Option (State I V) → ℝ) :
    Integrable (fun ω => f (ω t).1) (snapshotPathLaw p q G) := by
  have hi : Integrable (fun s : Snapshot I V => f s.1)
      ((snapshotPathLaw p q G).map (fun ω => ω t)) := .of_finite
  exact hi.comp_measurable (measurable_pi_apply t)

theorem sum_snapshotWeight_stateObservable (p : Parameters) (q t : ℕ)
    (G : Input I V) (before : Snapshot I V) (f : Option (State I V) → ℝ) :
    (∑ out, snapshotWeight p q t G before out * f out.1) =
      ∑ out, transitionWeight p q t G before.1 out * f out := by
  simp only [Snapshot, Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, sum_snapshotWeight_state]

theorem integral_stateObservable_eq_historyWeight (p : Parameters) (q : ℕ)
    (G : Input I V) (t : ℕ) (f : Option (State I V) → ℝ) :
    (∫ ω, f (ω t).1 ∂snapshotPathLaw p q G) =
      ∑ out, historyWeight p q G t out * f out := by
  induction t generalizing f with
  | zero =>
    have hi := FiniteHistory.ae_initial_state
      (fun t => snapshotPMF p q t G) (initialSnapshot (I := I) (V := V))
    have heq : (fun ω => f (ω 0).1) =ᵐ[snapshotPathLaw p q G]
        fun _ => f (some initialState) := by
      filter_upwards [hi] with ω hω
      simp only [hω, initialSnapshot]
    rw [integral_congr_ae heq]
    simp [historyWeight]
  | succ t ih =>
    have hce := condExp_snapshot_step p q G t (fun _ out => f out.1)
    have hce' : (snapshotPathLaw p q G)[
        (fun ω => f (ω (t + 1)).1) | snapshotFiltration t]
        =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ out, transitionWeight p q t G (ω t).1 out * f out := by
      change (snapshotPathLaw p q G)[
        (fun ω => f (ω (t + 1)).1) | snapshotFiltration t] =ᵐ[snapshotPathLaw p q G] _ at hce
      simpa only [sum_snapshotWeight_stateObservable] using hce
    calc
      (∫ ω, f (ω (t + 1)).1 ∂snapshotPathLaw p q G) =
          ∫ ω, ((snapshotPathLaw p q G)[
            (fun ω => f (ω (t + 1)).1) | snapshotFiltration t]) ω
              ∂snapshotPathLaw p q G :=
        (integral_condExp (snapshotFiltration.le t)).symm
      _ = ∫ ω, (∑ out, transitionWeight p q t G (ω t).1 out * f out)
          ∂snapshotPathLaw p q G := integral_congr_ae hce'
      _ = ∑ out, ∫ ω, transitionWeight p q t G (ω t).1 out * f out
          ∂snapshotPathLaw p q G :=
        integral_finsetSum _ (fun out _ =>
          integrable_stateObservable p q G t (fun s => transitionWeight p q t G s out * f out))
      _ = ∑ out, ∑ before, historyWeight p q G t before *
          (transitionWeight p q t G before out * f out) := by
        apply Finset.sum_congr rfl
        intro out _
        exact ih (fun before => transitionWeight p q t G before out * f out)
      _ = ∑ out, historyWeight p q G (t + 1) out * f out := by
        simp only [historyWeight, Finset.sum_mul, mul_assoc]

theorem state_event_real_eq_historyWeight (p : Parameters) (q : ℕ)
    (G : Input I V) (t : ℕ) (A : Set (Option (State I V))) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ∈ A} =
      ∑ out, if out ∈ A then historyWeight p q G t out else 0 := by
  have hm : MeasurableSet {ω : FiniteHistory.Path (Snapshot I V) | (ω t).1 ∈ A} :=
    (show MeasurableSet {s : Snapshot I V | s.1 ∈ A} from .of_discrete).preimage
      (measurable_pi_apply t)
  rw [← integral_indicator_one hm]
  have h := integral_stateObservable_eq_historyWeight p q G t
    (fun out => if out ∈ A then 1 else 0)
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, mul_ite,
    mul_one, mul_zero] using h

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancy2
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P V I : Type*}

theorem card_hits_le (Q : Finset V) (T : Finset P) (R : P → V → Prop)
    (hunique : ∀ p ∈ T, ∀ v ∈ Q, ∀ w ∈ Q, R p v → R p w → v = w) :
    (hits Q T R).card ≤ T.card := by
  classical
  have hsub : hits Q T R ⊆ T.biUnion (fun p => Q.filter (R p)) := by
    intro v hv
    obtain ⟨hvQ, p, hpT, hpv⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_biUnion.mpr ⟨p, hpT, Finset.mem_filter.mpr ⟨hvQ, hpv⟩⟩
  have hcard : ∀ p ∈ T, (Q.filter (R p)).card ≤ 1 := by
    intro p hp
    apply Finset.card_le_one.mpr
    intro v hv w hw
    exact hunique p hp v (Finset.mem_filter.mp hv).1 w (Finset.mem_filter.mp hw).1
      (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2
  simpa using (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le_card_mul T (fun p => Q.filter (R p)) 1 hcard)

theorem average_hit_indicator (slots : Finset I) (Q : I → Finset V)
    (T : Finset P) (R : I → P → V → Prop) :
    average slots Q (fun i v => if ∃ p ∈ T, R i p v then 1 else 0) =
      hitProbability slots Q T R := by
  unfold average hitProbability hits
  simp only [Finset.sum_boole]

theorem hitProbability_le (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (T : Finset P) (R : I → P → V → Prop)
    (L : ℝ) (hL : 0 < L)
    (hsize : ∀ i ∈ slots, L ≤ ((Q i).card : ℝ))
    (hunique : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      R i p v → R i p w → v = w) :
    hitProbability slots Q T R ≤ (T.card : ℝ) / L := by
  have hcard : (0 : ℝ) < slots.card := by
    exact_mod_cast Finset.card_pos.mpr hslots
  unfold hitProbability
  apply (div_le_iff₀ hcard).2
  calc
    (∑ i ∈ slots, ((hits (Q i) T (R i)).card : ℝ) / (Q i).card) ≤
        ∑ _i ∈ slots, (T.card : ℝ) / L := by
      apply Finset.sum_le_sum
      intro i hi
      exact div_le_div₀ (Nat.cast_nonneg T.card)
        (by exact_mod_cast card_hits_le (Q i) T (R i) (hunique i hi)) hL (hsize i hi)
    _ = (T.card : ℝ) / L * slots.card := by simp [mul_comm]

theorem average_const (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (hQ : ∀ i ∈ slots, (Q i).Nonempty) (c : ℝ) :
    average slots Q (fun _ _ => c) = c := by
  have hI : (slots.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hslots).ne'
  unfold average
  have hinner : ∀ i ∈ slots, (∑ _v ∈ Q i, c) / ((Q i).card : ℝ) = c := by
    intro i hi
    have hiQ : ((Q i).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (hQ i hi)).ne'
    simp [hiQ]
  rw [Finset.sum_congr rfl hinner]
  simp [hI]

theorem average_sub (slots : Finset I) (Q : I → Finset V) (f g : I → V → ℝ) :
    average slots Q (fun i v => f i v - g i v) =
      average slots Q f - average slots Q g := by
  simp only [average, Finset.sum_sub_distrib, sub_div]

theorem remaining_card (T : Finset P) (R : P → V → Prop) (v : V)
    (hsmall : (T.filter (fun p => R p v)).card ≤ 1) :
    ((T.filter (fun p => ¬ R p v)).card : ℝ) =
      (T.card : ℝ) - if ∃ p ∈ T, R p v then 1 else 0 := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := T) (fun p => R p v)
  by_cases hhit : ∃ p ∈ T, R p v
  · have hpos : 0 < (T.filter (fun p => R p v)).card := by
      apply Finset.card_pos.mpr
      obtain ⟨p, hp, hpv⟩ := hhit
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpv⟩⟩
    have hone : (T.filter (fun p => R p v)).card = 1 := by omega
    have hsumR : (1 : ℝ) + ((T.filter (fun p => ¬ R p v)).card : ℝ) = T.card := by
      exact_mod_cast (hone ▸ hsum)
    simp only [ite_eq_left hhit]
    linarith
  · have hzero : (T.filter (fun p => R p v)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hhit ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    have heq : (T.filter (fun p => ¬ R p v)).card = T.card := by omega
    simp [hhit, heq]

theorem average_remaining_eq (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (hQ : ∀ i ∈ slots, (Q i).Nonempty)
    (T : Finset P) (R : I → P → V → Prop)
    (hsmall : ∀ i ∈ slots, ∀ v ∈ Q i, (T.filter (fun p => R i p v)).card ≤ 1) :
    average slots Q (fun i v => ((T.filter (fun p => ¬ R i p v)).card : ℝ)) =
      (T.card : ℝ) - hitProbability slots Q T R := by
  have heq : average slots Q (fun i v => ((T.filter (fun p => ¬ R i p v)).card : ℝ)) =
      average slots Q (fun i v => (T.card : ℝ) - if ∃ p ∈ T, R i p v then 1 else 0) := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    exact remaining_card T (R i) v (hsmall i hi v hv)
  rw [heq, average_sub, average_const slots hslots Q hQ, average_hit_indicator]

theorem average_remaining_ge (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (T : Finset P) (R : I → P → V → Prop)
    (L : ℝ) (hL : 0 < L)
    (hsize : ∀ i ∈ slots, L ≤ ((Q i).card : ℝ))
    (hunique : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      R i p v → R i p w → v = w)
    (hsmall : ∀ i ∈ slots, ∀ v ∈ Q i, (T.filter (fun p => R i p v)).card ≤ 1) :
    (1 - L⁻¹) * (T.card : ℝ) ≤
      average slots Q (fun i v => ((T.filter (fun p => ¬ R i p v)).card : ℝ)) := by
  have hQ : ∀ i ∈ slots, (Q i).Nonempty := by
    intro i hi
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (Q i).card := hL.trans_le (hsize i hi)
    exact_mod_cast this
  rw [average_remaining_eq slots hslots Q hQ T R hsmall]
  have hhit := hitProbability_le slots hslots Q T R L hL hsize hunique
  rw [div_eq_mul_inv] at hhit
  nlinarith

theorem average_remaining_ge_ratio (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (T : Finset P) (R : I → P → V → Prop)
    (q B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ slots, q / B ≤ ((Q i).card : ℝ))
    (hunique : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      R i p v → R i p w → v = w)
    (hsmall : ∀ i ∈ slots, ∀ v ∈ Q i, (T.filter (fun p => R i p v)).card ≤ 1) :
    (1 - B / q) * (T.card : ℝ) ≤
      average slots Q (fun i v => ((T.filter (fun p => ¬ R i p v)).card : ℝ)) := by
  simpa only [inv_div] using
    average_remaining_ge slots hslots Q T R (q / B) (div_pos hq hB) hsize hunique hsmall

theorem rescaled_increment_abs_le {t t' c a b d L M : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 < a) (hb : b = c * a)
    (hd : 0 < d) (hdb : d ≤ b) (ht : 0 ≤ t) (htM : t ≤ M)
    (hL : 0 ≤ L) (hjump : |t' - t| ≤ L) :
    |t' / b - t / a| ≤ (L + (1 - c) * M) / d := by
  have hbpos : 0 < b := by rw [hb]; positivity
  have hscale : 0 ≤ (1 - c) * t := mul_nonneg (sub_nonneg.mpr hc1) ht
  have hscaleM : (1 - c) * t ≤ (1 - c) * M :=
    mul_le_mul_of_nonneg_left htM (sub_nonneg.mpr hc1)
  have heq : t' / b - t / a = (t' - t + (1 - c) * t) / b := by
    rw [hb]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hbpos]
  apply div_le_div₀ (add_nonneg hL (mul_nonneg (sub_nonneg.mpr hc1) (ht.trans htM)))
    ?_ hd hdb
  calc
    |t' - t + (1 - c) * t| ≤ |t' - t| + |(1 - c) * t| := abs_add_le _ _
    _ = |t' - t| + (1 - c) * t := by rw [abs_of_nonneg hscale]
    _ ≤ L + (1 - c) * M := add_le_add hjump hscaleM

end
end Balanced.SelectionOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_PlaneSelectionOccupancy
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {q : ℕ} {P D L I V : Type*}
variable [Fintype P] [Fintype D] [Fintype L]
variable [DecidableEq P] [DecidableEq I] [DecidableEq V]

omit [DecidableEq P] in
theorem plane_line_eq_of_direction_eq_of_incident
    (A : FiniteAffine.Plane q P D L) {l m : L} {p : P}
    (hd : A.direction l = A.direction m)
    (hl : A.incident p l) (hm : A.incident p m) : l = m := by
  obtain ⟨n, hn, huniq⟩ := A.unique_line_direction p (A.direction m)
  exact (huniq l ⟨hd, hl⟩).trans (huniq m ⟨rfl, hm⟩).symm

theorem plane_common_point_eq_of_lines_ne
    (A : FiniteAffine.Plane q P D L) {l m : L} (hne : l ≠ m)
    {p r : P} (hpl : A.incident p l) (hpm : A.incident p m)
    (hrl : A.incident r l) (hrm : A.incident r m) : p = r := by
  by_contra hpr
  obtain ⟨n, hn, huniq⟩ := A.unique_join p r hpr
  exact hne ((huniq l ⟨hpl, hrl⟩).trans (huniq m ⟨hpm, hrm⟩).symm)

 theorem plane_deletion_card_le_one (A : FiniteAffine.Plane q P D L)
    (T : Finset P) (l m : L) (hT : ∀ p ∈ T, A.incident p l) :
    (T.filter (fun p => m ≠ l ∧ A.incident p m)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp r hr
  obtain ⟨hpT, hne, hpm⟩ := Finset.mem_filter.mp hp
  obtain ⟨hrT, _, hrm⟩ := Finset.mem_filter.mp hr
  exact plane_common_point_eq_of_lines_ne A hne.symm (hT p hpT) hpm (hT r hrT) hrm

omit [DecidableEq I] [DecidableEq V] in
theorem plane_occupancy_drift (A : FiniteAffine.Plane q P D L)
    (slots : Finset I) (hslots : slots.Nonempty) (Q : I → Finset V)
    (lineOf : I → V → L) (direction : I → D)
    (hinj : ∀ i ∈ slots, Set.InjOn (lineOf i) (↑(Q i) : Set V))
    (hdir : ∀ i ∈ slots, ∀ v ∈ Q i, A.direction (lineOf i v) = direction i)
    (l : L) (T : Finset P) (hT : ∀ p ∈ T, A.incident p l)
    (B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ slots, (q : ℝ) / B ≤ ((Q i).card : ℝ)) :
    (1 - B / q) * (T.card : ℝ) ≤
      average slots Q (fun i v => ((afterPlaneLine A T l (lineOf i v)).card : ℝ)) := by
  classical
  have hu : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      lineOf i v ≠ l ∧ A.incident p (lineOf i v) →
      lineOf i w ≠ l ∧ A.incident p (lineOf i w) → v = w := by
    intro i hi p hp v hv w hw hpv hpw
    exact hinj i hi hv hw (plane_line_eq_of_direction_eq_of_incident A
      ((hdir i hi v hv).trans (hdir i hi w hw).symm) hpv.2 hpw.2)
  have hs : ∀ i ∈ slots, ∀ v ∈ Q i,
      (T.filter (fun p => lineOf i v ≠ l ∧ A.incident p (lineOf i v))).card ≤ 1 := by
    intro i hi v hv
    exact plane_deletion_card_le_one A T l (lineOf i v) hT
  have h := average_remaining_ge_ratio slots hslots Q T
    (fun i p v => lineOf i v ≠ l ∧ A.incident p (lineOf i v)) q B
    (by exact_mod_cast hq) hB hsize hu (by
      intro i hi v hv
      convert hs i hi v hv using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext p
      simp)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext i v
  congr 1
  apply congrArg Finset.card
  ext p
  simp [afterPlaneLine]

theorem plane_step_abs_le_one (A : FiniteAffine.Plane q P D L)
    (T : Finset P) (l m : L) (hT : ∀ p ∈ T, A.incident p l) :
    |((afterPlaneLine A T l m).card : ℝ) - (T.card : ℝ)| ≤ 1 := by
  classical
  have hs : (T.filter (fun p => m ≠ l ∧ A.incident p m)).card ≤ 1 := by
    convert plane_deletion_card_le_one A T l m hT using 1
    all_goals try with_reducible_and_instances rfl
  have hc := Finset.card_filter_add_card_filter_not
    (s := T) (fun p => m ≠ l ∧ A.incident p m)
  have heq : afterPlaneLine A T l m =
      T.filter (fun p => ¬ (m ≠ l ∧ A.incident p m)) := by
    ext p
    simp [afterPlaneLine]
  rw [heq]
  have hsub : (T.filter (fun p => ¬ (m ≠ l ∧ A.incident p m))).card ≤ T.card :=
    Finset.card_filter_le _ _
  have hsubR : ((T.filter (fun p => ¬ (m ≠ l ∧ A.incident p m))).card : ℝ) ≤ T.card := by
    exact_mod_cast hsub
  rw [abs_of_nonpos (sub_nonpos.mpr hsubR)]
  have hcR : ((T.filter (fun p => m ≠ l ∧ A.incident p m)).card : ℝ) +
      (T.filter (fun p => ¬ (m ≠ l ∧ A.incident p m))).card = T.card := by
    exact_mod_cast hc
  have hsR : ((T.filter (fun p => m ≠ l ∧ A.incident p m)).card : ℝ) ≤ 1 := by
    exact_mod_cast hs
  linarith

omit [DecidableEq I] [DecidableEq V] in
theorem selection_plane_occupancy_drift [Fintype I] [Fintype V]
    (G : Selection.Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line)
    (slots : Finset I) (hslots : slots.Nonempty) (Q : I → Finset V)
    (hQ : ∀ i ∈ slots, ∀ v ∈ Q i, G.slot v = i)
    (l : L) (T : Finset P) (hT : ∀ p ∈ T, A.incident p l)
    (B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ slots, (q : ℝ) / B ≤ ((Q i).card : ℝ)) :
    (1 - B / q) * (T.card : ℝ) ≤
      average slots Q (fun _ v => ((afterPlaneLine A T l (line v)).card : ℝ)) := by
  apply plane_occupancy_drift A slots hslots Q (fun _ => line)
    (fun i => (index i).1) _ _ l T hT B hq hB hsize
  · intro i hi v hv w hw heq
    exact hline.2 v w ((hQ i hi v hv).trans (hQ i hi w hw).symm) heq
  · intro i hi v hv
    simpa only [hQ i hi v hv] using hline.1 v

end
end Balanced.SelectionOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessOccupancy
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem noise_mean_eq_draw_mean (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (f : I → V → ℝ) :
    (∑ r : Noise I V, noiseWeight p q G S r * f r.1 r.2.1) =
      ∑ i : I, ∑ v : V, drawWeight G S i v * f i v := by
  simp only [Noise, Fintype.sum_prod_type, noiseWeight]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro v hv
  calc
    (∑ flags, drawWeight G S i v * flagsWeight p q G S flags * f i v) =
        ∑ flags, (drawWeight G S i v * f i v) * flagsWeight p q G S flags := by
      apply Finset.sum_congr rfl
      intro flags hflags
      ring
    _ = _ := by rw [← Finset.mul_sum, sum_flagsWeight, mul_one]

theorem draw_mean_eq_average (G : Input I V) (S : State I V) (f : I → V → ℝ) :
    (∑ i : I, ∑ v : V, drawWeight G S i v * f i v) =
      SelectionOccupancy.average S.remaining (domain G S) f := by
  classical
  have hi : ∀ i : I, (∑ v : V, drawWeight G S i v * f i v) =
      if i ∈ S.remaining then
        ((∑ v ∈ domain G S i, f i v) / (domain G S i).card) / S.remaining.card
      else 0 := by
    intro i
    by_cases him : i ∈ S.remaining
    · simp only [drawWeight, him, true_and, ite_true, ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [← Finset.mul_sum]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp [drawWeight, him]
  simp_rw [hi]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact (Finset.sum_div _ _ _).symm

theorem noise_mean_eq_average (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (f : I → V → ℝ) :
    (∑ r : Noise I V, noiseWeight p q G S r * f r.1 r.2.1) =
      SelectionOccupancy.average S.remaining (domain G S) f := by
  rw [noise_mean_eq_draw_mean, draw_mean_eq_average]

theorem performed_occupancy_ge {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V)
    (hp : Precheck p q t G S) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line)
    (l : L) (T : Finset P) (hT : ∀ x ∈ T, A.incident x l)
    (B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ S.remaining, (q : ℝ) / B ≤ ((domain G S i).card : ℝ)) :
    (1 - B / q) * (T.card : ℝ) ≤
      ∑ r : Noise I V, noiseWeight p q G S r *
        ((SelectionOccupancy.afterPlaneLine A T l (line r.2.1)).card : ℝ) := by
  classical
  rw [noise_mean_eq_average p q G S
    (fun _ v => ((SelectionOccupancy.afterPlaneLine A T l (line v)).card : ℝ))]
  apply SelectionOccupancy.selection_plane_occupancy_drift G A index line hline
    S.remaining hp.1 (domain G S) _ l T hT B hq hB hsize
  intro i hi v hv
  exact (Finset.mem_filter.mp hv).2

omit [Fintype I] in
theorem domain_size_ge_q_div_Bstar (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (hc : 0 < p.c)
    (hscale : p.smin ≤ p.sizeScale q t) (i : I) (hi : i ∈ S.remaining) :
    (q : ℝ) / p.Bstar ≤ ((domain G S i).card : ℝ) := by
  have heq : (q : ℝ) / p.Bstar = p.smin * p.c * q / 2 := by
    unfold Parameters.Bstar
    rw [div_div_eq_mul_div]
    ring
  rw [heq]
  apply le_trans _ (hp.2.2.2.1 i hi).2
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hscale hc.le) (Nat.cast_nonneg q)

theorem performed_occupancy_ge_Bstar {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V)
    (hp : Precheck p q t G S) (hc : 0 < p.c) (hq : 0 < q)
    (hscale : p.smin ≤ p.sizeScale q t)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line)
    (l : L) (T : Finset P) (hT : ∀ x ∈ T, A.incident x l) :
    (1 - p.Bstar / q) * (T.card : ℝ) ≤
      ∑ r : Noise I V, noiseWeight p q G S r *
        ((SelectionOccupancy.afterPlaneLine A T l (line r.2.1)).card : ℝ) := by
  have hB : 0 < p.Bstar := by
    unfold Parameters.Bstar Parameters.smin
    positivity
  exact performed_occupancy_ge p q t G S hp A index line hline l T hT p.Bstar hq hB
    (fun i hi => domain_size_ge_q_div_Bstar p q t G S hp hc hscale i hi)

theorem performed_rescaled_occupancy_ge {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V)
    (hp : Precheck p q t G S) (hc : 0 < p.c) (hq : 0 < q)
    (hscale : p.smin ≤ p.sizeScale q t)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line)
    (l : L) (T : Finset P) (hT : ∀ x ∈ T, A.incident x l) :
    (T.card : ℝ) / (1 - p.Bstar / q) ^ t ≤
      ∑ r : Noise I V, noiseWeight p q G S r *
        (((SelectionOccupancy.afterPlaneLine A T l (line r.2.1)).card : ℝ) /
          (1 - p.Bstar / q) ^ (t + 1)) := by
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (le_div_iff₀ (pow_pos hfactor _)).2
  have heq : (T.card : ℝ) / (1 - p.Bstar / q) ^ t *
      (1 - p.Bstar / q) ^ (t + 1) = (1 - p.Bstar / q) * T.card := by
    rw [pow_succ, ← mul_assoc, div_mul_cancel₀ _ (pow_pos hfactor t).ne', mul_comm]
  rw [heq]
  exact performed_occupancy_ge_Bstar p q t G S hp hc hq hscale A index line hline l T hT

theorem tracked_card_le_order {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (q : ℕ) (A : FiniteAffine.Plane q P D L) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) : T.card ≤ q := by
  classical
  have hs : T ⊆ A.linePoints l := by
    intro x hx
    simp [FiniteAffine.Plane.linePoints, hT x hx]
  exact (Finset.card_le_card hs).trans_eq (A.card_points_line l)

omit [Fintype I] [Fintype V] in
theorem performed_rescaled_occupancy_jump {P D L : Type*}
    [Fintype P] [Fintype D] [Fintype L]
    (p : Parameters) (q t : ℕ) (hc : 0 < p.c) (hq : 0 < q)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (line : V → L)
    (l : L) (T : Finset P) (hT : ∀ x ∈ T, A.incident x l)
    (d : ℝ) (hd : 0 < d) (hdenom : d ≤ (1 - p.Bstar / q) ^ (t + 1))
    (r : Noise I V) :
    |((SelectionOccupancy.afterPlaneLine A T l (line r.2.1)).card : ℝ) /
        (1 - p.Bstar / q) ^ (t + 1) -
      (T.card : ℝ) / (1 - p.Bstar / q) ^ t| ≤ (1 + p.Bstar) / d := by
  classical
  have hB : 0 < p.Bstar := by
    unfold Parameters.Bstar Parameters.smin
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfactor1 : 1 - p.Bstar / q ≤ 1 := by
    linarith [div_nonneg hB.le hqR.le]
  have hcard : (T.card : ℝ) ≤ q := by
    exact_mod_cast tracked_card_le_order q A l T hT
  have h := SelectionOccupancy.rescaled_increment_abs_le hfactor hfactor1
    (pow_pos hfactor t) (show (1 - p.Bstar / q) ^ (t + 1) =
      (1 - p.Bstar / q) * (1 - p.Bstar / q) ^ t by rw [pow_succ]; ring)
    hd hdenom (Nat.cast_nonneg T.card) hcard (show (0 : ℝ) ≤ 1 by norm_num)
    (SelectionOccupancy.plane_step_abs_le_one A T l (line r.2.1) hT)
  have heq : (1 : ℝ) + (1 - (1 - p.Bstar / q)) * q = 1 + p.Bstar := by
    field_simp
    ring
  simpa only [heq] using h

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyTrack
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

theorem occupancyPrefix_subset (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (T : Finset P) (t : ℕ)
    (h : Prefix (Snapshot I V) t) : occupancyPrefix q A line l T t h ⊆ T :=
  Finset.filter_subset _ _

theorem occupancyResponse_bound (p : Parameters) (q t : ℕ) (G : Input I V)
    (hc : 0 < p.c) (hq : 0 < q) (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (d : ℝ) (hd : 0 < d)
    (hdenom : d ≤ (1 - p.Bstar / q) ^ (t + 1))
    (h : Prefix (Snapshot I V) t) (out : Snapshot I V) :
    |occupancyResponse p q G A line l T t h out| ≤ (1 + p.Bstar) / d := by
  have hB : 0 < p.Bstar := by unfold Parameters.Bstar Parameters.smin; positivity
  have hnonneg : 0 ≤ (1 + p.Bstar) / d := by positivity
  unfold occupancyResponse
  split
  · split
    · exact performed_rescaled_occupancy_jump p q t hc hq hfactor A line l _
        (fun x hx => hT x (occupancyPrefix_subset q A line l T t h hx)) d hd hdenom _
    · simpa using hnonneg
  · simpa using hnonneg

theorem occupancyResponse_mean_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (hc : 0 < p.c) (hq : 0 < q) (hscale : p.smin ≤ p.sizeScale q t)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (h : Prefix (Snapshot I V) t) :
    0 ≤ ∑ out, (snapshotPMF p q t G (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) out).toReal *
      occupancyResponse p q G A line l T t h out := by
  simp_rw [snapshotPMF_apply_real]
  rw [sum_snapshotWeight_response]
  cases hb : (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 with
  | none => simp [drawStepWeight, occupancyResponse, hb]
  | some S =>
    by_cases hp : Precheck p q t G S
    · rw [sum_drawStepWeight_of_precheck p q t G S hp]
      simp only [occupancyResponse, hb, hp, ite_true]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
        sum_noiseWeight p q G S hp.1 (fun i hi => (hp.2.2.2.1 i hi).1), one_mul]
      exact sub_nonneg.mpr (performed_rescaled_occupancy_ge p q t G S hp hc hq
        hscale hfactor A index line hline l _
          (fun x hx => hT x (occupancyPrefix_subset q A line l T t h hx)))
    · simp [drawStepWeight, occupancyResponse, hb, hp]

theorem occupancyTrack_lower_tail (p : Parameters) (q N : ℕ) (G : Input I V)
    (hc : 0 < p.c) (hq : 0 < q) (hN : 1 ≤ N)
    (hscale : ∀ t < N, p.smin ≤ p.sizeScale q t)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (d : ℝ) (hd : 0 < d)
    (hdenom : ∀ t < N, d ≤ (1 - p.Bstar / q) ^ (t + 1))
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ N) :
    (snapshotPathLaw p q G).real
      {ω | occupancyTrack p q G A line l T t ω ≤ (T.card : ℝ) - u} ≤
      2 * Real.exp (-u ^ 2 / (8 * (N : ℝ) * ((1 + p.Bstar) / d) ^ 2)) := by
  have hB : 0 < p.Bstar := by unfold Parameters.Bstar Parameters.smin; positivity
  exact additiveTrack_lower_tail (fun n => snapshotPMF p q n G) initialSnapshot
    (T.card : ℝ) (occupancyResponse p q G A line l T) N ((1 + p.Bstar) / d)
    hN (by positivity)
    (fun j hj h out => occupancyResponse_bound p q j G hc hq hfactor A line l T
      hT d hd (hdenom j hj) h out)
    (fun j hj h => occupancyResponse_mean_nonnegative p q j G hc hq (hscale j hj)
      hfactor A index line hline l T hT h) u hu t ht

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyAgreement
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

omit [Fintype I] in
theorem positive_snapshot_survival_before (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (hout : out.1 ≠ none)
    (hpos : 0 < snapshotWeight p q t G before out) :
    ∃ S r, before.1 = some S ∧ out.2 = some r ∧ Precheck p q t G S := by
  unfold snapshotWeight at hpos
  split at hpos
  next hcons =>
    cases hb : before.1 with
    | none => exact (hout (by simpa [advance, hb] using hcons)).elim
    | some S =>
      cases hr : out.2 with
      | none => exact (hout (by simpa [advance, hb, hr] using hcons)).elim
      | some r =>
        refine ⟨S, r, rfl, rfl, ?_⟩
        by_contra hpre
        simp [drawStepWeight, hb, hr, hpre] at hpos
  next => exact (lt_irrefl 0 hpos).elim

theorem occupancyPrefix_succ_of_draw (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (T : Finset P) (t : ℕ)
    (ω : Path (Snapshot I V)) (r : Noise I V) (hr : (ω (t + 1)).2 = some r) :
    occupancyPrefix q A line l T (t + 1) (frestrictLe (t + 1) ω) =
      SelectionOccupancy.afterPlaneLine A
        (occupancyPrefix q A line l T t (frestrictLe t ω)) l (line r.2.1) := by
  ext x
  simp only [occupancyPrefix, SelectionOccupancy.afterPlaneLine, Finset.mem_filter]
  constructor
  · rintro ⟨hx, havoid⟩
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · intro j hj s hs
      exact havoid j (by omega) s hs
    · exact havoid t (by omega) r hr
  · rintro ⟨⟨hx, havoid⟩, hlast⟩
    refine ⟨hx, ?_⟩
    intro j hj s hs
    by_cases hlt : j < t
    · exact havoid j hlt s hs
    · have heq : j = t := by omega
      subst j
      have hrs : r = s := Option.some.inj (hr.symm.trans hs)
      simpa [← hrs] using hlast

theorem occupancyTrack_eq_on_surviving_path (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P)
    (ω : Path (Snapshot I V))
    (hsupport : ∀ j, snapshotPMF p q j G (ω j) (ω (j + 1)) ≠ 0) :
    ∀ t, (ω t).1 ≠ none →
      occupancyTrack p q G A line l T t ω =
        ((occupancyPrefix q A line l T t (frestrictLe t ω)).card : ℝ) /
          (1 - p.Bstar / q) ^ t := by
  intro t
  induction t with
  | zero => intro _; simp [occupancyTrack]
  | succ t ih =>
    intro hsurv
    have hp : 0 < snapshotWeight p q t G (ω t) (ω (t + 1)) := by
      have hn : snapshotWeight p q t G (ω t) (ω (t + 1)) ≠ 0 := by
        intro hz
        apply hsupport t
        change ENNReal.ofReal (snapshotWeight p q t G (ω t) (ω (t + 1))) = 0
        rw [hz, ENNReal.ofReal_zero]
      exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G _ _) (Ne.symm hn)
    obtain ⟨S, r, hb, hr, hpre⟩ :=
      positive_snapshot_survival_before p q t G (ω t) (ω (t + 1)) hsurv hp
    have hprev := ih (by rw [hb]; simp)
    have hinc := additiveTrack_increment (T.card : ℝ)
      (occupancyResponse p q G A line l T) t ω
    change occupancyTrack p q G A line l T (t + 1) ω -
      occupancyTrack p q G A line l T t ω = _ at hinc
    have hlast : (frestrictLe t ω ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 = some S := hb
    simp only [stepObservable, occupancyResponse, hlast, hr, hpre, ite_true] at hinc
    rw [occupancyPrefix_succ_of_draw q A line l T t ω r hr]
    linarith

theorem ae_occupancyTrack_eq (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t, (ω t).1 ≠ none →
      occupancyTrack p q G A line l T t ω =
        ((occupancyPrefix q A line l T t (frestrictLe t ω)).card : ℝ) /
          (1 - p.Bstar / q) ^ t := by
  have hs := ae_all_iff.2 (fun j => FiniteHistory.ae_step_support
    (fun n => snapshotPMF p q n G) (initialSnapshot (I := I) (V := V)) j)
  filter_upwards [hs] with ω hω
  exact occupancyTrack_eq_on_surviving_path p q G A line l T ω hω

theorem surviving_occupancy_lower_tail (p : Parameters) (q N : ℕ) (G : Input I V)
    (hc : 0 < p.c) (hq : 0 < q) (hN : 1 ≤ N)
    (hscale : ∀ j < N, p.smin ≤ p.sizeScale q j)
    (hfactor : 0 < 1 - p.Bstar / q)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (d : ℝ) (hd : 0 < d)
    (hdenom : ∀ j < N, d ≤ (1 - p.Bstar / q) ^ (j + 1))
    (u : ℝ) (hu : 0 < u) (hub : u ≤ (T.card : ℝ))
    (t : ℕ) (ht : t ≤ N) (hdt : d ≤ (1 - p.Bstar / q) ^ t) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ≠ none ∧
      ((occupancyPrefix q A line l T t (frestrictLe t ω)).card : ℝ) ≤
        d * ((T.card : ℝ) - u)} ≤
      2 * Real.exp (-u ^ 2 / (8 * (N : ℝ) * ((1 + p.Bstar) / d) ^ 2)) := by
  refine le_trans ?_ (occupancyTrack_lower_tail p q N G hc hq hN hscale hfactor
    A index line hline l T hT d hd hdenom u hu t ht)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_occupancyTrack_eq p q G A line l T] with ω hω hbad
  rcases hbad with ⟨hsurv, hsmall⟩
  show occupancyTrack p q G A line l T t ω ≤ (T.card : ℝ) - u
  rw [hω t hsurv]
  apply (div_le_iff₀ (pow_pos hfactor t)).2
  exact hsmall.trans (by nlinarith [mul_le_mul_of_nonneg_right hdt (sub_nonneg.mpr hub)])

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyBound
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

theorem Parameters.occupancyDecay_pos (p : Parameters) (hp : p.Admissible) :
    0 < p.occupancyDecay := by
  have hc := hp.1
  have hc₀ := hp.2.2.1
  have hB : 0 < p.Bstar := by unfold Parameters.Bstar Parameters.smin; positivity
  unfold Parameters.occupancyDecay
  positivity

theorem surviving_source_occupancy_bound (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 0 < q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (G : Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (l : L) (T : Finset P)
    (hT : ∀ x ∈ T, A.incident x l) (hcard : p.c₀ * q ≤ (T.card : ℝ))
    (t : ℕ) (ht : t ≤ 3 * q) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ≠ none ∧
      ((occupancyPrefix q A line l T t (frestrictLe t ω)).card : ℝ) ≤
        2 * p.rho * q} ≤ 2 * Real.exp (-p.occupancyDecay * q) := by
  have hc := hp.1
  have hC := hp.2.1
  have hc₀ := hp.2.2.1
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hP : 0 < p.Pstar := by unfold Parameters.Pstar; positivity
  have hB : 0 < p.Bstar := by unfold Parameters.Bstar Parameters.smin; positivity
  have hfactor : 0 < 1 - p.Bstar / q := by
    have hhalf : p.Bstar / q ≤ 1 / 2 := (div_le_iff₀ hqR).2 (by linarith)
    linarith
  have hd : 0 < Real.exp (-6 * p.Bstar) := Real.exp_pos _
  have hscale : ∀ j < 3 * q, p.smin ≤ p.sizeScale q j := by
    intro j hj
    exact (SelectionScales.domain_bounds hP.le hq hPq hj.le).1
  have hdenom : ∀ j ≤ 3 * q, Real.exp (-6 * p.Bstar) ≤ (1 - p.Bstar / q) ^ j := by
    intro j hj
    exact (SelectionScales.domain_bounds hB.le hq hBq hj).1
  have hu : 0 < p.c₀ * (q : ℝ) / 2 := by positivity
  have hub : p.c₀ * (q : ℝ) / 2 ≤ (T.card : ℝ) := by linarith
  have hb := surviving_occupancy_lower_tail p q (3 * q) G hc hq (by omega)
    hscale hfactor A index line hline l T hT (Real.exp (-6 * p.Bstar)) hd
    (fun j hj => hdenom j.succ (by omega)) (p.c₀ * q / 2) hu hub t ht (hdenom t ht)
  have hexp : -(p.c₀ * (q : ℝ) / 2) ^ 2 /
      (8 * ((3 * q : ℕ) : ℝ) * ((1 + p.Bstar) / Real.exp (-6 * p.Bstar)) ^ 2) =
      -p.occupancyDecay * q := by
    unfold Parameters.occupancyDecay
    push_cast
    field_simp
    ring
  rw [hexp] at hb
  refine le_trans ?_ hb
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  refine ⟨hω.1, hω.2.trans ?_⟩
  unfold Parameters.rho
  nlinarith [mul_le_mul_of_nonneg_left hcard hd.le]

theorem source_plane_line_card (q : ℕ) (A : FiniteAffine.Plane q P D L) :
    Fintype.card L = q * (q + 1) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset L)) (t := (Finset.univ : Finset D))
    (f := A.direction) (by simp : Set.MapsTo A.direction
      (↑(Finset.univ : Finset L)) (↑(Finset.univ : Finset D)))
  simpa [A.card_lines_direction, A.card_directions, Nat.mul_comm] using h

theorem surviving_all_line_occupancy_bound (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 0 < q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (G : Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (T : L → Finset P)
    (hT : ∀ l x, x ∈ T l → A.incident x l)
    (hcard : ∀ l, p.c₀ * q ≤ ((T l).card : ℝ)) (t : ℕ) (ht : t ≤ 3 * q) :
    (snapshotPathLaw p q G).real {ω | (ω t).1 ≠ none ∧ ∃ l,
      ((occupancyPrefix q A line l (T l) t (frestrictLe t ω)).card : ℝ) ≤
        2 * p.rho * q} ≤
      2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  let E : L → Set (Path (Snapshot I V)) := fun l => {ω | (ω t).1 ≠ none ∧
    ((occupancyPrefix q A line l (T l) t (frestrictLe t ω)).card : ℝ) ≤
      2 * p.rho * q}
  have heq : {ω | (ω t).1 ≠ none ∧ ∃ l,
      ((occupancyPrefix q A line l (T l) t (frestrictLe t ω)).card : ℝ) ≤
        2 * p.rho * q} = ⋃ l, E l := by
    ext ω
    simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hs, l, hl⟩
      exact ⟨l, hs, hl⟩
    · rintro ⟨l, hs, hl⟩
      exact ⟨hs, l, hl⟩
  rw [heq]
  refine (measureReal_iUnion_fintype_le E).trans ?_
  calc
    ∑ l, (snapshotPathLaw p q G).real (E l) ≤
        ∑ _l : L, 2 * Real.exp (-p.occupancyDecay * q) := by
      exact Finset.sum_le_sum (fun l _ => surviving_source_occupancy_bound
        p hp q hq hPq hBq G A index line hline l (T l) (hT l) (hcard l) t ht)
    _ = 2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        source_plane_line_card q A, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

theorem source_occupancy_error_tendsto (p : Parameters) (hp : p.Admissible) :
    Tendsto (fun q : ℕ => 2 * (q : ℝ) * (q + 1) *
      Real.exp (-p.occupancyDecay * q)) atTop (nhds 0) := by
  have hκ := p.occupancyDecay_pos hp
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
    p.occupancyDecay hκ).comp tendsto_natCast_atTop_atTop
  have h₂ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2
    p.occupancyDecay hκ).comp tendsto_natCast_atTop_atTop
  have hsum := (h₂.add h₁).const_mul 2
  convert hsum using 1
  · ext q
    simp only [Function.comp_apply, Real.rpow_one, Real.rpow_two]
    ring
  · norm_num

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyTail
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

omit [Fintype I] in
theorem positive_snapshot_surviving_update (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (S' : State I V) (hout : out.1 = some S')
    (hpos : 0 < snapshotWeight p q t G before out) :
    ∃ S r, before.1 = some S ∧ out.2 = some r ∧
      update G S r.1 r.2.1 r.2.2 = S' := by
  obtain ⟨S, r, hb, hr, _⟩ := positive_snapshot_survival_before p q t G before out
    (by rw [hout]; simp) hpos
  refine ⟨S, r, hb, hr, ?_⟩
  have hcons : out.1 = advance q G before.1 out.2 := by
    by_contra hn
    simp [snapshotWeight, hn] at hpos
  rw [hout, hb, hr] at hcons
  change some S' = (if Postcheck q G S r.2.1 r.2.2 then
    some (update G S r.1 r.2.1 r.2.2) else none) at hcons
  split at hcons
  · exact (Option.some.inj hcons).symm
  · contradiction

theorem recorded_seen_on_support_path (p : Parameters) (q : ℕ) (G : Input I V)
    (ω : Path (Snapshot I V)) (hi : ω 0 = initialSnapshot)
    (hsupport : ∀ j, snapshotPMF p q j G (ω j) (ω (j + 1)) ≠ 0) :
    ∀ t S, (ω t).1 = some S → ∀ i v, S.recorded i = some v →
      ∃ j < t, ∃ r : Noise I V, (ω (j + 1)).2 = some r ∧ r.2.1 = v := by
  intro t
  induction t with
  | zero =>
    intro S hS i v hv
    have hinit : S = initialState := by
      simpa [hi, initialSnapshot] using hS.symm
    simp [hinit, initialState] at hv
  | succ t ih =>
    intro S' hS' i v hv
    have hp : 0 < snapshotWeight p q t G (ω t) (ω (t + 1)) := by
      have hn : snapshotWeight p q t G (ω t) (ω (t + 1)) ≠ 0 := by
        intro hz
        apply hsupport t
        change ENNReal.ofReal (snapshotWeight p q t G (ω t) (ω (t + 1))) = 0
        rw [hz, ENNReal.ofReal_zero]
      exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G _ _) (Ne.symm hn)
    obtain ⟨S, r, hb, hr, hu⟩ :=
      positive_snapshot_surviving_update p q t G _ _ S' hS' hp
    rw [← hu] at hv
    by_cases heq : i = r.1
    · subst i
      have hv' : r.2.1 = v := by simpa [update] using hv
      exact ⟨t, by omega, r, hr, hv'⟩
    · have hv' : S.recorded i = some v := by simpa [update, heq] using hv
      obtain ⟨j, hj, s, hs, hsv⟩ := ih S hb i v hv'
      exact ⟨j, by omega, s, hs, hsv⟩

theorem ae_occupancyPrefix_avoids_recorded (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S →
      ∀ x ∈ occupancyPrefix q A line l T t (frestrictLe t ω),
      ∀ i v, S.recorded i = some v → ¬ (line v ≠ l ∧ A.incident x (line v)) := by
  filter_upwards [ae_initial_state (fun n => snapshotPMF p q n G) initialSnapshot,
    ae_all_iff.2 (fun n => ae_step_support (fun j => snapshotPMF p q j G)
      initialSnapshot n)] with ω hi hs
  intro t S hS x hx i v hv
  obtain ⟨j, hj, r, hr, hrv⟩ := recorded_seen_on_support_path p q G ω hi hs t S hS i v hv
  have hx' := (Finset.mem_filter.mp hx).2 j hj r hr
  simpa [hrv] using hx'

omit [Fintype V] in
theorem remaining_lines_loss_le (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (R : Finset P) (hR : ∀ x ∈ R, A.incident x l)
    (J : Finset I) (a : I → V) :
    R.card ≤ (R.filter (fun x => ∀ i ∈ J,
      ¬ (line (a i) ≠ l ∧ A.incident x (line (a i))))).card + J.card := by
  classical
  let bad : Finset P := J.biUnion (fun i => R.filter
    (fun x => line (a i) ≠ l ∧ A.incident x (line (a i))))
  have hbad : bad.card ≤ J.card := by
    simpa only [mul_one] using Finset.card_biUnion_le_card_mul J
      (fun i => R.filter (fun x => line (a i) ≠ l ∧ A.incident x (line (a i)))) 1
      (fun i _ => SelectionOccupancy.plane_deletion_card_le_one A R l (line (a i)) hR)
  have heq : R.filter (fun x => ∀ i ∈ J,
      ¬ (line (a i) ≠ l ∧ A.incident x (line (a i)))) = R \ bad := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, bad, Finset.mem_biUnion]
    aesop
  rw [heq]
  have hsub : bad ⊆ R := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxi).1
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  omega

omit [Fintype V] in
theorem finalTracked_loss_le_remaining (q : ℕ) (_ : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P)
    (l : L) (R : Finset P) (hRT : R ⊆ T l) (hR : ∀ x ∈ R, A.incident x l)
    (S : State I V) (a : I → V)
    (hext : ∀ i, i ∉ S.remaining → S.recorded i = some (a i))
    (havoid : ∀ x ∈ R, ∀ i v, S.recorded i = some v →
      ¬ (line v ≠ l ∧ A.incident x (line v))) :
    R.card ≤ (Selection.finalTracked A line T a l).card + S.remaining.card := by
  have hc := remaining_lines_loss_le q A line l R hR S.remaining a
  apply hc.trans
  apply Nat.add_le_add_right
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxR, hxgood⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hRT hxR, ?_⟩
  intro i hneq hinc
  by_cases hi : i ∈ S.remaining
  · exact hxgood i hi ⟨hneq, hinc⟩
  · exact havoid x hxR i (a i) (hext i hi) ⟨hneq, hinc⟩

theorem ae_occupancyPrefix_subset_recorded (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S → ∀ l,
      occupancyPrefix q A line l (T l) t (frestrictLe t ω) ⊆ recordedTracked q A line T S l := by
  filter_upwards [ae_all_iff.2 (fun l =>
    ae_occupancyPrefix_avoids_recorded p q G A line l (T l))] with ω hω
  intro t S hS l x hx
  exact Finset.mem_filter.mpr ⟨occupancyPrefix_subset q A line l (T l) t _ hx,
    hω l t S hS x hx⟩

theorem surviving_recorded_occupancy_bound (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 0 < q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (G : Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (T : L → Finset P)
    (hT : ∀ l x, x ∈ T l → A.incident x l)
    (hcard : ∀ l, p.c₀ * q ≤ ((T l).card : ℝ)) (t : ℕ) (ht : t ≤ 3 * q) :
    (snapshotPathLaw p q G).real {ω | ∃ S, (ω t).1 = some S ∧ ∃ l,
      ((recordedTracked q A line T S l).card : ℝ) ≤ 2 * p.rho * q} ≤
      2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  refine le_trans ?_ (surviving_all_line_occupancy_bound p hp q hq hPq hBq G A
    index line hline T hT hcard t ht)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_occupancyPrefix_subset_recorded p q G A line T] with ω hω hbad
  obtain ⟨S, hS, l, hl⟩ := hbad
  refine ⟨by rw [hS]; simp, l, ?_⟩
  exact le_trans (by exact_mod_cast Finset.card_le_card (hω t S hS l)) hl

theorem recorded_finalTracked_loss_le (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P)
    (hT : ∀ l x, x ∈ T l → A.incident x l) (S : State I V) (a : I → V)
    (hext : ∀ i, i ∉ S.remaining → S.recorded i = some (a i)) (l : L) :
    (recordedTracked q A line T S l).card ≤
      (Selection.finalTracked A line T a l).card + S.remaining.card := by
  exact finalTracked_loss_le_remaining q G A line T l _ (Finset.filter_subset _ _)
    (fun x hx => hT l x (Finset.mem_filter.mp hx).1) S a hext
    (fun x hx => (Finset.mem_filter.mp hx).2)

theorem completion_occupancyMass_le_bad_recorded (p : Parameters) (q : ℕ)
    (G : Input I V) (A : FiniteAffine.Plane q P D L) (line : V → L)
    (T : L → Finset P) (hT : ∀ l x, x ∈ T l → A.incident x l)
    (S : State I V) (law : Selection.OutputLaw G)
    (hrem : (S.remaining.card : ℝ) ≤ p.rho * q)
    (hext : ∀ a, 0 < law.weight a → ∀ i, i ∉ S.remaining →
      S.recorded i = some (a i)) :
    Selection.occupancyFailureMass law A line T p.rho ≤
      if ∃ l, ((recordedTracked q A line T S l).card : ℝ) ≤ 2 * p.rho * q
        then 1 else 0 := by
  classical
  split
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => law.nonnegative a)).trans law.mass_le_one
  · rename_i hgood
    unfold Selection.occupancyFailureMass
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro a ha
    apply le_antisymm _ (law.nonnegative a)
    apply le_of_not_gt
    intro hpos
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp ha).2
    have hlower : 2 * p.rho * (q : ℝ) < (recordedTracked q A line T S l).card :=
      lt_of_not_ge (fun h => hgood ⟨l, h⟩)
    have hloss := recorded_finalTracked_loss_le q G A line T hT S a (hext a hpos) l
    have hlossR : ((recordedTracked q A line T S l).card : ℝ) ≤
        (Selection.finalTracked A line T a l).card + (S.remaining.card : ℝ) := by
      exact_mod_cast hloss
    linarith

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyFinal
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

theorem sourceTerminalLaw_agrees_recorded [Nonempty V]
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) (a : I → V)
    (hpos : 0 < (sourceTerminalLaw p q G hno S).weight a) :
    ∀ i, i ∉ S.remaining → S.recorded i = some (a i) := by
  unfold sourceTerminalLaw at hpos
  split at hpos
  · unfold terminalLaw at hpos
    split at hpos
    next h =>
      change 0 < ((PMF.uniformOfFinset (Tail.successfulAssignments G S) _).map
        (Tail.complete G S (recordedAssignment S)) a).toReal at hpos
      have hs := (PMF.apply_pos_iff _ _).mp (ENNReal.toReal_pos_iff.mp hpos).1
      obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      exact Tail.complete_agrees_recorded G S (recordedAssignment S)
        (recordedAssignment_recorded G S h.1) b
    next => simp [failureLaw] at hpos
  · simp [failureLaw] at hpos

theorem finalLaw_occupancy_bound [Nonempty V] (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (hρq : 2 ≤ p.rho * q) (G : Input I V)
    (hn : Fintype.card I = 2 * (q + 1))
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (T : L → Finset P)
    (hT : Selection.TrackedSets A T p.c₀) :
    Selection.occupancyFailureMass (finalLaw p q G hno) A line T p.rho ≤
      2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  let N := p.lastMainTime q (Fintype.card I)
  let bad : Option (State I V) → Prop := fun out => ∃ S, out = some S ∧ ∃ l,
    ((recordedTracked q A line T S l).card : ℝ) ≤ 2 * p.rho * q
  have hpoints : ∀ l x, x ∈ T l → A.incident x l := by
    intro l x hx
    exact (Finset.mem_filter.mp ((hT l).1 hx)).2
  have hcard : ∀ l, p.c₀ * q ≤ ((T l).card : ℝ) := fun l => (hT l).2
  have htime : N ≤ 3 * q := by
    have hN : N ≤ Fintype.card I := Nat.sub_le _ _
    omega
  have hbound := surviving_recorded_occupancy_bound p hp q (by omega) hPq hBq
    G A index line hline T hpoints hcard N htime
  change (snapshotPathLaw p q G).real {ω | (ω N).1 ∈ {o | bad o}} ≤ _ at hbound
  rw [state_event_real_eq_historyWeight] at hbound
  refine le_trans ?_ hbound
  rw [occupancyFailureMass_finalLaw]
  apply Finset.sum_le_sum
  intro out _
  have hw := historyWeight_nonnegative p q G N out
  change historyWeight p q G N out * _ ≤ _
  by_cases hzero : historyWeight p q G N out = 0
  · simp [hzero]
  have hpos : 0 < historyWeight p q G N out := lt_of_le_of_ne hw (Ne.symm hzero)
  cases out with
  | none => simp [sourceTerminalOutcomeLaw, Selection.occupancyFailureMass, failureLaw, bad]
  | some S =>
    have htail : p.tailSlots q ≤ Fintype.card I := by
      have ht := Parameters.tailSlots_le_order hp q
      omega
    have hrem : S.remaining.card = p.tailSlots q := by
      have hc := positive_historyWeight_card p q G N S hpos
      dsimp [N, Parameters.lastMainTime] at hc
      omega
    have hremR : (S.remaining.card : ℝ) ≤ p.rho * q := by
      rw [hrem]
      exact Parameters.tailSlots_le_rho_mul hp hρq
    have ht := completion_occupancyMass_le_bad_recorded p q G A line T hpoints S
      (sourceTerminalLaw p q G hno S) hremR
      (sourceTerminalLaw_agrees_recorded p q G hno S)
    have hm := mul_le_mul_of_nonneg_left ht hw
    simpa [bad, sourceTerminalOutcomeLaw, mul_ite] using hm

theorem outputLaw_occupancy_bound (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (hρq : 2 ≤ p.rho * q) (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (T : L → Finset P)
    (hT : Selection.TrackedSets A T p.c₀) :
    Selection.occupancyFailureMass (outputLaw p q G hG.2.1) A line T p.rho ≤
      2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  let : Nonempty V := graphBounds_vertex_nonempty G q p.c p.C hp.1 (by omega) hG
  rw [outputLaw_eq_finalLaw]
  exact finalLaw_occupancy_bound p hp q hq hPq hBq hρq G hG.1 hG.2.1 A index line hline T hT

theorem eventually_outputLaw_occupancy_bound.{u, v, w}
    (p : Parameters) (hp : p.Admissible) :
    ∀ᶠ q : ℕ in atTop,
      ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
      ∀ G : Input I V, ∀ hG : GraphBounds G q p.c p.C,
      ∀ (P D L : Type w) [Fintype P] [Fintype D] [Fintype L],
      ∀ (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L),
      Selection.LineAssignment G A index line →
      ∀ T : L → Finset P, Selection.TrackedSets A T p.c₀ →
        Selection.occupancyFailureMass (outputLaw p q G hG.2.1) A line T p.rho ≤
          2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  filter_upwards [Parameters.eventually_scale_regime p,
    Parameters.eventually_occupancy_regime hp] with q hs ho
  intro I V _ _ G hG P D L _ _ _ A index line hline T hT
  exact outputLaw_occupancy_bound p hp q hs.1 hs.2 ho.2.1 ho.2.2 G hG
    A index line hline T hT

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyUniform
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced.Selection.Process
universe u v w

theorem exists_uniformOccupancyEstimate (p : Parameters) (hp : p.Admissible) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop, UniformOccupancyEstimate.{u,v,w} p ε q := by
  refine ⟨fun q => 2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q),
    source_occupancy_error_tendsto p hp, ?_⟩
  exact eventually_outputLaw_occupancy_bound.{u,v,w} p hp

theorem selectionStatement_of_uniform_concentration
    (hconcentration : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformConcentrationEstimate.{u,v} p ε q) :
    SelectionStatement.{u,v,w} := by
  exact selectionStatement_of_uniform_concentration_occupancy hconcentration
    exists_uniformOccupancyEstimate

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionEndpoint
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u v w

theorem selection_proof : SelectionStatement.{u,v,w} := by
  apply Selection.Process.selectionStatement_of_uniform_concentration
  intro p hp
  exact Selection.Process.exists_uniformConcentratedPath_estimate p hp

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Results
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem deletion_domination_oai : SelectedDeletionResult.{u} :=
  SelectedDeletion.result_of_candidate_and_selection candidateGraph_proof selection_proof

end Balanced

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.deletion_domination_oai.{u} := @OAI.Balanced.deletion_domination_oai.{u}
