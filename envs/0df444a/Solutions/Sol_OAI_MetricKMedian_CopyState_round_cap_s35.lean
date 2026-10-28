-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.round_cap_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:58:15.024765+00:00
-- url     : https://prove2.me/submissions/5315e299-3408-46ce-9527-febc0d17b3aa

import Mathlib
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K021

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceGenerator
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic GeneratorAverage GraphMoments
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem mem_graph_erase (G : I → Finset I) (h i : I) :
    i ∈ (graphActions G).erase h ↔ h ∈ G i := by simp [graphActions]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_HeavyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem ordinary_heavyActions (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    e ∈ (heavyActions Full H).ordinary ↔ e.isLeft := by simp [heavyActions]

omit [Fintype I] in
 theorem heavyParent_membership (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    heavyParent Full H e ∈ H ↔ ¬ e.isLeft := by
  cases e with
  | inl h => simp [heavyParent, h.property]
  | inr p => simp [heavyParent, p.property.1]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActualActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

 theorem nonordinary_parent_heavy (G : I → Finset I) (H : Finset I)
    (e : HeavyAction (graphActions G) H) (he : e ∉ (heavyActions (graphActions G) H).ordinary) :
    (heavyActions (graphActions G) H).source e ∈ H := by
  apply (heavyParent_membership _ _ e).mpr
  simpa only [ordinary_heavyActions] using he

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F]
variable (Δ : ℕ)

variable [Fintype F]

 theorem reset_integral (A erased : Finset (Copy (F := F) Δ)) (O : Finset F) :
    O ⊆ integral Δ (next Δ A erased O) := by
  intro f hf
  apply (mem_integral _ _ _).mpr
  intro i hi
  exact mem_union_right _ ((mem_resets _ _ _).mpr ((mem_slots _ _ _).mp hi ▸ hf))

theorem integral_persists (A erased : Finset (Copy (F := F) Δ)) (O : Finset F)
    (hattribute : ∀ i ∈ A, i ∈ erased → i.1 ∈ integral Δ A → i.1 ∈ O) :
    integral Δ A ⊆ integral Δ (next Δ A erased O) := by
  intro f hf
  apply (mem_integral _ _ _).mpr
  intro i hi
  have hiA := (mem_integral _ _ _).mp hf hi
  have hif := (mem_slots _ _ _).mp hi
  by_cases hie : i ∈ erased
  · apply mem_union_right
    apply (mem_resets _ _ _).mpr
    exact hattribute i hiA hie (hif ▸ hf)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hiA,hie⟩)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

 theorem own_card_integral (A : Finset (Copy (F := F) Δ)) (i : A)
    (hi : i.val.1 ∈ integral Δ A) : (own Δ A i).card=Δ := by
  have he : (own Δ A i).image Subtype.val=slots Δ i.val.1 := by
    ext h
    constructor
    · intro hh
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hh
      exact (mem_slots _ _ _).mpr ((mem_own _ _ _ _).mp ht)
    · intro hh
      have hA := (mem_integral _ _ _).mp hi hh
      exact mem_image.mpr ⟨⟨h,hA⟩,(mem_own _ _ _ _).mpr ((mem_slots _ _ _).mp hh),rfl⟩
  have hc := congrArg Finset.card he
  simpa only [card_image_of_injective _ Subtype.val_injective,card_slots] using hc

 theorem integral_incoming_same_group (A : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    {i h : A} (hi : i.val.1 ∈ integral Δ A) (hh : h ∈ G i) : h.val.1=i.val.1 := by
  have he : own Δ A i=G i := eq_of_subset_of_card_le (hown i)
    (by rw [hG i,own_card_integral Δ A i hi])
  exact (mem_own _ _ _ _).mp (he.symm ▸ hh)

variable {Δ}

 theorem heavy_erase_parent {I : Type*} [Fintype I] [DecidableEq I]
    (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    (heavyActions Full H).erase e ⊆ Full.erase (heavyParent Full H e) := by
  intro i hi
  cases e with
  | inl h => exact hi
  | inr p => exact (mem_singleton.mp hi).symm ▸ p.property.2

 theorem parent_selected {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → Finset I) (H : Finset I) (Z : Finset (HeavyAction (graphActions G) H))
    {e : HeavyAction (graphActions G) H} (he : e ∈ Z) :
    heavyParent (graphActions G) H e ∈ selectedSources G H Z := by
  by_cases ho : e ∈ (heavyActions (graphActions G) H).ordinary
  · exact mem_union_right _ (mem_image.mpr ⟨e,mem_inter.mpr ⟨he,ho⟩,rfl⟩)
  · exact mem_union_left _ (nonordinary_parent_heavy G H e ho)

 theorem round_integral_persists (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
    integral Δ A ⊆ integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)) := by
  apply integral_persists
  intro i _ hie hii
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hie
  obtain ⟨e,he,hje⟩ := mem_biUnion.mp hj
  have hp := heavy_erase_parent (graphActions G) H e hje
  have hg := (mem_graph_erase G _ _).mp hp
  have hsame := integral_incoming_same_group Δ A G hG hown hii hg
  exact mem_image.mpr ⟨_,parent_selected G H Z he,hsame⟩

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_GroupCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

 theorem integral_next_subset (A erased : Finset (Copy (F := F) Δ)) (O : Finset F) :
    integral Δ (next Δ A erased O) ⊆ integral Δ A ∪ O := by
  intro f hf
  by_cases ho : f ∈ O
  · exact mem_union_right _ ho
  · apply mem_union_left
    apply (mem_integral _ _ _).mpr
    intro i hi
    have hh := (mem_integral _ _ _).mp hf hi
    rcases mem_union.mp hh with hh | hh
    · exact (mem_sdiff.mp hh).1
    · have hh' := (mem_resets _ _ _).mp hh
      rw [(mem_slots _ _ _).mp hi] at hh'
      exact False.elim (ho hh')

 theorem round_integral_eq (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (FixedBatch.HeavyAction (FixedBatch.graphActions G) H))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
    integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))=
      integral Δ A ∪ roundOpened A G H Z := by
  apply Subset.antisymm (integral_next_subset Δ A _ _)
  exact union_subset (round_integral_persists A G H Z hG hown) (reset_integral Δ A _ _)

end MetricKMedian.CopyState

namespace MetricKMedian.GroupCap
open Finset
variable {F E : Type*}

 theorem le_cap (R : ℝ) (d : F → ℝ) (O : Finset F) (c : ℝ) :
    c ≤ cap R d O ↔ c ≤ 5*R ∧ ∀ f ∈ O, c ≤ d f := le_fold_min _

 theorem cap_le_radius (R : ℝ) (d : F → ℝ) (O : Finset F) : cap R d O ≤ 5*R :=
  (fold_min_le _).mpr (Or.inl le_rfl)

 theorem cap_le_member (R : ℝ) (d : F → ℝ) (O : Finset F) {f : F} (hf : f ∈ O) :
    cap R d O ≤ d f := (fold_min_le _).mpr (Or.inr ⟨f,hf,le_rfl⟩)

 theorem cap_antitone (R : ℝ) (d : F → ℝ) {O O' : Finset F} (hO : O ⊆ O') :
    cap R d O' ≤ cap R d O :=
  (le_cap R d O _).mpr ⟨cap_le_radius R d O',fun _ hf => cap_le_member R d O' (hO hf)⟩

theorem cap_union_image [DecidableEq F] (R : ℝ) (d : F → ℝ) (O : Finset F) (Z : Finset E) (s : E → F) :
    cap R d (O ∪ Z.image s)=Z.fold min (cap R d O) (fun e => d (s e)) := by
  apply le_antisymm
  · apply (le_fold_min _).mpr
    exact ⟨cap_antitone R d subset_union_left,fun e he =>
      cap_le_member R d _ (mem_union_right _ (mem_image.mpr ⟨e,he,rfl⟩))⟩
  · have hh := (le_fold_min _).mp (show Z.fold min (cap R d O) (fun e => d (s e)) ≤
        Z.fold min (cap R d O) (fun e => d (s e)) from le_rfl)
    apply (le_cap R d _ _).mpr
    refine ⟨hh.1.trans (cap_le_radius R d O),?_⟩
    intro f hf
    rcases mem_union.mp hf with hf | hf
    · exact hh.1.trans (cap_le_member R d O hf)
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hf
      exact hh.2 e he

end MetricKMedian.GroupCap
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] {Δ : ℕ}

theorem round_cap_s35_oai (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (R : ℝ) (d : F → ℝ)
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
    GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)))=
      nextCap (heavyActions (graphActions G) H) (fun i => d i.val.1)
        (GroupCap.cap R d (integral Δ A ∪ forcedGroups A H)) Z := by
  rw [round_integral_eq Δ A G H Z hG hown]
  unfold roundOpened selectedSources
  rw [image_union,image_image,← union_assoc,GroupCap.cap_union_image]
  rfl

end MetricKMedian.CopyState
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.CopyState.round_cap_s35_oai.{u_1} := @OAI.MetricKMedian.CopyState.round_cap_s35_oai.{u_1}
