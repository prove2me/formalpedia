-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:22:39.348242+00:00
-- url     : https://prove2.me/submissions/c06816dd-53ab-441e-abb9-fcbff7ffbf1c

import Mathlib
import Definitions.Def_OAIQ053K020
import Definitions.Def_OAIQ053K032
import Definitions.Def_OAIQ053K039
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedFixedBatch_actual_local_bound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

theorem mass_mono {g : ℝ} {S T : Finset I} (hg : 0 ≤ g) (hST : S ⊆ T) :
    mass g S ≤ mass g T := by
  apply mul_le_mul_of_nonneg_left _ hg
  exact_mod_cast Finset.card_le_card hST

theorem point_cost_le {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) {i : I} (hi : i ∈ S) : g * d i ≤ cost g d S := by
  exact Finset.single_le_sum (fun j hj => mul_nonneg hg (hd j hj)) hi

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_FiniteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteGraph

variable {I H : Type*} [Fintype H] [DecidableEq I] [DecidableEq H]

theorem mem_touching (E : H → Finset I) (S : Finset I) (h : H) :
    h ∈ touching E S ↔ ∃ i ∈ S, i ∈ E h := by
  simp only [touching, Finset.mem_biUnion, incoming, Finset.mem_filter,
    Finset.mem_univ, true_and]

end MetricKMedian.FiniteGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_SourceGenerator
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
-- module Solutions.OAIQ053_KM.KMedian_Process_HeavyActions
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Process_ActualActions
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyState
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyRound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyTransport
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

 theorem localSet_image (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) :
    (localSet A S).image Subtype.val=S := by
  ext i
  constructor
  · rintro hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact (mem_localSet _ _ _).mp hj
  · intro hi
    exact mem_image.mpr ⟨⟨i,hS hi⟩,(mem_localSet _ _ _).mpr hi,rfl⟩

 theorem image_mass (A : Finset (Copy (F := F) Δ)) (S : Finset A) (g : ℝ) :
    mass g (S.image Subtype.val)=mass g S := by
  simp only [mass,card_image_of_injective _ Subtype.val_injective]

 theorem image_cost (A : Finset (Copy (F := F) Δ)) (S : Finset A) (g : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    PhysicalPotential.cost g d (S.image Subtype.val)=
      PhysicalPotential.cost g (fun i => d i.val) S := by
  unfold PhysicalPotential.cost
  rw [sum_image (fun _ _ _ _ he => Subtype.ext he)]

 theorem localSet_mass (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (g : ℝ) :
    mass g (localSet A S)=mass g S := by
  rw [← image_mass,localSet_image A S hS]

 theorem localSet_cost (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (g : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    PhysicalPotential.cost g (fun i => d i.val) (localSet A S)=PhysicalPotential.cost g d S := by
  rw [← image_cost,localSet_image A S hS]

 theorem image_potential (A : Finset (Copy (F := F) Δ)) (S : Finset A) (x g b : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    potential x g d (S.image Subtype.val) b=potential x g (fun i => d i.val) S b := by
  unfold potential
  rw [image_mass,image_cost]

 theorem localSet_potential (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (x g b : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    potential x g (fun i => d i.val) (localSet A S) b=potential x g d S b := by
  rw [← image_potential,localSet_image A S hS]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_GroupCap
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

 theorem cap_nonneg {R : ℝ} (d : F → ℝ) (O : Finset F)
    (hR : 0 ≤ R) (hd : ∀ f, 0 ≤ d f) : 0 ≤ cap R d O :=
  (le_cap R d O 0).mpr ⟨by positivity,fun f _ => hd f⟩

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
-- module Solutions.OAIQ053_KM.KMedian_Process_LocalForceScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Finset Analytic
variable {I : Type*} [DecidableEq I]

theorem local_cap_scale {g b R : ℝ} {d : I → ℝ} {S S₀ : Finset I}
    (hg : 0 < g) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd : ∀ i ∈ S₀, 0 ≤ d i) (hb : 0 ≤ b) (hbR : b ≤ 5*R)
    (hR : ∃ i ∈ S₀, R=d i) :
    b ≤ 5*(cost g d S+(1-mass g S)*b)/g := by
  let Q := cost g d S+(1-mass g S)*b
  have hy : mass g S ≤ 1 := (mass_mono hg.le hS).trans_eq hm₀
  have hV0 := cost_nonneg hg.le (fun i hi => hd i (hS hi))
  have hVQ : cost g d S ≤ Q := le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hy) hb)
  have hQ : 0 ≤ Q := hV0.trans hVQ
  change b ≤ 5*Q/g
  apply (le_div_iff₀ hg).mpr
  by_cases heq : S=S₀
  · obtain ⟨i, hi, hRi⟩ := hR
    have hp := point_cost_le hg.le (fun i hi => hd i (hS hi)) (heq.symm ▸ hi)
    rw [← hRi] at hp
    have hm := mul_le_mul_of_nonneg_right hbR hg.le
    nlinarith only [hp, hm, hVQ]
  · have hc : S.card < S₀.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS, heq⟩)
    have hc' : (S.card:ℝ)+1 ≤ (S₀.card:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hc)
    have hmul := mul_le_mul_of_nonneg_left hc' hg.le
    have hgap : g ≤ 1-mass g S := by
      unfold mass at hm₀ ⊢
      nlinarith only [hmul, hm₀]
    have hb' := mul_le_mul_of_nonneg_right hgap hb
    dsimp only [Q] at hQ ⊢
    nlinarith only [hb', hV0, hQ]

end MetricKMedian.PhysicalPotential

end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalRound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

omit [Fintype F] in
 theorem forcedAlive_subset (A S : Finset (Copy (F := F) Δ)) (H : Finset A) :
    forcedAlive A S H ⊆ localSet A S := filter_subset _ _

omit [Fintype F] in
 theorem heavy_alive_forced (A S : Finset (Copy (F := F) Δ)) (H : Finset A) :
    H ∩ localSet A S ⊆ forcedAlive A S H := by
  intro i hi
  exact mem_filter.mpr ⟨(mem_inter.mp hi).2,
    mem_image.mpr ⟨i,(mem_inter.mp hi).1,rfl⟩⟩

theorem round_cap (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
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

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalBatchData
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

theorem graph_eq (G : I → Finset I) : graph G=graphActions G := rfl

theorem heavy_eq (Full : Actions I I) (H : Finset I) : heavy Full H=heavyActions Full H := rfl

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalBatchFacts
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

omit [Fintype I] in
theorem conflicts_eq (D : Actions I E) (Δ : ℕ) (e : E) :
    conflicts D Δ e=balancedConflicts D Δ e := by
  unfold conflicts balancedConflicts balanced balancedActions
  split_ifs with he
  · ext f
    constructor
    · intro hf
      obtain ⟨hb,hne,i,hi⟩ := mem_filter.mp hf
      apply mem_erase.mpr
      refine ⟨hne,mem_inter.mpr ⟨?_,hb⟩⟩
      exact (FiniteGraph.mem_touching _ _ _).mpr ⟨i,(mem_inter.mp hi).1,(mem_inter.mp hi).2⟩
    · intro hf
      obtain ⟨hne,hf⟩ := mem_erase.mp hf
      obtain ⟨ht,hb⟩ := mem_inter.mp hf
      obtain ⟨i,hi,hif⟩ := (FiniteGraph.mem_touching _ _ _).mp ht
      exact mem_filter.mpr ⟨hb,hne,⟨i,mem_inter.mpr ⟨hi,hif⟩⟩⟩
  · rfl

theorem proposal_eq (G : I → Finset I) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) {n : ℕ}
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    (hpp : 0 ≤ p ∧ p ≤ 1)
    (hq : ∀ e : HeavyAction (graph G) (heavySet (graphMass G g) β),
      0 ≤ bias (graphMass G g) p φ (heavyParent (graph G) _ e) ∧
      bias (graphMass G g) p φ (heavyParent (graph G) _ e) ≤ 1) :
    proposal G Δ g β p φ hp hφ hupper enum =
      SparseEnumeratedBatch.law enum
        (balancedActions (heavyActions (graphActions G) (heavySet (graphMass G g) β)) Δ)
        (balancedConflicts (heavyActions (graphActions G) (heavySet (graphMass G g) β)) Δ)
        p (fun e => bias (graphMass G g) p φ (heavyParent (graph G) _ e)) hpp hq := by
  unfold proposal
  dsimp only
  congr 1
  funext e
  exact conflicts_eq _ _ e

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalProposalBound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset PhysicalPotential Analytic FixedBatch
variable {I : Type} [DecidableEq I] [Fintype I] {n : ℕ}

theorem proposal_local_bound (G : I → Finset I) (S F : Finset I) (Δ : ℕ)
    (g β p φ : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    {x h R b b' : ℝ} (d : I → ℝ)
    (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hy : mass (g:ℝ) S ≤ 1) (hF : F ⊆ S) (hHS : heavySet (graphMass G g) β ∩ S ⊆ F)
    (hd0 : ∀ i, 0 ≤ d i) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S, d i ≤ R)
    (hbQ : b ≤ 5*((PhysicalPotential.cost (g:ℝ) d S+(1-mass (g:ℝ) S)*b)/(g:ℝ)))
    (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) (hb'0 : 0 ≤ b') (hb' : b' ≤ b)
    (hbF : ∀ i ∈ F, b' ≤ d i) (hbH : ∀ i ∈ heavySet (graphMass G g) β, b' ≤ d i) :
    let D := heavy (graph G) (heavySet (graphMass G g) β)
    (proposal G Δ g β p φ hp hφ hupper enum).real.expect (fun A =>
      potential (x*Real.exp (-h)) (g:ℝ) d
        (nextAliveAt D (coefficient x (mass (g:ℝ) S)) d (S \ F) A)
        (nextCap D d b' A)-potential x (g:ℝ) d S b) ≤
      h*(timeRate x (mass (g:ℝ) S)*PhysicalPotential.cost (g:ℝ) d S+
        (g:ℝ)*(∑ e ∈ relevant (graphActions G) S, charge (graphActions G) x (g:ℝ) b d S e))+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  dsimp only
  let H := heavySet (graphMass G g) β
  let q := fun e : HeavyAction (graph G) H => bias (graphMass G g) p φ (heavyParent (graph G) H e)
  have hpp : 0 ≤ p ∧ p ≤ 1 := ⟨hp,by have hh := mul_nonneg hp hφ; nlinarith only [hh,hupper]⟩
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := fun e => bias_probability _ hp hφ hupper _
  have hqb : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+(φ:ℝ))*(p:ℝ) := by
    intro e
    exact_mod_cast bias_bounds (graphMass G g) hp hφ (heavyParent (graph G) H e)
  have ht := SparseEnumeratedFixedBatch.actual_local_bound_s53 G H S F Δ enum p q hpp hq
    d hprob hG hg hg1 hunit hx0 hx1 hh0 hh1 (by exact_mod_cast hφ) hφ1 hqb hsmall
    hy hF hHS hd0 hR0 hdR hbQ hb0 hbR hb'0 hb' hbF hbH
  rw [proposal_eq G Δ g β p φ hp hφ hupper enum hpp hq]
  exact ht

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseConditionalRoundDrift
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F : Type} [DecidableEq F] [Fintype F] {Δ n : ℕ}

theorem rational_conditional_round_drift_s53_oai (A S S₀ : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (RationalBatchData.graph G)
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
    {x h R : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hSA : S ⊆ A) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd0 : ∀ f, 0 ≤ d f) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, d i.1 ≤ R)
    (hR : ∃ i ∈ S₀, R=d i.1) :
    let H := RationalBatchData.heavySet (RationalBatchData.graphMass G g) β
    let μ := RationalBatchData.proposal G Δ g β p φ hp hφ hupper enum
    μ.real.expect (fun Z => potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))-
      potential x g (fun i => d i.1) S (GroupCap.cap R d (integral Δ A))) ≤
    h*(timeRate x (mass g S)*PhysicalPotential.cost g (fun i => d i.1) S+
      (g:ℝ)*(∑ e ∈ relevant (graphActions G) (localSet A S),
        charge (graphActions G) x g (GroupCap.cap R d (integral Δ A))
          (fun i => d i.val.1) (localSet A S) e))+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  intro H μ
  let D := heavyActions (graphActions G) H
  let b := GroupCap.cap R d (integral Δ A)
  let b' := GroupCap.cap R d (integral Δ A ∪ forcedGroups A H)
  have hb0 : 0 ≤ b := GroupCap.cap_nonneg d _ hR0 hd0
  have hbR : b ≤ 5*R := GroupCap.cap_le_radius R d _
  have hb'0 : 0 ≤ b' := GroupCap.cap_nonneg d _ hR0 hd0
  have hb' : b' ≤ b := GroupCap.cap_antitone R d subset_union_left
  have hy : mass g (localSet A S) ≤ 1 := by
    rw [localSet_mass A S hSA]
    exact (mass_mono hg.le hS).trans_eq hm₀
  have hbQ : b ≤ 5*((PhysicalPotential.cost g (fun i : A => d i.val.1) (localSet A S)+
      (1-mass g (localSet A S))*b)/g) := by
    rw [localSet_mass A S hSA,localSet_cost A S hSA g (fun i => d i.1)]
    simpa only [mul_div_assoc] using local_cap_scale hg hS hm₀ (fun i _ => hd0 i.1) hb0 hbR hR
  have hbF : ∀ i ∈ forcedAlive A S H, b' ≤ d i.val.1 := by
    intro i hi
    exact GroupCap.cap_le_member R d _ (mem_union_right _ (mem_filter.mp hi).2)
  have hbH : ∀ i ∈ H, b' ≤ d i.val.1 := by
    intro i hi
    exact GroupCap.cap_le_member R d _ (mem_union_right _ (mem_image.mpr ⟨i,hi,rfl⟩))
  have hh := RationalBatchData.proposal_local_bound G (localSet A S) (forcedAlive A S H) Δ
    g β p φ hp hφ hupper enum (fun i => d i.val.1) hprob
    hG hg hg1 hunit hx0 hx1 hh0 hh1 hφ1 hsmall
    hy (forcedAlive_subset A S H) (heavy_alive_forced A S H) (fun i => hd0 i.val.1) hR0
    (fun i hi => hdR i.val (hS ((mem_localSet _ _ _).mp hi)))
    hbQ hb0 hbR hb'0 hb' hbF hbH
  dsimp only at hh
  change μ.real.expect _ ≤ _ at hh
  have hpoint : ∀ Z, potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))=
    potential (x*Real.exp (-h)) g (fun i : A => d i.val.1)
      (nextAliveAt D (coefficient x (mass g (localSet A S))) (fun i => d i.val.1)
        (localSet A S \ forcedAlive A S H) Z)
      (nextCap D (fun i => d i.val.1) b' Z) := by
    intro Z
    rw [round_cap A G H Z R d hG hown]
    unfold roundAlive
    rw [image_potential,localSet_mass A S hSA]
  have hequal := congrArg
    (fun v : Finset (HeavyAction (graphActions G) H) → ℝ =>
      μ.real.expect (fun Z => v Z-potential x g (fun i => d i.1) S b)) (funext hpoint)
  apply hequal.le.trans
  convert hh using 1 <;>
    (try simp only [localSet_mass A S hSA,localSet_cost A S hSA g (fun i => d i.1),
    localSet_potential A S hSA x g b (fun i => d i.1),b,D,H,
    RationalBatchData.heavy_eq,RationalBatchData.graph_eq])
  all_goals rfl

end MetricKMedian.CopyState
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53_oai := @OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53_oai
