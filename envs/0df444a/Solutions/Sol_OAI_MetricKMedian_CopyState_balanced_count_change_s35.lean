-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.balanced_count_change_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:53.158199+00:00
-- url     : https://prove2.me/submissions/42c94feb-2655-4939-a614-da1f2ee8eca7

import Mathlib
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K024

section
-- module Solutions.Q224_RR.KMedian_Process_PhysicalPotential
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

theorem mass_sdiff [DecidableEq I] (g : ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    mass g (S \ T) = mass g S - mass g T := by
  unfold mass
  rw [Finset.card_sdiff_of_subset hTS, Nat.cast_sub (Finset.card_le_card hTS)]
  ring

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.Q224_RR.KMedian_Process_FiniteGraph
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
-- module Solutions.Q224_RR.KMedian_Process_CopyState
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.CopyState.mem_localSet _root_.OAI.MetricKMedian.CopyState.mem_own
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

 theorem slots_disjoint {f h : F} (hfh : f ≠ h) : Disjoint (slots Δ f) (slots Δ h) := by
  apply disjoint_left.mpr
  intro i hi hj
  exact hfh (((mem_slots Δ f i).mp hi).symm.trans ((mem_slots Δ h i).mp hj))

 theorem card_resets (O : Finset F) : (resets Δ O).card=O.card*Δ := by
  rw [resets, card_biUnion (fun _ _ _ _ hne => slots_disjoint Δ hne)]
  simp

variable [Fintype F]

omit [Fintype F] in
 theorem reset_mass (O : Finset F) {g : ℝ} (hunit : g*(Δ:ℝ)=1) :
    mass g (resets Δ O)=(O.card:ℝ) := by
  rw [mass, card_resets, Nat.cast_mul]
  nlinarith only [hunit]

omit [Fintype F] in

theorem next_mass_le (A erased : Finset (Copy (F := F) Δ)) (O : Finset F)
    {g : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (he : erased ⊆ A) :
    mass g (next Δ A erased O) ≤ mass g A-mass g erased+O.card := by
  have hc := card_union_le (A \ erased) (resets Δ O)
  have hr : ((next Δ A erased O).card:ℝ) ≤ ((A \ erased).card:ℝ)+(resets Δ O).card := by
    exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hr hg
  change mass g (next Δ A erased O) ≤ _ at hm
  rw [mul_add, ← mass, ← mass, mass_sdiff g he, reset_mass Δ O hunit] at hm
  exact hm

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.Q224_RR.KMedian_Process_CopyRound
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

variable {Δ}

omit [Fintype F] in
 theorem roundErased_subset (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : roundErased A G H Z ⊆ A := by
  rintro i hi
  obtain ⟨h,_,rfl⟩ := mem_image.mp hi
  exact h.property

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.Q224_RR.KMedian_Process_PhysicalCountGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

theorem balanced_disjoint (D : Actions I E) (Δ : ℕ) (ω : E → Bool) :
    (↑(PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω) : Set E).PairwiseDisjoint D.erase := by
  intro e he f hf hne
  have he' := mem_inter.mp he
  have hf' := mem_inter.mp hf
  apply disjoint_left.mpr
  intro i hi hj
  have hconf : f ∈ balancedConflicts D Δ e := by
    rw [balancedConflicts,ite_eq_left he'.2]
    unfold FiniteGraph.conflicts
    apply mem_erase.mpr
    refine ⟨Ne.symm hne,mem_inter.mpr ⟨?_,hf'.2⟩⟩
    exact (FiniteGraph.mem_touching D.erase (D.erase e) f).mpr ⟨i,hi,hj⟩
  have ht := (mem_filter.mp he'.1).2.2 f hconf
  have hu := (mem_filter.mp hf'.1).2.1
  simp only [ht,Bool.false_eq_true] at hu

 theorem balanced_mass (D : Actions I E) (Δ : ℕ) (ω : E → Bool) {g : ℝ}
    (hunit : g*(Δ:ℝ)=1) :
    mass g ((PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω).biUnion D.erase)=
      ((PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω).card:ℝ) := by
  rw [mass,card_biUnion (balanced_disjoint D Δ ω)]
  have hc : (∑ e ∈ PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω,
      (D.erase e).card)=(PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω).card*Δ := by
    calc
      _ = ∑ _e ∈ PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω, Δ := by
        apply sum_congr rfl
        intro e he
        exact (mem_filter.mp (mem_inter.mp he).2).2
      _ = _ := by simp
  rw [hc,Nat.cast_mul]
  nlinarith only [hunit]

end MetricKMedian.FixedBatch

namespace MetricKMedian.CopyState
open Finset FixedBatch PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

theorem round_count_change (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
    mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤
      (H.card:ℝ)+((Z ∩ (heavyActions (graphActions G) H).ordinary).card:ℝ)-
        mass g (Z.biUnion (heavyActions (graphActions G) H).erase) := by
  have hn := next_mass_le Δ A (roundErased A G H Z) (roundOpened A G H Z) hg hunit (roundErased_subset A G H Z)
  have he : mass g (roundErased A G H Z)=mass g (Z.biUnion (heavyActions (graphActions G) H).erase) := by
    rw [roundErased,mass,mass,card_image_of_injective _ Subtype.val_injective]
  have ho : (roundOpened A G H Z).card ≤ H.card+(Z ∩ (heavyActions (graphActions G) H).ordinary).card :=
    (card_image_le).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))
  have hor : ((roundOpened A G H Z).card:ℝ) ≤ (H.card:ℝ)+((Z ∩ (heavyActions (graphActions G) H).ordinary).card:ℝ) :=
    by exact_mod_cast ho
  rw [he] at hn
  linarith only [hn,hor]

 theorem balanced_count_change_s35_oai (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (ω : HeavyAction (graphActions G) H → Bool) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
    let D := heavyActions (graphActions G) H
    let Z := PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω
    mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤ H.card := by
  dsimp only
  have hh := round_count_change A G H (PhysicalBatchLaw.balanced (balancedActions (heavyActions (graphActions G) H) Δ) (balancedConflicts (heavyActions (graphActions G) H) Δ) ω) hg hunit
  rw [balanced_mass _ Δ ω hunit] at hh
  have hc : (((PhysicalBatchLaw.balanced (balancedActions (heavyActions (graphActions G) H) Δ)
      (balancedConflicts (heavyActions (graphActions G) H) Δ) ω) ∩
      (heavyActions (graphActions G) H).ordinary).card:ℝ) ≤
      ((PhysicalBatchLaw.balanced (balancedActions (heavyActions (graphActions G) H) Δ)
      (balancedConflicts (heavyActions (graphActions G) H) Δ) ω).card:ℝ) := by
    exact_mod_cast card_le_card (inter_subset_left (s₂ := (heavyActions (graphActions G) H).ordinary))
  linarith only [hh,hc]

end MetricKMedian.CopyState
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.CopyState.balanced_count_change_s35_oai.{u_1} := @OAI.MetricKMedian.CopyState.balanced_count_change_s35_oai.{u_1}
