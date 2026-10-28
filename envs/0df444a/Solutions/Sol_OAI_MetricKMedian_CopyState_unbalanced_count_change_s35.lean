-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.unbalanced_count_change_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:58:58.932835+00:00
-- url     : https://prove2.me/submissions/c4a2f442-33f4-4553-b293-b09624a1e724

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K021

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
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
-- module Solutions.OAIQ035_KM.KMedian_Process_CountGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountGeometry
open Finset
variable {E U : Type*} [Fintype E] [DecidableEq E] [DecidableEq U]

omit [Fintype E] in
theorem overlap_self (S : E → Finset U) (e : E) : overlap S e e=0 := by simp [overlap]
omit [Fintype E] in
theorem overlap_symm (S : E → Finset U) (e f : E) : overlap S e f=overlap S f e := by
  by_cases h : e=f
  · subst f; rfl
  · simp only [overlap, ite_eq_right h, ite_eq_right (Ne.symm h), inter_comm]

omit [Fintype E] in
                                                                                
theorem truncated_union (S : E → Finset U) (T : Finset E) :
    2*(∑ e ∈ T, (S e).card) ≤ 2*(T.biUnion S).card+∑ e ∈ T, ∑ f ∈ T, overlap S e f := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    have hrow : ∑ f ∈ T, overlap S a f = ∑ f ∈ T, (S a ∩ S f).card := by
      apply sum_congr rfl
      intro f hf
      have haf : a ≠ f := by intro h; subst f; exact ha hf
      simp only [overlap, ite_eq_right haf]
    have hcol : ∑ e ∈ T, overlap S e a = ∑ f ∈ T, (S a ∩ S f).card := by
      simp_rw [overlap_symm S _ a]
      exact hrow
    have hint : (S a ∩ T.biUnion S).card ≤ ∑ f ∈ T, (S a ∩ S f).card := by
      rw [inter_biUnion]
      exact card_biUnion_le
    have hcard := card_union_add_card_inter (S a) (T.biUnion S)
    simp only [sum_insert ha, biUnion_insert, overlap_self, zero_add, sum_add_distrib]
    rw [hrow, hcol]
    omega

theorem selected_mass_bound (S : E → Finset U) (a : E → ℝ) {g : ℝ} (hg : 0 ≤ g)
    (ω : E → Bool) :
    (∑ e, a e*CountStatistic.bit ω e)-g*((univ.filter (fun e => ω e=true)).biUnion S).card ≤
      CountStatistic.statistic (fun e => a e-g*(S e).card)
        (fun e f => g*(overlap S e f:ℝ)) ω := by
  let T := univ.filter (fun e => ω e=true)
  have heq : ∀ (f : E → ℝ), (∑ e, f e*CountStatistic.bit ω e)=∑ e ∈ T, f e := by
    intro f
    dsimp only [T]
    rw [sum_filter]
    apply sum_congr rfl
    intro e _
    unfold CountStatistic.bit
    split_ifs <;> simp
  have hquad : (∑ e, ∑ f, g*(overlap S e f:ℝ)*CountStatistic.bit ω e*CountStatistic.bit ω f)=
      g*∑ e ∈ T, ∑ f ∈ T, (overlap S e f:ℝ) := by
    simp_rw [heq]
    simp only [← sum_mul]
    rw [heq]
    simp only [mul_sum]
  have hbase : 2*(∑ e ∈ T, ((S e).card:ℝ)) ≤
      2*((T.biUnion S).card:ℝ)+(∑ e ∈ T, ∑ f ∈ T, (overlap S e f:ℝ)) := by
    exact_mod_cast truncated_union S T
  unfold CountStatistic.statistic
  rw [hquad, heq, heq]
  simp only [sum_sub_distrib, ← mul_sum]
  nlinarith only [mul_le_mul_of_nonneg_left hbase hg]

end MetricKMedian.CountGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_UnbalancedActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

omit [Fintype I] in
 theorem masked_union (D : Actions I E) (Δ : ℕ) (ω : E → Bool) :
    (univ.filter (fun e => ω e=true)).biUnion (countErase D Δ)=
      (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω).biUnion D.erase := by
  ext i
  simp only [mem_biUnion,mem_filter,mem_univ,true_and,PhysicalBatchLaw.unbalanced]
  constructor
  · rintro ⟨e,he,hi⟩
    by_cases hb : e ∈ balancedActions D Δ
    · simp only [countErase,ite_eq_left hb,Finset.notMem_empty] at hi
    · exact ⟨e,⟨he,hb⟩,by simpa only [countErase,ite_eq_right hb] using hi⟩
  · rintro ⟨e,⟨he,hb⟩,hi⟩
    exact ⟨e,he,by simpa only [countErase,ite_eq_right hb] using hi⟩

omit [Fintype I] in
 theorem masked_openings (D : Actions I E) (Δ : ℕ) (ω : E → Bool) :
    (∑ e, countOpening D Δ e*CountStatistic.bit ω e)=
    (((PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω) ∩ D.ordinary).card:ℝ) := by
  have heq : (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω ∩ D.ordinary) =
      univ.filter (fun e => ω e=true ∧ e ∉ balancedActions D Δ ∧ e ∈ D.ordinary) := by
    ext e
    simp [PhysicalBatchLaw.unbalanced, and_assoc]
  rw [heq, ← sum_boole]
  apply sum_congr rfl
  intro e _
  simp only [countOpening,CountStatistic.bit]
  split_ifs <;> simp_all

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalCountGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

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

 theorem unbalanced_count_change_s35_oai (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (ω : HeavyAction (graphActions G) H → Bool) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
    let D := heavyActions (graphActions G) H
    let Z := PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω
    mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤
      (H.card:ℝ)+CountStatistic.statistic
        (fun e => countOpening D Δ e-mass g (countErase D Δ e))
        (fun e f => g*(CountGeometry.overlap (countErase D Δ) e f:ℝ)) ω := by
  dsimp only
  have hn := round_count_change A G H (PhysicalBatchLaw.unbalanced (balancedActions (heavyActions (graphActions G) H) Δ) ω) hg hunit
  have hs := CountGeometry.selected_mass_bound (countErase (heavyActions (graphActions G) H) Δ)
    (countOpening (heavyActions (graphActions G) H) Δ) hg ω
  rw [masked_openings,masked_union] at hs
  dsimp only [mass] at hn hs ⊢
  linarith only [hn,hs]

end MetricKMedian.CopyState
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.CopyState.unbalanced_count_change_s35_oai.{u_1} := @OAI.MetricKMedian.CopyState.unbalanced_count_change_s35_oai.{u_1}
