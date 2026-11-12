-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:51.317203+00:00
-- url     : https://prove2.me/submissions/2a4ea4eb-66cc-4027-9bac-4a5f0f4f6d27

import Mathlib
import Definitions.Def_Q238L004
import Definitions.Def_Q238L012

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BottomMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
lemma separated_sum_le {α : Type*} [DecidableEq α] (v : α→ℝ) (S Y : Finset α)
    (hc : S.card=Y.card) (h : ∀ s∈S,∀ y∈Y,y∉S→v s≤v y) :
    ∑ s∈S,v s≤∑ y∈Y,v y := by
  have hd : (S\Y).card=(Y\S).card := by
    rw [Finset.card_sdiff,Finset.card_sdiff,Finset.inter_comm Y S,hc]
  by_cases hn : (S\Y).Nonempty
  · obtain ⟨m,hm,hmax⟩:=(S\Y).exists_max_image v hn
    have hl := Finset.sum_le_sum (s:=S\Y) (fun s hs=>hmax s hs)
    have hr := Finset.sum_le_sum (s:=Y\S) (fun y hy=>h m (Finset.mem_sdiff.mp hm).1 y
      (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2)
    simp only [Finset.sum_const,nsmul_eq_mul] at hl hr
    have hs := Finset.sum_inter_add_sum_sdiff S Y v
    have hy := Finset.sum_inter_add_sum_sdiff Y S v
    rw [Finset.inter_comm Y S] at hy
    rw [hd] at hl
    linarith
  · have hz : S\Y=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
    have hsub : S⊆Y:=Finset.sdiff_eq_empty_iff_subset.mp hz
    exact (congrArg (fun U : Finset α=>∑ u∈U,v u) (Finset.eq_of_subset_of_card_le hsub hc.ge)).le

variable {α : Type*} [LinearOrder α]
lemma bottomSet_subset (U : Finset α) (k : ℕ) : bottomSet U k⊆U := by
  intro x hx
  exact (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))
lemma bottomSet_card (U : Finset α) (k : ℕ) : (bottomSet U k).card=min k U.card := by
  rw [bottomSet,List.toFinset_card_of_nodup ((U.sort_nodup (·≤·)).sublist (List.take_sublist _ _)),List.length_take,Finset.length_sort]
lemma bottomSet_separated (U : Finset α) (k : ℕ) (x : α) (hx : x∈bottomSet U k)
    (y : α) (hy : y∈U) (hn : y∉bottomSet U k) : x<y := by
  have hp := (Finset.sortedLT_sort U).pairwise
  have hpair : ((U.sort (·≤·)).take k++(U.sort (·≤·)).drop k).Pairwise (·<·) := by
    rw [List.take_append_drop]
    exact hp
  have hy' : y∈(U.sort (·≤·)).drop k := by
    have hm := (Finset.mem_sort (·≤·)).mpr hy
    rw [←List.take_append_drop k (U.sort (·≤·)),List.mem_append] at hm
    exact hm.resolve_left (fun h=>hn (List.mem_toFinset.mpr h))
  exact (List.pairwise_append.mp hpair).2.2 x (List.mem_toFinset.mp hx) y hy'
lemma bottomSet_sum_le (v : α→ℝ) (hv : Monotone v) (U : Finset α) (k : ℕ)
    (Y : Finset α) (hY : Y⊆U) (hc : Y.card=min k U.card) :
    ∑ x∈bottomSet U k,v x≤∑ y∈Y,v y := by
  apply separated_sum_le v _ Y ((bottomSet_card U k).trans hc.symm)
  intro x hx y hy hn
  exact hv (le_of_lt (bottomSet_separated U k x hx y (hY hy) hn))
end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFillMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.Canonical
variable {E V : Type*} [DecidableEq E] [DecidableEq V] {a : ℕ}
omit [DecidableEq E] in
lemma pick_part (part : E→Fin a) (o : Fin a→E) (ho : ∀ j,part (o j)=j) (xs : List E) (j : Fin a) :
    part (pick part o xs j)=j := by
  unfold pick
  cases he : xs.filter (fun e=>part e=j) with
  | nil=>exact ho j
  | cons e es=>
    have hm : e∈xs.filter (fun e=>part e=j) := by rw [he]; exact List.mem_cons_self
    exact of_decide_eq_true (List.mem_filter.mp hm).2
lemma pick_covers (part : E→Fin a) (o : Fin a→E) (xs : List E)
    (hX : ∀ j,(xs.toFinset.filter (fun e=>part e=j)).card≤1) (e : E) (he : e∈xs) :
    pick part o xs (part e)=e := by
  unfold pick
  have hm : e∈xs.filter (fun x=>part x=part e) := List.mem_filter.mpr ⟨he,by simp only [decide_true]⟩
  cases hx : xs.filter (fun x=>part x=part e) with
  | nil=>rw [hx] at hm; exact False.elim (List.not_mem_nil hm)
  | cons f fs=>
    have hf : f∈xs.filter (fun x=>part x=part e) := by rw [hx]; exact List.mem_cons_self
    have hf' := List.mem_filter.mp hf
    change f=e
    exact (Finset.card_le_one.mp (hX (part e))) f
      (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hf'.1,of_decide_eq_true hf'.2⟩) e
      (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he,rfl⟩)
omit [DecidableEq E] in
lemma filled_subset (F : Finset V) (part : E→Fin a) (o : Fin a→E) (loc : E→V)
    (hloc : ∀ e,loc e∈F) (xs : List E) : filled part o loc xs⊆F := by
  intro x hx
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx
  exact hloc _
omit [DecidableEq E] in
lemma filled_card (part : E→Fin a) (o : Fin a→E) (loc : E→V) (xs : List E) :
    (filled part o loc xs).card≤a := (Finset.card_image_le).trans (by simp)
lemma filled_covers (part : E→Fin a) (o : Fin a→E) (loc : E→V) (xs : List E)
    (hX : ∀ j,(xs.toFinset.filter (fun e=>part e=j)).card≤1) : ∀ e∈xs.toFinset,loc e∈filled part o loc xs := by
  intro e he
  exact Finset.mem_image.mpr ⟨part e,Finset.mem_univ _,by
    simp only [Function.comp_apply,pick_covers part o xs hX e (List.mem_toFinset.mp he)]⟩
omit [DecidableEq E] in
lemma filled_ball [PseudoMetricSpace V] (part : E→Fin a) (o : Fin a→E) (ho : ∀ j,part (o j)=j)
    (loc : E→V) (w : Fin a→V) (radius : Fin a→ℝ)
    (hball : ∀ e,dist (w (part e)) (loc e) ≤ radius (part e)) (xs : List E) :
    ∀ i,∃ x∈filled part o loc xs,dist (w i) x ≤ radius i := by
  intro i
  refine ⟨loc (pick part o xs i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,?_⟩
  simpa only [pick_part part o ho xs] using hball (pick part o xs i)
end MetricKMedianRecovery.Completion.Canonical
namespace MetricKMedianRecovery.Completion.Canonical
variable {V : Type*} [LinearOrder V]
lemma subset_pad (F U : Finset V) (n : ℕ) : U⊆pad F U n := Finset.subset_union_left
lemma pad_subset (F U : Finset V) (n : ℕ) (hUF : U⊆F) : pad F U n⊆F :=
  Finset.union_subset hUF ((bottomSet_subset _ _).trans Finset.sdiff_subset)
lemma pad_card (F U : Finset V) (n : ℕ) (hUF : U⊆F) (hUn : U.card≤n) (hnF : n≤F.card) :
    (pad F U n).card=n := by
  have hd : Disjoint U (bottomSet (F\U) (n-U.card)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    exact (Finset.mem_sdiff.mp (bottomSet_subset _ _ hb)).2 hx
  rw [pad,Finset.card_union_of_disjoint hd,bottomSet_card,Finset.card_sdiff_of_subset hUF,
    min_eq_left (Nat.sub_le_sub_right hnF _)]
  omega
lemma pad_nonempty (F U : Finset V) (n : ℕ) (hUF : U⊆F) (hUn : U.card≤n) (hnF : n≤F.card) (hn : 0<n) :
    (pad F U n).Nonempty := Finset.card_pos.mp (by rw [pad_card F U n hUF hUn hnF]; exact hn)
end MetricKMedianRecovery.Completion.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Score
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {E R : Type*} [Fintype R]

lemma le_topSum {q : ℕ} (v : R → ℝ) {S : Finset R}
    (hS : S.card = min q (Fintype.card R)) : (∑ s ∈ S, v s) ≤ topSum q v := by
  apply Finset.le_sup' (f := fun S => ∑ s ∈ S, v s)
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  exact hS

lemma topSum_le {q : ℕ} {v : R → ℝ} {a : ℝ}
    (h : ∀ S : Finset R, S.card = min q (Fintype.card R) → (∑ s ∈ S, v s) ≤ a) :
    topSum q v ≤ a := by
  apply Finset.sup'_le
  intro S hS
  exact h S (Finset.mem_powersetCard.mp hS).2

lemma topSum_attained (q : ℕ) (v : R → ℝ) :
    ∃ S : Finset R, S.card = min q (Fintype.card R) ∧ (∑ s ∈ S, v s) = topSum q v := by
  classical
  obtain ⟨S,hS,hm⟩ := Finset.exists_max_image
    (Finset.univ.powersetCard (min q (Fintype.card R)))
    (fun S => ∑ s ∈ S, v s) (Finset.powersetCard_nonempty.mpr (by simp))
  have hc := (Finset.mem_powersetCard.mp hS).2
  refine ⟨S,hc,le_antisymm (le_topSum v hc) ?_⟩
  exact topSum_le (fun T hT => hm T (by simp [Finset.mem_powersetCard, hT]))

lemma bottomSum_attained (q : ℕ) (v : R → ℝ) :
    ∃ S : Finset R, S.card = min q (Fintype.card R) ∧ (∑ s ∈ S, v s) = bottomSum q v := by
  obtain ⟨S,hS,hm⟩ := topSum_attained q (fun r => -v r)
  refine ⟨S,hS,?_⟩
  unfold bottomSum
  rw [← hm,Finset.sum_neg_distrib,neg_neg]

lemma bottomSum_le {q : ℕ} (v : R → ℝ) {S : Finset R}
    (hS : S.card = min q (Fintype.card R)) : bottomSum q v ≤ ∑ s ∈ S, v s := by
  have hh := le_topSum (fun r => -v r) hS
  simp only [Finset.sum_neg_distrib] at hh
  exact neg_le.mp (by simpa only [bottomSum] using hh)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Virtual
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_ball _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_permanent _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma virtualNearest_nonneg {a : ℕ} (S : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V)
    (hr : ∀ i, 0 ≤ radius i) (hM : 0 ≤ M) : 0 ≤ virtualNearest S w radius M x := by
  apply Finset.le_inf'
  intro t _
  cases t with
  | real s => exact dist_nonneg
  | ball i => exact add_nonneg dist_nonneg (hr i)
  | permanent => exact hM

omit [DecidableEq V] in
lemma distanceTo_le {S : Finset V} (hS : S.Nonempty) (x : V) {s : V} (hs : s ∈ S) :
    distanceTo S hS x ≤ dist x s := Finset.inf'_le _ hs

omit [DecidableEq V] in
lemma distanceTo_triangle (S : Finset V) (hS : S.Nonempty) (x y : V) :
    distanceTo S hS x ≤ dist x y + distanceTo S hS y := by
  obtain ⟨z,hz,hm⟩ := Finset.exists_min_image S (dist y) hS
  have he : dist y z = distanceTo S hS y :=
    le_antisymm (Finset.le_inf' hS _ hm) (Finset.inf'_le _ hz)
  exact (distanceTo_le hS x hz).trans (by rw [← he]; exact dist_triangle _ _ _)

lemma cappedCost_nonneg {E : Type*} (baseline : ℝ) (distance : E → ℝ) (X : Finset E)
    (hb : 0 ≤ baseline) (hd : ∀ e ∈ X, 0 ≤ distance e) :
    0 ≤ cappedCost baseline distance X := (Finset.le_fold_min _).mpr ⟨hb,hd⟩

lemma le_cappedCost {E : Type*} (baseline : ℝ) (distance : E → ℝ) (X : Finset E)
    {x : ℝ} (hb : x ≤ baseline) (hd : ∀ e ∈ X, x ≤ distance e) :
    x ≤ cappedCost baseline distance X := (Finset.le_fold_min _).mpr ⟨hb,hd⟩

omit [PseudoMetricSpace V] in

lemma completion_cardinality (S Q Red Blue Add : Finset V)
    (hQ : Q ⊆ S) (hRed : Red ⊆ S \ Q) (hBlue : Blue ⊆ S \ Q)
    (hRB : Disjoint Red Blue)
    (hcount : Add.card ≤ Q.card + Red.card + Blue.card) :
    ((S \ (Q ∪ Red ∪ Blue)) ∪ Add).card ≤ S.card := by
  have hQR : Disjoint Q Red := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hRed hx')).2 hx
  have hQB : Disjoint Q Blue := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hBlue hx')).2 hx
  have hd : Disjoint (Q ∪ Red) Blue := Finset.disjoint_union_left.mpr ⟨hQB,hRB⟩
  have hs : Q ∪ Red ∪ Blue ⊆ S :=
    Finset.union_subset (Finset.union_subset hQ (hRed.trans Finset.sdiff_subset))
      (hBlue.trans Finset.sdiff_subset)
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [Finset.card_union_of_disjoint hd,Finset.card_union_of_disjoint hQR] at hc
  exact (Finset.card_union_le _ _).trans (by omega)

omit [PseudoMetricSpace V] in
lemma assignmentWeight_sum {a : ℕ} (D : Finset V)
    (assignment : V → Virtual V a) (s : V) (charge : ℝ) :
    (∑ p ∈ D, if assignment p = Virtual.real s then charge else 0) =
      assignmentWeight D assignment s * charge := by
  rw [← Finset.sum_filter]
  simp [assignmentWeight]

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma virtual_domination {a : ℕ} (F U G : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (hUF : U ⊆ F) (hG : G ⊆ U)
    (hfill : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i)
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M) (x : V) :
    ∀ t ∈ withGhosts G, distanceTo U hU x ≤ virtualDistance w radius M x t := by
  intro t ht
  cases t with
  | real s => exact distanceTo_le hU x (hG (real_mem_withGhosts.mp ht))
  | ball i =>
    obtain ⟨u,hu,hb⟩ := hfill i
    exact (distanceTo_le hU x hu).trans
      ((dist_triangle x (w i) u).trans (by change dist x (w i) + dist (w i) u ≤ dist x (w i) + radius i; linarith))
  | permanent =>
    obtain ⟨u,hu⟩ := hU
    exact (distanceTo_le ⟨u,hu⟩ x hu).trans (hM x u (hUF hu))

lemma nearest_le_virtualNearest {a : ℕ} (F U G : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (hUF : U ⊆ F) (hG : G ⊆ U)
    (hfill : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i)
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M) (x : V) :
    distanceTo U hU x ≤ virtualNearest G w radius M x := by
  apply Finset.le_inf'
  exact virtual_domination F U G hU w radius M hUF hG hfill hM x

lemma nearest_le_redCost {E : Type*} {a : ℕ} (F U G : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ) (loc : E → V) (X : Finset E)
    (hUF : U ⊆ F) (hG : G ⊆ U)
    (hfill : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i)
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M) (hX : ∀ e ∈ X, loc e ∈ U) (s : V) :
    distanceTo U hU s ≤ cappedCost (virtualNearest G w radius M s) (fun e => dist s (loc e)) X := by
  apply le_cappedCost
  · exact nearest_le_virtualNearest F U G hU w radius M hUF hG hfill hM s
  · intro e he
    exact distanceTo_le hU s (hX e he)

omit [PseudoMetricSpace V] in

lemma sum_assignment_charges {a : ℕ} {R : Type*} (D : Finset V)
    (assignment : V → Virtual V a) (T : Finset R) (loc : R → V) (charge : R → ℝ) :
    (∑ p ∈ D, ∑ r ∈ T, if assignment p = Virtual.real (loc r) then charge r else 0) =
      ∑ r ∈ T, assignmentWeight D assignment (loc r) * charge r := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => assignmentWeight_sum D assignment (loc r) (charge r))

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_AssignmentChargesNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma assignment_charges_nonneg {a : ℕ} {R : Type*} (T : Finset R)
    (assignment : V → Virtual V a) (loc : R → V) (charge : R → ℝ)
    (hc : ∀ r ∈ T, 0 ≤ charge r) (p : V) :
    0 ≤ ∑ r ∈ T, if assignment p = Virtual.real (loc r) then charge r else 0 := by
  apply Finset.sum_nonneg
  intro r hr
  split_ifs
  · exact hc r hr
  · rfl

omit [PseudoMetricSpace V] in
lemma assignment_charge_le {a : ℕ} {R : Type*} (T : Finset R)
    (assignment : V → Virtual V a) (loc : R → V) (charge : R → ℝ)
    (hc : ∀ r ∈ T, 0 ≤ charge r) (p : V) {r : R} (hr : r ∈ T)
    (hp : assignment p = Virtual.real (loc r)) :
    charge r ≤ ∑ s ∈ T, if assignment p = Virtual.real (loc s) then charge s else 0 := by
  have hh := Finset.single_le_sum (s := T) (f := fun s =>
    if assignment p = Virtual.real (loc s) then charge s else 0)
    (fun s hs => by split_ifs; exact hc s hs; rfl) hr
  simpa only [ite_eq_left hp] using hh

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealizationChargingAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
open Categorical FiniteSampling
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma realization_charging_with_assignment {E R B : Type*} {a : ℕ}
    (D F H G U : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (assignment : V → Virtual V a)
    (hamem : ∀ p, assignment p ∈ withGhosts H)
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest H w radius M p)
    (loc : E → V) (X : Finset E) (Tred : Finset R) (Tblue : Finset B)
    (redLoc : R → V) (blueLoc blueDest : B → V)
    (hr : ∀ i, 0 ≤ radius i) (hM0 : 0 ≤ M)
    (hUF : U ⊆ F) (hG : G ⊆ U)
    (hfill : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i)
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M) (hX : ∀ e ∈ X, loc e ∈ U)
    (hblue : ∀ b ∈ Tblue, blueDest b ∈ U)
    (hcover : ∀ s ∈ H, s ∈ U ∨ (∃ r ∈ Tred, redLoc r = s) ∨
      (∃ b ∈ Tblue, blueLoc b = s)) :
    (∑ p ∈ D, distanceTo U hU p) ≤
      (∑ p ∈ D, cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X) +
      (∑ r ∈ Tred, assignmentWeight D assignment (redLoc r) *
        cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X) +
      ∑ b ∈ Tblue, assignmentWeight D assignment (blueLoc b) *
        dist (blueLoc b) (blueDest b) := by
  let redCost := fun r => cappedCost (virtualNearest G w radius M (redLoc r))
    (fun e => dist (redLoc r) (loc e)) X
  let blueCost := fun b => dist (blueLoc b) (blueDest b)
  let extraR := fun p => ∑ r ∈ Tred, if assignment p = Virtual.real (redLoc r) then redCost r else 0
  let extraB := fun p => ∑ b ∈ Tblue, if assignment p = Virtual.real (blueLoc b) then blueCost b else 0
  have hrednn : ∀ r ∈ Tred, 0 ≤ redCost r := by
    intro r _
    exact cappedCost_nonneg _ _ X (virtualNearest_nonneg G w radius M (redLoc r) hr hM0)
      (fun _ _ => dist_nonneg)
  have hbluenn : ∀ b ∈ Tblue, 0 ≤ blueCost b := fun _ _ => dist_nonneg
  have hRnn (p : V) : 0 ≤ extraR p := assignment_charges_nonneg Tred assignment redLoc redCost hrednn p
  have hBnn (p : V) : 0 ≤ extraB p := assignment_charges_nonneg Tblue assignment blueLoc blueCost hbluenn p
  have hbase (p : V) : distanceTo U hU p ≤ virtualNearest H w radius M p + extraR p + extraB p := by
    have ht := hamem p
    have hd := hadist p
    cases he : assignment p with
    | real s =>
      rw [he,real_mem_withGhosts] at ht
      simp only [he,virtualDistance] at hd
      rcases hcover s ht with hs | ⟨r,hrm,rfl⟩ | ⟨b,hbm,rfl⟩
      · have hl := distanceTo_le hU p hs
        linarith [hRnn p,hBnn p]
      · have hl := nearest_le_redCost F U G hU w radius M loc X hUF hG hfill hM hX (redLoc r)
        have hex : redCost r ≤ extraR p :=
          assignment_charge_le Tred assignment redLoc redCost hrednn p hrm he
        have htri := distanceTo_triangle U hU p (redLoc r)
        linarith [hBnn p]
      · have hl := distanceTo_le hU (blueLoc b) (hblue b hbm)
        have hex : blueCost b ≤ extraB p :=
          assignment_charge_le Tblue assignment blueLoc blueCost hbluenn p hbm he
        have htri := distanceTo_triangle U hU p (blueLoc b)
        linarith [hRnn p]
    | ball i =>
      have hz := virtual_domination F U G hU w radius M hUF hG hfill hM p
        (Virtual.ball i) (ball_mem_withGhosts G i)
      rw [he] at hd
      linarith [hRnn p,hBnn p]
    | permanent =>
      have hz := virtual_domination F U G hU w radius M hUF hG hfill hM p
        Virtual.permanent (permanent_mem_withGhosts G)
      rw [he] at hd
      linarith [hRnn p,hBnn p]
  have hpoint (p : V) : distanceTo U hU p ≤
      cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X + extraR p + extraB p := by
    have hh := le_cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X
      (show distanceTo U hU p-extraR p-extraB p ≤ virtualNearest H w radius M p by linarith [hbase p])
      (fun e he => by have h := distanceTo_le hU p (hX e he); linarith [hRnn p,hBnn p])
    linarith
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ D) => hpoint p)
  simp only [Finset.sum_add_distrib] at hsum
  have hRsum := sum_assignment_charges D assignment Tred redLoc redCost
  have hBsum := sum_assignment_charges D assignment Tblue blueLoc blueCost
  change (∑ p ∈ D,extraR p) = _ at hRsum
  change (∑ p ∈ D,extraB p) = _ at hBsum
  rw [hRsum,hBsum] at hsum
  exact hsum

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionRealizeMath
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_ball _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_permanent _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.Canonical
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
lemma realize_spec {E R B : Type*} [DecidableEq E] [Fintype R] [Fintype B]
    [DecidableEq R] {a c q : ℕ}
    (D F S Q G : Finset V) (hS : S ⊆ F) (hn : S.Nonempty) (hQ : Q ⊆ S)
    (part : E → Fin a) (o : Fin a → E) (ho : ∀ j,part (o j)=j) (loc : E → V)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (assignment : V → Virtual V a)
    (hamem : ∀ p, assignment p ∈ withGhosts (S \ Q))
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest (S \ Q) w radius M p)
    (hr : ∀ i, 0 ≤ radius i) (hM0 : 0 ≤ M)
    (hloc : ∀ e, loc e ∈ F) (hball : ∀ e, dist (w (part e)) (loc e) ≤ radius (part e))
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M)
    (redLoc : R → V) (blueLoc blueDest : B → V)
    (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
    (hred : ∀ r, redLoc r ∈ S \ Q) (hblue : ∀ b, blueLoc b ∈ S \ Q)
    (hRB : ∀ r b, redLoc r ≠ blueLoc b)
    (hG : G ⊆ S \ Q) (hGR : ∀ r, redLoc r ∉ G) (hGB : ∀ b, blueLoc b ∉ G)
    (hdest : ∀ b, blueDest b ∈ F) (hdestCount : (Finset.univ.image blueDest).card ≤ c)
    (hcount : a+c ≤ Q.card+q+Fintype.card B)
    (K : ℝ)
    (hK : (∑ b, assignmentWeight D assignment (blueLoc b) *
      dist (blueLoc b) (blueDest b)) ≤ K)
    (xs : List E) (hX : ∀ j, (xs.toFinset.filter (fun e => part e = j)).card ≤ 1)
    (T : Finset R) (hT : T.card=q) :
    let X := xs.toFinset
    let U := realize F S Q part o loc redLoc blueLoc blueDest xs T
    U ⊆ F ∧ U.card = S.card ∧ ∃ hU : U.Nonempty,
      (∑ p ∈ D, distanceTo U hU p) ≤
        K + (∑ p ∈ D, cappedCost (virtualNearest (S \ Q) w radius M p) (fun e => dist p (loc e)) X) +
        (∑ r∈T,assignmentWeight D assignment (redLoc r) *
          cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X) := by
  classical
  let X := xs.toFinset
  change _ ∧ _ ∧ _
  let Red := T.image redLoc
  let Blue := Finset.univ.image blueLoc
  let Dest := Finset.univ.image blueDest
  have hRcard : Red.card = q := by rw [Finset.card_image_of_injective _ hredInj,hT]
  have hBcard : Blue.card = Fintype.card B := by simp [Blue,Finset.card_image_of_injective _ hblueInj]
  have hRsub : Red ⊆ S \ Q := by
    intro s hs
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hs
    exact hred r
  have hBsub : Blue ⊆ S \ Q := by
    intro s hs
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hs
    exact hblue b
  have hRBD : Disjoint Red Blue := by
    apply Finset.disjoint_left.mpr
    intro s hs hs'
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b,_,he⟩ := Finset.mem_image.mp hs'
    exact hRB r b he.symm
  let Filled := filled part o loc xs
  have hFF := filled_subset F part o loc hloc xs
  have hFc : Filled.card≤a := filled_card part o loc xs
  have hFX := filled_covers part o loc xs hX
  have hFi := filled_ball part o ho loc w radius hball xs
  have hDF : Dest ⊆ F := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hx
    exact hdest b
  have hAddc : (Filled ∪ Dest).card ≤ Q.card + Red.card + Blue.card := by
    have hd : Dest.card ≤ c := hdestCount
    have hh := Finset.card_union_le Filled Dest
    rw [hRcard,hBcard]
    omega
  let U₀ := (S \ (Q ∪ Red ∪ Blue)) ∪ (Filled ∪ Dest)
  have h₀ : U₀ ⊆ F := Finset.union_subset (Finset.sdiff_subset.trans hS) (Finset.union_subset hFF hDF)
  have hc₀ : U₀.card≤S.card := completion_cardinality S Q Red Blue (Filled∪Dest) hQ hRsub hBsub hRBD hAddc
  let U := pad F U₀ S.card
  have hUF := pad_subset F U₀ S.card h₀
  have hUc := pad_card F U₀ S.card h₀ hc₀ (Finset.card_le_card hS)
  have hUn := pad_nonempty F U₀ S.card h₀ hc₀ (Finset.card_le_card hS) (Finset.card_pos.mpr hn)
  have hU₀ := subset_pad F U₀ S.card
  have hFU : Filled ⊆ U := by
    intro f hf
    exact hU₀ (Finset.mem_union_right _ (Finset.mem_union_left _ hf))
  have hDU : Dest ⊆ U := by
    intro d hd
    exact hU₀ (Finset.mem_union_right _ (Finset.mem_union_right _ hd))
  have hGU : G ⊆ U := by
    intro s hs
    apply hU₀
    apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp (hG hs)).1,?_⟩
    intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.mem_sdiff.mp (hG hs)).2 hb
      · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hb
        exact hGR r hs
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
      exact hGB b hs
  have hFillU : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i := by
    intro i
    obtain ⟨u,hu,hb⟩ := hFi i
    exact ⟨u,hFU hu,hb⟩
  have hXU : ∀ e ∈ X, loc e ∈ U := fun e he => hFU (hFX e he)
  have hBlueU : ∀ b ∈ (Finset.univ : Finset B), blueDest b ∈ U := by
    intro b _
    exact hDU (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩)
  have hcover : ∀ s ∈ S \ Q, s ∈ U ∨ (∃ r ∈ T, redLoc r = s) ∨
      (∃ b ∈ (Finset.univ : Finset B), blueLoc b = s) := by
    intro s hs
    by_cases hR : s ∈ Red
    · exact Or.inr (Or.inl (Finset.mem_image.mp hR))
    by_cases hB : s ∈ Blue
    · exact Or.inr (Or.inr (Finset.mem_image.mp hB))
    apply Or.inl
    apply hU₀
    apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp hs).1,?_⟩
    simp only [Finset.mem_union,not_or]
    exact ⟨⟨(Finset.mem_sdiff.mp hs).2,hR⟩,hB⟩
  have hh := realization_charging_with_assignment D F (S \ Q) G U hUn w radius M assignment hamem hadist loc X T Finset.univ
    redLoc blueLoc blueDest hr hM0 hUF hGU hFillU hM hXU hBlueU hcover
  refine ⟨hUF,hUc,hUn,?_⟩
  refine hh.trans ?_
  dsimp only [X]
  linarith

end MetricKMedianRecovery.Completion.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordList BinaryArithmetic
lemma capped_cast {E : Type*} (b : ℚ) (d : E→ℚ) (S : Finset E) :
    (capped b d S:ℝ)=Completion.cappedCost (b:ℝ) (fun e=>(d e:ℝ)) S := by
  classical
  induction S using Finset.induction_on with
  | empty=>rfl
  | @insert e S he ih=>
    simp only [capped,Completion.cappedCost,Finset.fold_insert he,Rat.cast_min] at *
    rw [ih]

end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordList BinaryArithmetic
lemma ranking_injective {r : ℕ} (v : Fin r→ℚ) : Function.Injective (ranking v) := by
  intro i j h
  exact Fin.ext (congrArg (fun p=> (ofLex p).2) h)
lemma rank_value_mono : Monotone (fun p : ℚ ×ₗ ℕ=>((ofLex p).1:ℝ)) := by
  intro x y h
  exact Rat.cast_le.mpr (Prod.Lex.le_iff'.mp h).1
lemma bottom_sum_cast {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    ((bottomValues v k).sum:ℝ)= Completion.bottomSum k (fun i=>(v i:ℝ)) := by
  classical
  let U:=Finset.univ.image (ranking v)
  let B:=Completion.bottomSet U k
  have hU : U.card=r := by simp [U,Finset.card_image_of_injective _ (ranking_injective v)]
  have hB := Completion.bottomSet_subset U k
  obtain ⟨S,_,hS⟩:=Finset.subset_image_iff.mp hB
  have hc : S.card=min k (Fintype.card (Fin r)) := by
    have he:=Completion.bottomSet_card U k
    rw [←hS,Finset.card_image_of_injective _ (ranking_injective v),hU] at he
    simpa using he
  have he : (∑ p∈B,((ofLex p).1:ℝ))=∑ i∈S,(v i:ℝ) := by
    rw [show B=S.image (ranking v) from hS.symm,Finset.sum_image (ranking_injective v).injOn]
    rfl
  have hn := (U.sort_nodup (·≤·)).sublist (List.take_sublist k (U.sort (·≤·)))
  have hb : ((bottomValues v k).sum:ℝ)=∑ p∈B,((ofLex p).1:ℝ) := by
    rw [Rat.cast_list_sum]
    simp only [bottomValues,List.map_map,Function.comp_def]
    exact (List.sum_toFinset _ hn).symm
  rw [hb]
  apply le_antisymm
  · obtain ⟨Y,hY,eY⟩:=Completion.bottomSum_attained k (fun i=>(v i:ℝ))
    have h := Completion.bottomSet_sum_le (fun p : ℚ ×ₗ ℕ=>((ofLex p).1:ℝ)) rank_value_mono U k
      (Y.image (ranking v)) (Finset.image_subset_image (Finset.subset_univ Y)) (by
        rw [Finset.card_image_of_injective _ (ranking_injective v),hU]
        simpa using hY)
    rw [Finset.sum_image (ranking_injective v).injOn] at h
    exact h.trans_eq eY
  · rw [he]
    exact Completion.bottomSum_le _ hc

end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBottomIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordList BinaryArithmetic
lemma indexSet_image {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    (indexSet v k).image (ranking v)=Completion.bottomSet (Finset.univ.image (ranking v)) k := by
  classical
  ext p
  simp only [Finset.mem_image,indexSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact hi
  · intro hp
    obtain ⟨i,_,he⟩:=Finset.mem_image.mp (Completion.bottomSet_subset _ _ hp)
    exact ⟨i,he ▸ hp,he⟩
lemma indexSet_card {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : (indexSet v k).card=min k r := by
  rw [←Finset.card_image_of_injective _ (ranking_injective v),indexSet_image,Completion.bottomSet_card,
    Finset.card_image_of_injective _ (ranking_injective v),Finset.card_univ,Fintype.card_fin]
lemma indexSet_sum {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    ∑ i∈indexSet v k,(v i:ℝ)=Completion.bottomSum k (fun i=>(v i:ℝ)) := by
  classical
  rw [←bottom_sum_cast]
  have hn:=((Finset.univ.image (ranking v)).sort_nodup (·≤·)).sublist (List.take_sublist k _)
  have h:=List.sum_toFinset (fun p : ℚ ×ₗ ℕ=>((ofLex p).1:ℝ)) hn
  rw [show (((Finset.univ.image (ranking v)).sort (·≤·)).take k).toFinset=
    (indexSet v k).image (ranking v) from (indexSet_image v k).symm,
    Finset.sum_image (ranking_injective v).injOn] at h
  rw [Rat.cast_list_sum]
  simpa only [bottomValues,List.map_map,Function.comp_def,ranking,ofLex_toLex] using h
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFairCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α β : Type*} [LinearOrder α] [AddCommMonoid β]
lemma sum_enum (S : Finset α) (f : α→β) : (∑ i:Fin S.card,f (enum S i))=∑ x∈S,f x := by
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ enum S)).sum = _
  rw [←List.map_ofFn,enum_list,←List.sum_toFinset f (S.sort_nodup (·≤·)),Finset.sort_toFinset]
end MetricKMedianRecovery.SortedIndex
namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open Completion
variable {n q a r b : ℕ} [PseudoMetricSpace (Fin n)]
lemma realize_le_surrogate_s238r_oai
    (D F S Q G : Finset (Fin n)) (hS : S⊆F) (hn : S.Nonempty) (hQ : Q⊆S)
    (part : Fin q→Fin a) (o : Fin a→Fin q) (ho : ∀ j,part (o j)=j) (loc : Fin q→Fin n)
    (w : Fin a→Fin n) (radius : Fin a→ℝ) (M : ℝ)
    (assignment : Fin n→Virtual (Fin n) a)
    (hamem : ∀ p,assignment p∈withGhosts (S\Q))
    (hadist : ∀ p,virtualDistance w radius M p (assignment p)=virtualNearest (S\Q) w radius M p)
    (hr : ∀ i,0 ≤ radius i) (hM0 : 0≤M)
    (hloc : ∀ e,loc e∈F) (hball : ∀ e,dist (w (part e)) (loc e) ≤ radius (part e))
    (hM : ∀ x,∀ f∈F,dist x f≤M)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n)
    (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
    (hred : ∀ i,redLoc i∈S\Q) (hblue : ∀ i,blueLoc i∈S\Q)
    (hRB : ∀ i j,redLoc i≠blueLoc j)
    (hG : G⊆S\Q) (hGR : ∀ i,redLoc i∉G) (hGB : ∀ i,blueLoc i∉G)
    (hdest : ∀ i,blueDest i∈F) (c k : ℕ) (hdestCount : (Finset.univ.image blueDest).card ≤ c)
    (hcount : a+c≤Q.card+k+b) (hk : k ≤ r) (K : ℝ)
    (hK : (∑ i,assignmentWeight D assignment (blueLoc i)*dist (blueLoc i) (blueDest i))≤K)
    (base : Fin D.card→ℚ) (distance : Fin D.card→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (hbase : ∀ i,(base i:ℝ)=virtualNearest (S\Q) w radius M (SortedIndex.enum D i))
    (hdistance : ∀ i e,(distance i e:ℝ)=dist (SortedIndex.enum D i) (loc e))
    (hweight : ∀ i,(weight i:ℝ)=assignmentWeight D assignment (redLoc i))
    (hredBase : ∀ i,(redBase i:ℝ)=virtualNearest G w radius M (redLoc i))
    (hredDistance : ∀ i e,(redDistance i e:ℝ)=dist (redLoc i) (loc e))
    (xs : List (Fin q)) (hX : Categorical.PartitionFeasible part xs.toFinset) :
    let T:=BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k
    let U:=Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs T
    U⊆F ∧ U.card=S.card ∧ ∃ hU:U.Nonempty,
      (∑ p∈D,distanceTo U hU p)≤
        surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
          (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) xs.toFinset := by
  let T:=BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k
  have hT : T.card=k := by rw [BinaryRationalSort.indexSet_card,Nat.min_eq_left hk]
  have hc : a+c≤Q.card+k+Fintype.card (Fin b) := by simpa only [Fintype.card_fin] using hcount
  have hh:=Canonical.realize_spec D F S Q G hS hn hQ part o ho loc w radius M assignment hamem hadist hr hM0 hloc hball hM
    redLoc blueLoc blueDest hredInj hblueInj hred hblue hRB hG hGR hGB hdest hdestCount hc K hK xs hX T hT
  obtain ⟨hF,hcard,hU,hcost⟩:=hh
  refine ⟨hF,hcard,hU,?_⟩
  have hclients : (∑ i:Fin D.card,cappedCost (base i:ℝ) (fun e=>(distance i e:ℝ)) xs.toFinset)=
      ∑ p∈D,cappedCost (virtualNearest (S\Q) w radius M p) (fun e=>dist p (loc e)) xs.toFinset := by
    simp_rw [hbase,hdistance]
    exact SortedIndex.sum_enum D (fun p => cappedCost (virtualNearest (S\Q) w radius M p) (fun e=>dist p (loc e)) xs.toFinset)
  have hreds : (∑ i∈T,assignmentWeight D assignment (redLoc i)*
      cappedCost (virtualNearest G w radius M (redLoc i)) (fun e=>dist (redLoc i) (loc e)) xs.toFinset)=
      bottomSum k (fun i=>(weight i:ℝ)*cappedCost (redBase i:ℝ) (fun e=>(redDistance i e:ℝ)) xs.toFinset) := by
    have hh:=BinaryRationalSort.indexSet_sum (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k
    simp only [Rat.cast_mul,BinaryCompletion.capped_cast] at hh
    simpa only [hweight,hredBase,hredDistance] using hh
  exact hcost.trans_eq (by rw [surrogate,hclients,←hreds])
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238r_oai
