-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:19.057574+00:00
-- url     : https://prove2.me/submissions/b682a641-ab0f-47bd-b9e9-b40eb879d442

import Mathlib
import Definitions.Def_Q238L008
import Definitions.Def_Q238L010
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionAlgorithm_sixtyTwoFin_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionFair_realize_le_surrogate_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : average X ≤ average Y :=
  Finset.expect_le_expect (fun ω _ => h ω)

lemma average_sub (X Y : Ω → ℝ) :
    average (fun ω => X ω - Y ω) = average X - average Y :=
  Finset.expect_sub_distrib _ _ _

end Average

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Table
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

open FiniteSampling
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

omit [Fintype E] [Fintype Ω] [Nonempty Ω] in
lemma mem_draw {a : ℕ} (r : Fin a → Table Ω E) (seed : Fin a → Ω)
    (S : Finset E) (e : E) :
    e ∈ draw a r seed S ↔ e ∈ S ∨ ∃ j, r j (seed j) = some e := by
  induction a with
  | zero => simp [draw]
  | succ a ih =>
    simp only [draw]
    have he : (∃ j : Fin (a+1), r j (seed j) = some e) ↔
      r 0 (seed 0) = some e ∨ ∃ j : Fin a, r j.succ (seed j.succ) = some e := Fin.exists_fin_succ
    rw [he]
    cases h : r 0 (seed 0) with
    | none => simpa [put, h, Fin.tail_def] using ih (Fin.tail r) (Fin.tail seed)
    | some f =>
      simp only [put, Finset.mem_insert, ih, Fin.tail_def, Option.some.injEq]
      tauto

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Advance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling

lemma adaptiveRun_invariant {S Ω : Type*} (f : S → Ω → S) (Inv : S → Prop)
    (hInv : ∀ s, Inv s → ∀ ω, Inv (f s ω)) (n : ℕ)
    (s : S) (hs : Inv s) (seed : Fin n → Ω) : Inv (adaptiveRun f n s seed) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih _ (hInv s hs (seed 0)) (Fin.tail seed)

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_TableValue
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section GreedyStep
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

omit [Fintype E] in
lemma draw_feasible (part : E → Fin a) (s : GreedyState E a T)
    (hs : GreedyInvariant part s) (seed : Fin a → Fin T) (j : Fin a) :
    ((draw a s.2 seed ∅).filter (fun e => part e = j)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he f hf
  obtain ⟨he,hpe⟩ := Finset.mem_filter.mp he
  obtain ⟨hf,hpf⟩ := Finset.mem_filter.mp hf
  obtain ⟨k,hk⟩ : ∃ k, s.2 k (seed k) = some e := by simpa [mem_draw] using he
  obtain ⟨l,hl⟩ : ∃ l, s.2 l (seed l) = some f := by simpa [mem_draw] using hf
  have hkl : k = l := (hs.1 k (seed k) e hk).symm.trans (hpe.trans (hpf.symm.trans
    (hs.1 l (seed l) f hl)))
  subst l
  exact Option.some.inj (hk.symm.trans hl)

end GreedyStep
end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

lemma initialState_invariant {E : Type*} {a T : ℕ} (part : E → Fin a) :
    GreedyInvariant part (initialState E a T) := by
  constructor
  · intro j ω e he
    change (none : Option E) = some e at he
    cases he
  · intro j ω h
    rfl

end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Selected
open FiniteSampling
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

omit [Fintype E] in
lemma greedyStep_invariant (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (s : GreedyState E a T) (hs : GreedyInvariant part s)
    (seed : OracleSeed E a T L) : GreedyInvariant part (greedyStep part rule g s seed) := by
  by_cases ht : s.1 < T
  · simp only [greedyStep, dite_eq_left ht, GreedyInvariant, advance]
    constructor
    · intro j ω e he
      by_cases hω : ω = (⟨s.1,ht⟩ : Fin T)
      · subst ω
        simp only [Function.update_self, Option.some.injEq] at he
        rw [← he]
        exact (rule.spec _ j).1
      · rw [Function.update_of_ne hω] at he
        exact hs.1 j ω e he
    · intro j ω hω
      have hne : ω ≠ (⟨s.1,ht⟩ : Fin T) := by
        intro he
        have := congrArg Fin.val he
        simp only at this
        omega
      rw [Function.update_of_ne hne]
      exact hs.2 j ω (by omega)
  · simpa only [greedyStep, dite_eq_right ht] using hs

omit [Fintype E] in
lemma greedyRun_invariant (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : Fin T → OracleSeed E a T L) :
    GreedyInvariant part (greedyRun part rule g seed) :=
  adaptiveRun_invariant _ (GreedyInvariant part) (greedyStep_invariant part rule g)
    T _ (initialState_invariant part) seed

omit [Fintype E] in
lemma greedyOutput_feasible (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T)) :
    ∀ j, ((greedyOutput part rule g seed).filter (fun e => part e = j)).card ≤ 1 := by
  intro j
  exact draw_feasible part _ (greedyRun_invariant part rule g seed.1) seed.2 j

end MetricKMedianRecovery.Categorical.Selected

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

lemma score_le_iff {baseline t : ℝ} {offer : E → ℝ} {X : Finset E} :
    score baseline offer X ≤ t ↔ baseline ≤ t ∧ ∀ e ∈ X, offer e ≤ t :=
  Finset.fold_max_le t

lemma le_score_iff {baseline t : ℝ} {offer : E → ℝ} {X : Finset E} :
    t ≤ score baseline offer X ↔ t ≤ baseline ∨ ∃ e ∈ X, t ≤ offer e :=
  Finset.le_fold_max t

lemma baseline_le_score (baseline : ℝ) (offer : E → ℝ) (X : Finset E) :
    baseline ≤ score baseline offer X := le_score_iff.mpr (Or.inl le_rfl)

lemma offer_le_score (baseline : ℝ) (offer : E → ℝ) {X : Finset E} {e : E}
    (he : e ∈ X) : offer e ≤ score baseline offer X :=
  le_score_iff.mpr (Or.inr ⟨e,he,le_rfl⟩)

lemma score_mono (baseline : ℝ) (offer : E → ℝ) : Monotone (score baseline offer) := by
  intro X Y hXY
  exact score_le_iff.mpr ⟨baseline_le_score _ _ _, fun e he => offer_le_score _ _ (hXY he)⟩

@[simp] lemma score_insert [DecidableEq E] (baseline : ℝ) (offer : E → ℝ) (X : Finset E) (e : E) :
    score baseline offer (insert e X) = max (offer e) (score baseline offer X) := by
  apply le_antisymm
  · apply score_le_iff.mpr
    refine ⟨(baseline_le_score _ _ _).trans (le_max_right _ _), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (offer_le_score _ _ hx).trans (le_max_right _ _)
  · exact max_le (offer_le_score _ _ (Finset.mem_insert_self _ _))
      (score_mono _ _ (Finset.subset_insert _ _))

lemma score_diminishing [DecidableEq E] (baseline : ℝ) (offer : E → ℝ) {X Y : Finset E}
    (hXY : X ⊆ Y) (e : E) :
    score baseline offer (insert e Y) - score baseline offer Y ≤
      score baseline offer (insert e X) - score baseline offer X := by
  rw [score_insert, score_insert]
  have hm := score_mono baseline offer hXY
  rcases le_total (offer e) (score baseline offer Y) with h | h
  · rw [max_eq_right h, sub_self]
    exact sub_nonneg.mpr (le_max_right _ _)
  · rw [max_eq_left h]
    have hh := le_max_left (offer e) (score baseline offer X)
    linarith

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

lemma topSum_mono (q : ℕ) {v w : R → ℝ} (h : ∀ s, v s ≤ w s) :
    topSum q v ≤ topSum q w := by
  apply topSum_le
  intro S hS
  exact (Finset.sum_le_sum (fun s _ => h s)).trans (le_topSum w hS)

lemma topSum_exchange (q : ℕ) (u v p r : R → ℝ)
    (hu : ∀ s, u s ≤ max (p s) (r s))
    (hv : ∀ s, v s ≤ min (p s) (r s))
    (huv : ∀ s, u s + v s ≤ p s + r s) :
    topSum q u + topSum q v ≤ topSum q p + topSum q r := by
  classical
  obtain ⟨I,hI,eI⟩ := topSum_attained q u
  obtain ⟨J,hJ,eJ⟩ := topSum_attained q v
  let C := I ∩ J
  let A := I \ J
  let B := J \ I
  let A₁ := A.filter (fun s => u s ≤ p s)
  let A₂ := A \ A₁
  have hA₁ : A₁ ⊆ A := Finset.filter_subset _ _
  have hA₂ : A₂ ⊆ A := Finset.sdiff_subset
  have hAC : Disjoint A C := by simp [A,C,Finset.disjoint_left]; tauto
  have hBC : Disjoint B C := by simp [B,C,Finset.disjoint_left]; tauto
  have hAB : Disjoint A B := by simp [A,B,Finset.disjoint_left]; tauto
  have hACard : A.card + C.card = I.card := Finset.card_sdiff_add_card_inter I J
  have hBCard : B.card + C.card = J.card := by
    simpa [B,C,Finset.inter_comm] using Finset.card_sdiff_add_card_inter J I
  have hABCard : A.card = B.card := by omega
  have hAparts : A₂.card + A₁.card = A.card := Finset.card_sdiff_add_card_eq_card hA₁
  obtain ⟨B₁,hB₁,hB₁card⟩ := Finset.exists_subset_card_eq
    (show A₂.card ≤ B.card by rw [← hABCard]; exact Finset.card_le_card hA₂)
  let B₂ := B \ B₁
  have hB₂ : B₂ ⊆ B := Finset.sdiff_subset
  have hBparts : B₂.card + B₁.card = B.card := Finset.card_sdiff_add_card_eq_card hB₁
  let K := C ∪ (A₁ ∪ B₁)
  let L := C ∪ (A₂ ∪ B₂)
  have hKA : Disjoint A₁ B₁ := hAB.mono hA₁ hB₁
  have hLA : Disjoint A₂ B₂ := hAB.mono hA₂ hB₂
  have hKC : Disjoint C (A₁ ∪ B₁) :=
    Finset.disjoint_union_right.mpr ⟨hAC.symm.mono_right hA₁,hBC.symm.mono_right hB₁⟩
  have hLC : Disjoint C (A₂ ∪ B₂) :=
    Finset.disjoint_union_right.mpr ⟨hAC.symm.mono_right hA₂,hBC.symm.mono_right hB₂⟩
  have hK : K.card = min q (Fintype.card R) := by
    simp only [K,Finset.card_union_of_disjoint hKC,Finset.card_union_of_disjoint hKA]
    omega
  have hL : L.card = min q (Fintype.card R) := by
    simp only [L,Finset.card_union_of_disjoint hLC,Finset.card_union_of_disjoint hLA]
    omega
  have hsI : (∑ s ∈ I,u s) = (∑ s ∈ C,u s) + (∑ s ∈ A,u s) := by
    exact (Finset.sum_inter_add_sum_sdiff I J u).symm
  have hsJ : (∑ s ∈ J,v s) = (∑ s ∈ C,v s) + (∑ s ∈ B,v s) := by
    simpa [C,B,Finset.inter_comm] using (Finset.sum_inter_add_sum_sdiff J I v).symm
  have hsA : (∑ s ∈ A,u s) = (∑ s ∈ A₁,u s) + (∑ s ∈ A₂,u s) := by
    simpa only [A₂,add_comm] using (Finset.sum_sdiff (f := u) hA₁).symm
  have hsB : (∑ s ∈ B,v s) = (∑ s ∈ B₁,v s) + (∑ s ∈ B₂,v s) := by
    simpa only [B₂,add_comm] using (Finset.sum_sdiff (f := v) hB₁).symm
  have hC : (∑ s ∈ C,u s) + (∑ s ∈ C,v s) ≤
      (∑ s ∈ C,p s) + (∑ s ∈ C,r s) := by
    simpa only [Finset.sum_add_distrib] using Finset.sum_le_sum (fun s (_ : s ∈ C) => huv s)
  have h₁ : (∑ s ∈ A₁,u s) ≤ (∑ s ∈ A₁,p s) :=
    Finset.sum_le_sum (fun s hs => (Finset.mem_filter.mp hs).2)
  have h₂ : (∑ s ∈ A₂,u s) ≤ (∑ s ∈ A₂,r s) := by
    apply Finset.sum_le_sum
    intro s hs
    have hs' := Finset.mem_sdiff.mp hs
    have hn : ¬u s ≤ p s := by
      intro hh
      exact hs'.2 (Finset.mem_filter.mpr ⟨hs'.1,hh⟩)
    exact (le_max_iff.mp (hu s)).resolve_left hn
  have h₃ : (∑ s ∈ B₁,v s) ≤ (∑ s ∈ B₁,p s) :=
    Finset.sum_le_sum (fun s _ => (hv s).trans (min_le_left _ _))
  have h₄ : (∑ s ∈ B₂,v s) ≤ (∑ s ∈ B₂,r s) :=
    Finset.sum_le_sum (fun s _ => (hv s).trans (min_le_right _ _))
  have hfront : (∑ s ∈ I,u s) + (∑ s ∈ J,v s) ≤
      (∑ s ∈ K,p s) + (∑ s ∈ L,r s) := by
    rw [hsI,hsJ,hsA,hsB]
    simp only [K,L,Finset.sum_union hKC,Finset.sum_union hKA,
      Finset.sum_union hLC,Finset.sum_union hLA]
    linarith
  rw [← eI,← eJ]
  exact hfront.trans (add_le_add (le_topSum p hK) (le_topSum r hL))

lemma topScores_diminishing [DecidableEq E] (q : ℕ)
    (baseline : R → ℝ) (offer : R → E → ℝ) {X Y : Finset E}
    (hXY : X ⊆ Y) (e : E) :
    topSum q (fun r => score (baseline r) (offer r) (insert e Y)) -
        topSum q (fun r => score (baseline r) (offer r) Y) ≤
    topSum q (fun r => score (baseline r) (offer r) (insert e X)) -
        topSum q (fun r => score (baseline r) (offer r) X) := by
  have hh := topSum_exchange q
    (fun r => score (baseline r) (offer r) (insert e Y))
    (fun r => score (baseline r) (offer r) X)
    (fun r => score (baseline r) (offer r) Y)
    (fun r => score (baseline r) (offer r) (insert e X))
  have h₁ : ∀ r, score (baseline r) (offer r) (insert e Y) ≤
      max (score (baseline r) (offer r) Y) (score (baseline r) (offer r) (insert e X)) := by
    intro r
    rw [score_insert,score_insert]
    exact max_le ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)
  have h₂ : ∀ r, score (baseline r) (offer r) X ≤
      min (score (baseline r) (offer r) Y) (score (baseline r) (offer r) (insert e X)) := by
    intro r
    exact le_min (score_mono _ _ hXY) (score_mono _ _ (Finset.subset_insert _ _))
  have h₃ : ∀ r, score (baseline r) (offer r) (insert e Y) + score (baseline r) (offer r) X ≤
      score (baseline r) (offer r) Y + score (baseline r) (offer r) (insert e X) := by
    intro r
    linarith [score_diminishing (baseline r) (offer r) hXY e]
  linarith [hh h₁ h₂ h₃]

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

lemma complement_cappedCost (C w baseline : ℝ) (distance : E → ℝ)
    (hw : 0 ≤ w) (X : Finset E) :
    C - w * cappedCost baseline distance X =
      score (C - w * baseline) (fun e => C - w * distance e) X := by
  classical
  induction X using Finset.induction_on with
  | empty => simp
  | @insert e X he ih =>
    simp only [cappedCost,Finset.fold_insert he,score_insert]
    change C-w*min (distance e) (cappedCost baseline distance X) = _
    rw [mul_min_of_nonneg _ _ hw,← max_sub_sub_left,ih]

variable {P : Type*} [Fintype P]

lemma saving_eq_scores (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (X : Finset E) :
    saving K q base distance weight redBase redDistance X =
      (∑ p, score 0 (fun e => base p - distance p e) X) +
      topSum q (fun r => score (-(weight r * redBase r))
        (fun e => -(weight r * redDistance r e)) X) -
      topSum q (fun r => -(weight r * redBase r)) := by
  have hbase (p : P) := complement_cappedCost (base p) 1 (base p) (distance p) (by norm_num) X
  simp only [one_mul,sub_self] at hbase
  have hred (r : R) := complement_cappedCost 0 (weight r) (redBase r) (redDistance r) (hw r) X
  simp only [zero_sub] at hred
  simp only [saving,surrogate,cappedCost_empty,bottomSum]
  simp only [hred,← hbase,Finset.sum_sub_distrib]
  ring

lemma saving_mono (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (hw : ∀ r, 0 ≤ weight r) :
    Monotone (saving K q base distance weight redBase redDistance) := by
  intro X Y hXY
  rw [saving_eq_scores K q base distance weight redBase redDistance hw X,
    saving_eq_scores K q base distance weight redBase redDistance hw Y]
  apply sub_le_sub_right
  apply add_le_add
  · exact Finset.sum_le_sum (fun p _ => score_mono 0 (fun e => base p-distance p e) hXY)
  · exact topSum_mono q (fun r => score_mono _ _ hXY)

lemma saving_diminishing [DecidableEq E] (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (hw : ∀ r, 0 ≤ weight r) {X Y : Finset E} (hXY : X ⊆ Y) (e : E) :
    saving K q base distance weight redBase redDistance (insert e Y) -
        saving K q base distance weight redBase redDistance Y ≤
    saving K q base distance weight redBase redDistance (insert e X) -
        saving K q base distance weight redBase redDistance X := by
  have hb := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
    score_diminishing 0 (fun e => base p-distance p e) hXY e)
  simp only [Finset.sum_sub_distrib] at hb
  have hr := topScores_diminishing q (fun r => -(weight r*redBase r))
    (fun r e => -(weight r*redDistance r e)) hXY e
  simp only [saving_eq_scores K q base distance weight redBase redDistance hw]
  linarith

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordList BinaryArithmetic
variable {E : Type*} {a T : ℕ}
lemma drawn_toFinset [DecidableEq E] (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) :
    (drawn r s).toFinset=Categorical.draw a r s ∅ := by
  ext e
  simp only [drawn,List.mem_toFinset,List.mem_flatten,List.mem_ofFn,
    Categorical.mem_draw,Finset.notMem_empty,false_or]
  aesop
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BottomMath
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordList BinaryArithmetic
variable {q p r : ℕ}
lemma surrogateQ_cast (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (S : Finset (Fin q)) :
    (surrogateQ k base distance weight redBase redDistance S:ℝ)=
      Completion.surrogate 0 k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) S := by
  simp only [surrogateQ,Rat.cast_add,Rat.cast_sum,BinaryRationalSort.bottom_sum_cast,
    Rat.cast_mul,capped_cast,Completion.surrogate,zero_add]
lemma savingQ_cast (K : ℝ) (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (S : Finset (Fin q)) :
    (savingQ k base distance weight redBase redDistance S:ℝ)=
      Completion.saving K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) S := by
  simp only [savingQ,Rat.cast_sub,surrogateQ_cast,Completion.saving,Completion.surrogate]
  ring
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CompletionAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open WordList BinaryArithmetic
variable {n q a p r b T L : ℕ}
lemma choices_toFinset (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    (choices k base distance weight redBase redDistance part hp seed).toFinset=
      Categorical.Selected.greedyOutput part (BinaryCategorical.rule part hp)
        (fun S=>(BinaryCompletion.savingQ k base distance weight redBase redDistance S:ℝ)) seed :=
  BinaryCategorical.drawn_toFinset _ _
lemma choices_feasible (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    Categorical.PartitionFeasible part (choices k base distance weight redBase redDistance part hp seed).toFinset := by
  rw [choices_toFinset]
  exact Categorical.Selected.greedyOutput_feasible _ _ _ _
end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchChecksCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open Categorical.Explicit
open MetricKMedianRecovery.Categorical
variable {q a p r : ℕ}
attribute [local irreducible] BinaryCategorical.rule exponent samples
lemma choices_binary (K : ℝ) (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (bits : BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) :
    (choices k base distance weight redBase redDistance part hp
      (binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits)).toFinset=
    Selected.binaryGreedyOutput part (BinaryCategorical.rule part hp)
      (Completion.saving K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ))) bits := by
  rw [choices_toFinset]
  have he : (fun S=>(BinaryCompletion.savingQ k base distance weight redBase redDistance S:ℝ))=
      Completion.saving K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) := by
    funext S
    exact BinaryCompletion.savingQ_cast K k base distance weight redBase redDistance S
  rw [he]
  rfl
lemma choices_expected (K : ℝ) (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part) (hw : ∀ i,0≤weight i)
    (X : Finset (Fin q)) (hX : PartitionFeasible part X) :
    FiniteSampling.average (fun bits : BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool =>
      Completion.surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ))
        (choices k base distance weight redBase redDistance part hp
          (binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits)).toFinset) ≤
      (38/100:ℝ)*Completion.surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) ∅ +
      (62/100:ℝ)*Completion.surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) X := by
  simp_rw [choices_binary K]
  let b : Fin p→ℝ := fun i=>(base i:ℝ)
  let d : Fin p→Fin q→ℝ := fun i e=>(distance i e:ℝ)
  let w : Fin r→ℝ := fun i=>(weight i:ℝ)
  let rb : Fin r→ℝ := fun i=>(redBase i:ℝ)
  let rd : Fin r→Fin q→ℝ := fun i e=>(redDistance i e:ℝ)
  have hw' : ∀ i,0≤w i := fun i=>Rat.cast_nonneg.mpr (hw i)
  have hh:=sixtyTwoFin_s238r part (BinaryCategorical.rule part hp) (Completion.saving K k b d w rb rd)
    (Completion.saving_mono K k b d w rb rd hw')
    (fun Y Z hYZ e=>Completion.saving_diminishing K k b d w rb rd hw' hYZ e)
    (Completion.saving_empty K k b d w rb rd) X hX
  simp only [Completion.saving,FiniteSampling.average_sub,FiniteSampling.average_const] at hh
  change _ ≤ 38/100*Completion.surrogate K k b d w rb rd ∅+62/100*Completion.surrogate K k b d w rb rd X
  linarith

end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CompletionResultGuarantee
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open Completion Categorical FiniteSampling
variable {n q a r b : ℕ} [PseudoMetricSpace (Fin n)]
lemma result_guarantee_s238r_oai
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
    (hp : Function.Surjective part) (hw : ∀ i,0≤weight i) :
    (∀ bits, result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits ⊆ F ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).card=S.card ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).Nonempty) ∧
    ∀ X, PartitionFeasible part X →
      average (fun bits=> realCost D (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits)) ≤
      (38/100:ℝ)*surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) ∅ +
      (62/100:ℝ)*surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) X := by
  have hh : ∀ bits,
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits)⊆F ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).card=S.card ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).Nonempty ∧
      realCost D (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits) ≤
        surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ))
        (BinaryCompletionAlgorithm.choices k base distance weight redBase redDistance part hp
          (binarySeedEquiv (Fin q) a (Explicit.exponent a) (Explicit.samples q a) bits)).toFinset := by
    intro bits
    have hh:=realize_le_surrogate_s238r D F S Q G hS hn hQ part o ho loc w radius M assignment hamem hadist hr hM0 hloc hball hM
      redLoc blueLoc blueDest hredInj hblueInj hred hblue hRB hG hGR hGB hdest c k hdestCount hcount hk K hK
      base distance weight redBase redDistance hbase hdistance hweight hredBase hredDistance
      (BinaryCompletionAlgorithm.choices k base distance weight redBase redDistance part hp
        (binarySeedEquiv (Fin q) a (Explicit.exponent a) (Explicit.samples q a) bits))
      (BinaryCompletionAlgorithm.choices_feasible k base distance weight redBase redDistance part hp _)
    obtain ⟨hF,hc,hn,hcost⟩:=hh
    refine ⟨hF,hc,hn,?_⟩
    unfold realCost
    split_ifs with hnon
    · exact hcost
    · exact False.elim (hnon hn)
  refine ⟨fun bits=>⟨(hh bits).1,(hh bits).2.1,(hh bits).2.2.1⟩,?_⟩
  intro X hX
  exact (average_mono (fun bits=>(hh bits).2.2.2)).trans
    (BinaryCompletionAlgorithm.choices_expected K k base distance weight redBase redDistance part hp hw X hX)
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r_oai
