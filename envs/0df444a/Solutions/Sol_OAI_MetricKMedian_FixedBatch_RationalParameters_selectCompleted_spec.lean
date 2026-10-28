-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:47:47.68606+00:00
-- url     : https://prove2.me/submissions/893a56ec-2a83-4511-b6c6-95f3a5e39097
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_completed_expectation
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_completion
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_count_tail

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem prob_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : 0 ≤ μ.prob E := by
  apply μ.expect_nonneg
  intro ω
  split_ifs <;> norm_num

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalCompletedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Completion.Rational
open Finset PhysicalPotential CopyState Analytic Preparation
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

omit [LinearOrder F] [Fintype F] in
theorem score_nonneg (d : Fin j → F → ℚ) (hd : ∀ c f, 0 ≤ d c f) (O : Finset F) :
    0 ≤ score d O := by
  apply sum_nonneg
  intro c _
  split_ifs with h
  · obtain ⟨f,_,he⟩ := mem_image.mp (min'_mem (O.image (d c)) (h.image _))
    rw [← he]
    exact hd c f
  · exact le_rfl

end MetricKMedian.Completion.Rational
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

theorem taperAt_le (t : ℕ) : (q.taperAt t:ℝ) ≤ 1/2 := by
  unfold taperAt
  split_ifs with ht
  · exact q.taper_le _
  · norm_num

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_Conditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

 theorem condition_support (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (ω : Ω) :
    0 < (condition μ P hP).weight ω ↔ P ω ∧ 0 < μ.weight ω := by
  change 0 < (if P ω then μ.weight ω/μ.prob P else 0) ↔ P ω ∧ 0 < μ.weight ω
  split_ifs with hp
  · simp only [hp, true_and]
    exact div_pos_iff_of_pos_right hP
  · simp [hp]

 theorem condition_expect_le (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    (condition μ P hP).expect f ≤ μ.expect f/μ.prob P := by
  have he : (condition μ P hP).expect f=
      μ.expect (fun ω => if P ω then f ω else 0)/μ.prob P := by
    unfold expect condition
    simp only [sum_div]
    apply sum_congr rfl
    intro ω _
    split_ifs <;> simp [div_mul_eq_mul_div]
  rw [he]
  apply div_le_div_of_nonneg_right _ hP.le
  apply μ.expect_mono
  intro ω
  split_ifs
  · exact le_rfl
  · exact hf ω

 theorem exists_support_le_expect (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ∃ ω, 0 < μ.weight ω ∧ f ω ≤ μ.expect f := by
  classical
  have hn : ∃ ω, 0 < μ.weight ω := by
    by_contra h
    push Not at h
    have hz : ∀ ω, μ.weight ω=0 := fun ω => le_antisymm (h ω) (μ.nonneg ω)
    have ht := μ.total
    simp only [hz, sum_const_zero] at ht
    norm_num at ht
  by_contra h
  push Not at h
  have hs : μ.expect (fun _ => μ.expect f) < μ.expect f := by
    apply sum_lt_sum
    · intro ω _
      by_cases hp : 0 < μ.weight ω
      · exact mul_le_mul_of_nonneg_left (h ω hp).le (μ.nonneg ω)
      · rw [le_antisymm (le_of_not_gt hp) (μ.nonneg ω), zero_mul, zero_mul]
    · obtain ⟨ω,hω⟩ := hn
      exact ⟨ω, mem_univ _, mul_lt_mul_of_pos_left (h ω hω) hω⟩
  rw [expect_const] at hs
  exact lt_irrefl _ hs

theorem select_success (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    ∃ ω, 0 < μ.weight ω ∧ P ω ∧ f ω ≤ μ.expect f/μ.prob P := by
  obtain ⟨ω,hω,hfω⟩ := (condition μ P hP).exists_support_le_expect f
  obtain ⟨hp,hw⟩ := (condition_support μ P hP ω).mp hω
  exact ⟨ω,hw,hp,hfω.trans (condition_expect_le μ P hP f hf)⟩

 theorem select_success_bound (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (f : Ω → ℝ) {p C : ℝ} (hp : 0 < p) (hP : p ≤ μ.prob P)
    (hf : ∀ ω, 0 ≤ f ω) (hE : μ.expect f ≤ C) :
    ∃ ω, 0 < μ.weight ω ∧ P ω ∧ f ω ≤ C/p := by
  obtain ⟨ω,hw,hgood,hcost⟩ := select_success μ P (hp.trans_le hP) f hf
  refine ⟨ω,hw,hgood,hcost.trans ?_⟩
  exact (div_le_div_of_nonneg_right hE (prob_nonneg μ P)).trans
    (div_le_div_of_nonneg_left ((μ.expect_nonneg hf).trans hE) hp hP)

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSelect
variable {α : Type}

theorem best_spec (P : α → Bool) (cost : α → ℚ) (L : List α) :
    (best P cost L=none ↔ ∀ a∈L,P a=false) ∧
    ∀ a, best P cost L=some a → a∈L ∧ P a=true ∧ ∀ b∈L,P b=true → cost a ≤ cost b := by
  induction L with
  | nil => simp [best]
  | cons a L ih =>
    by_cases ha : P a=true
    · cases hb : best P cost L with
      | none =>
        have hL := ih.1.mp hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro b h
          have he : a=b := Option.some.inj h
          subst b
          refine ⟨List.mem_cons_self,ha,?_⟩
          intro b hmem hP
          rcases List.mem_cons.mp hmem with he | he
          · subst b; exact le_rfl
          · have hf := hL b he
            rw [hP] at hf
            contradiction
      | some b =>
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro z hz
          by_cases hab : cost a ≤ cost b
          · simp only [ite_eq_left hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_self,ha,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_rfl
            · exact hab.trans (hmin z he hP)
          · simp only [ite_eq_right hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_of_lt (lt_of_not_ge hab)
            · exact hmin z he hP
    · have haf : P a=false := Bool.eq_false_iff.mpr ha
      simp only [best,haf,Bool.false_eq_true,ite_false]
      constructor
      · rw [ih.1]
        constructor
        · intro h b hb
          rcases List.mem_cons.mp hb with he | he
          · subst b; exact haf
          · exact h b he
        · intro h b hb
          exact h b (List.mem_cons_of_mem a hb)
      · intro b hb
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
        intro z hz hP
        rcases List.mem_cons.mp hz with he | he
        · subst z
          rw [haf] at hP
          contradiction
        · exact hmin z he hP

theorem choose_spec (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ)
    (a : α) (ha : choose μ P cost=some a) :
    P a=true ∧ ∀ i : Fin μ.length, P μ.states[i.val]=true → cost a ≤ cost μ.states[i.val] := by
  have hs := (best_spec P cost μ.states.toList).2 a ha
  refine ⟨hs.2.1,fun i hi => hs.2.2 _ ?_ hi⟩
  exact Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt)

theorem choose_bound (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ)
    {p C : ℝ} (hp : 0 < p)
    (hP : p ≤ μ.realIndex.prob (fun i => P μ.states[i.val]=true))
    (hcost : ∀ a,0 ≤ cost a)
    (hE : μ.expectation (fun a => (cost a:ℝ)) ≤ C) :
    ∃ a, choose μ P cost=some a ∧ P a=true ∧ (cost a:ℝ) ≤ C/p := by
  obtain ⟨i,_hi,hgood,hbound⟩ := μ.realIndex.select_success_bound
    (fun i => P μ.states[i.val]=true) (fun i => (cost μ.states[i.val]:ℝ)) hp hP
    (fun i => by exact_mod_cast hcost _) hE
  cases hb : choose μ P cost with
  | none =>
    have hz := (best_spec P cost μ.states.toList).1.mp hb _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt))
    rw [hgood] at hz
    contradiction
  | some a =>
    obtain ⟨ha,hmin⟩ := choose_spec μ P cost a hb
    refine ⟨a,rfl,ha,?_⟩
    exact (show (cost a:ℝ) ≤ (cost μ.states[i.val]:ℝ) by exact_mod_cast hmin i hgood).trans hbound

end MetricKMedian.SparseSelect
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistorySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

theorem selectCompleted_spec_oai (hτ : τ<1) (hj : 0<j)
    (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
    (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    ∃ O : Finset F, q.selectCompleted d₀ d R A B hB=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ mass (q.g:ℝ) A+(q.allowance:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,
        PhysicalPotential.cost (q.g:ℝ)
          (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)) := by
  let μ := q.tree d₀ A
  let good := fun a : Fin μ.length => mass (q.g:ℝ) μ.states[a.val].1.1 ≤
    mass (q.g:ℝ) A+(q.allowance:ℝ)
  have hfail : μ.realIndex.prob (fun a => ¬ good a) ≤ τ := by
    have hc := histories_count_tail d₀ location hd₀ q.g q.β q.probabilityQ q.φ q.taperAt
      q.probabilityQ_pos.le (by exact_mod_cast q.φpos.le) q.probabilityQ_le A q.T
      q.gpos q.gle (by exact_mod_cast q.probabilityQ_pos) q.φpos q.φle q.βpos q.unit
      (fun t _ => q.taperAt_pos t) (fun t _ => q.taperAt_le t) hA (by
        simpa only [probabilityQ,Rat.cast_mul,Rat.cast_ofNat] using q.count)
    have he : (q.allowance:ℝ)=(q.T:ℝ)*(4/((q.g:ℝ)*(q.β:ℝ))) := by
      simp only [allowance,Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
    have hf : μ.realIndex.prob (fun a => ¬ good a) ≤
      (q.T:ℝ)*(96*(q.Δ:ℝ)^2*(q.β:ℝ)/((q.probabilityQ:ℝ)*(q.φ:ℝ)^2*(q.g:ℝ))) := by
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      unfold FiniteLaw.prob SparseIntegerLaw.expectation
      apply congrArg μ.realIndex.expect
      funext a
      simp only [good,he,not_le]
      rfl
    exact hf.trans (by simpa only [probabilityQ,Rat.cast_mul,Rat.cast_ofNat] using q.failure)
  have hprob : 1-τ ≤ μ.realIndex.prob (fun a => q.completedGood d R A B hB μ.states[a.val]=true) := by
    have hc := μ.realIndex.prob_compl good
    have hp : 1-τ ≤ μ.realIndex.prob good := by linarith only [hc,hfail]
    apply hp.trans (μ.realIndex.prob_mono ?_)
    intro a ha
    have hs := histories_completion d₀ d location client hd₀ hd q.g q.β q.probabilityQ q.φ
      q.taperAt q.probabilityQ_pos.le (by exact_mod_cast q.φpos.le) q.probabilityQ_le A B R hB
      q.T (fun t => Real.exp (-(t:ℝ)*(q.h:ℝ))) q.gpos q.unit
      (fun t _ => q.taperAt_pos t) (fun t _ => q.taperAt_le t) hA hBA hR hm hdR a
    simp only [completedGood,decide_eq_true_eq]
    refine ⟨hs.2.1 hj,?_⟩
    have hh := hs.1.trans ha
    dsimp only [mass] at hh
    exact_mod_cast hh
  obtain ⟨z,hz,hgood,hcost⟩ := SparseSelect.choose_bound μ (q.completedGood d R A B hB)
    (fun z => score d (completed d R B hB q.g q.β z)) (sub_pos.mpr hτ) hprob
    (fun z => score_nonneg d (fun c f => by exact_mod_cast (hd c f ▸ dist_nonneg)) _)
    (q.completed_expectation d₀ d location client hd₀ hd A B R hB hA hBA hR hm hdR hatt)
  have hgood' := of_decide_eq_true hgood
  refine ⟨completed d R B hB q.g q.β z,?_,hgood'.1,?_,?_⟩
  · change Option.map _ (SparseSelect.choose μ _ _)=_
    rw [hz]
    rfl
  · dsimp only [mass]
    exact_mod_cast hgood'.2
  · exact hcost.trans_eq (by ring)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_oai := @OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_oai
