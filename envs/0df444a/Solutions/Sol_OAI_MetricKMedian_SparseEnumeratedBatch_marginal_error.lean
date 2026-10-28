-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:51:28.700378+00:00
-- url     : https://prove2.me/submissions/e933b367-b394-4dd9-a61f-afe5049f0d3b

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K062

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

theorem prob_congr (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω ↔ F ω) : μ.prob E = μ.prob F := by
  exact le_antisymm (μ.prob_mono fun ω => (hEF ω).mp) (μ.prob_mono fun ω => (hEF ω).mpr)

theorem prob_exists_le_sum (μ : FiniteLaw Ω) {I : Type*} (s : Finset I)
    (E : I → Ω → Prop) [∀ i, DecidablePred (E i)] :
    μ.prob (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  unfold prob
  rw [← expect_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i ∈ s, E i ω
  · obtain ⟨i, hi, hei⟩ := h
    simp only [ite_eq_left (show ∃ i ∈ s, E i ω from ⟨i, hi, hei⟩)]
    have hsingle := Finset.single_le_sum (f := fun j => if E j ω then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) hi
    simpa only [ite_eq_left hei] using hsingle
  · simp only [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRealTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem product_indicator (q : Fin n → Bool) (S : Finset (Fin n)) :
    (∏ i∈S, flag q i)=(if ∀ i∈S, q i=true then (1:ℚ) else 0) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi,ih]
    simp only [mem_insert,forall_eq_or_imp]
    cases hq : q i <;> simp [flag,hq]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw

theorem prob_false {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    μ.prob (fun _ => False)=0 := by
  simp only [prob, ite_false, expect_const]

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseFiltered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω E : Type} [Fintype Ω] [Fintype E] [DecidableEq E]

theorem prob_le_add_of_imp (μ : FiniteLaw Ω) (A B C : Ω → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    (h : ∀ ω, A ω → B ω ∨ C ω) : μ.prob A ≤ μ.prob B+μ.prob C := by
  rw [prob,prob,prob,← expect_add]
  apply μ.expect_mono
  intro ω
  by_cases ha : A ω
  · rcases h ω ha with hb | hc
    · simp only [ite_eq_left ha,ite_eq_left hb]
      split_ifs <;> norm_num
    · simp only [ite_eq_left ha,ite_eq_left hc]
      split_ifs <;> norm_num
  · simp only [ite_eq_right ha]
    split_ifs <;> norm_num

theorem filtered_two_moment (μ : FiniteLaw (E → Bool)) (C : E → Finset E)
    (p : ℝ) (hm : ∀ e, μ.prob (fun q => q e=true)=p)
    (hp : ∀ e f, e≠f → μ.prob (fun q => q e=true ∧ q f=true) ≤ p^2)
    (e : E) (hself : e∉C e) :
    |μ.prob (fun q => e∈selected C q)-p| ≤ (C e).card*p^2 := by
  classical
  have hu : μ.prob (fun q => e∈selected C q) ≤ p := by
    rw [← hm e]
    exact μ.prob_mono (fun q h => (mem_filter.mp h).2.1)
  have hd := μ.prob_le_add_of_imp (fun q => q e=true)
    (fun q => e∈selected C q) (fun q => ∃ f∈C e, q e=true ∧ q f=true) (by
      intro q he
      by_cases hh : ∀ f∈C e, q f=false
      · exact Or.inl (mem_filter.mpr ⟨mem_univ _,he,hh⟩)
      · push Not at hh
        obtain ⟨f,hf,hff⟩ := hh
        have hft : q f=true := by cases hq : q f <;> simp_all
        exact Or.inr ⟨f,hf,he,hft⟩)
  rw [hm e] at hd
  have hb := μ.prob_exists_le_sum (C e) (fun f q => q e=true ∧ q f=true)
  have hs : (∑ f∈C e, μ.prob (fun q => q e=true ∧ q f=true)) ≤ (C e).card*p^2 := by
    calc
      _ ≤ ∑ _f∈C e, p^2 := sum_le_sum (fun f hf => hp e f (fun he => hself (he ▸ hf)))
      _ = _ := by simp
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith only [hd,hb,hs]

end MetricKMedian.FiniteLaw
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem cylinder (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    (run (d := d) p hp n).real.prob (fun q => ∀ i∈S, q i=true)=((∏ i∈S,p i:ℚ):ℝ) := by
  calc
    _ = (run (d := d) p hp n).real.expect (fun q => ((∏ i∈S,flag q i:ℚ):ℝ)) := by
      unfold FiniteLaw.prob
      congr 1
      funext q
      rw [product_indicator]
      split_ifs <;> norm_num
    _ = _ := by rw [SparseIntegerLaw.real_expect,subset_moment p hp S hS]

theorem real_marginal (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hd : 1 ≤ d) (e : Fin n) :
    (run (d := d) p hp n).real.prob (fun q => q e=true)=(p e:ℝ) := by
  have he := cylinder (d := d) p hp {e} (by simpa using hd)
  simpa only [mem_singleton,forall_eq,prod_singleton] using he

theorem real_pair (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hd : 2 ≤ d) (e f : Fin n) (hef : e≠f) :
    (run (d := d) p hp n).real.prob (fun q => q e=true ∧ q f=true)=(p e:ℝ)*(p f:ℝ) := by
  have he := cylinder (d := d) p hp {e,f} (by simpa [hef] using hd)
  simpa only [mem_insert,mem_singleton,forall_eq_or_imp,forall_eq,prod_pair hef,Rat.cast_mul] using he

theorem filtered_error (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hd : 2 ≤ d)
    (C : Fin n → Finset (Fin n)) (e : Fin n) (hself : e∉C e) :
    |(run (d := d) (fun _ => p) (fun _ => hp) n).real.prob
      (fun q => e∈FiniteLaw.selected C q)-(p:ℝ)| ≤ (C e).card*(p:ℝ)^2 := by
  apply FiniteLaw.filtered_two_moment _ C (p:ℝ)
    (fun i => real_marginal _ _ (by omega) i) ?_ e hself
  intro i j hij
  rw [real_pair _ _ hd i j hij,pow_two]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRealExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_def (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.expectation f=∑ i : Fin μ.length, (μ.law.rational.weight i:ℝ)*f μ.states[i.val] := rfl

theorem expectation_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℝ) :
    (μ.bindIndexed κ).expectation f=
      ∑ a, (μ.law.rational.weight a:ℝ)*(κ a).expectation f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  calc
    _ = ∑ z, (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val] := by
      unfold expectation realIndex
      change (∑ i, (((ρ.integer.reindex finSigmaFinEquiv).rational.weight i):ℝ)*
        f ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
          (κ z.1).states[z.2.val]))[i.val])) = _
      simp only [Vector.getElem_ofFn]
      change (∑ i, (ρ.integer.rational.weight (finSigmaFinEquiv.symm i):ℝ)*
        f (κ (finSigmaFinEquiv.symm i).1).states[(finSigmaFinEquiv.symm i).2.val]) = _
      simp only [RationalLaw.integer_weight]
      exact (finSigmaFinEquiv (n := fun a => (κ a).length)).symm.sum_comp
        (fun z : Sigma (fun a : Fin μ.length => Fin (κ a).length) =>
          (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val])
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [ρ,RationalLaw.sigma,Rat.cast_mul,mul_assoc,← mul_sum,expectation_def]

theorem expectation_map (μ : SparseIntegerLaw α) (g : α → β) (f : β → ℝ) :
    (μ.map g).expectation f=μ.expectation (fun a => f (g a)) := by
  simp only [expectation_def,map,Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_mix (μ ν : SparseIntegerLaw α) (f : α → ℝ) :
    (mix μ ν).expectation f=(1/2)*μ.expectation f+(1/2)*ν.expectation f := by
  rw [mix,expectation_bindIndexed]
  change (∑ a : Fin 2, ((1/2:ℚ):ℝ)*(if a.val=0 then μ else ν).expectation f)=_
  norm_num [Fin.sum_univ_two]

theorem real_expect_all [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.real.expect f=μ.expectation f := by
  rw [real,FiniteLaw.expect_map]
  rfl

theorem prob_mix [Fintype α] [DecidableEq α] (μ ν : SparseIntegerLaw α)
    (P : α → Prop) [DecidablePred P] :
    (mix μ ν).real.prob P=(1/2)*μ.real.prob P+(1/2)*ν.real.prob P := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_mix]

theorem prob_map [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : SparseIntegerLaw α) (f : α → β) (P : β → Prop) [DecidablePred P] :
    (μ.map f).real.prob P=μ.real.prob (fun a => P (f a)) := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePhysicalBatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

theorem balanced_eq (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) :
    balanced Z C ω=PhysicalBatchLaw.balanced Z C ω := by
  ext e
  simp only [balanced,PhysicalBatchLaw.balanced,FiniteLaw.selected,mem_inter,mem_filter]

theorem unbalanced_eq (Z : Finset (Fin n)) (ω : Fin n → Bool) :
    unbalanced Z ω=PhysicalBatchLaw.unbalanced Z ω := rfl

theorem prob_eq (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (R : Finset (Fin n) → Prop) [DecidablePred R] :
    (law Z C p q hp hq).real.prob R=
      (1/2)*(SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
      (1/2)*(SparseBernoulli.run (d := 4) q hq n).real.prob
        (fun ω => R (PhysicalBatchLaw.unbalanced Z ω)) := by
  rw [law,SparseIntegerLaw.prob_mix,SparseIntegerLaw.prob_map,SparseIntegerLaw.prob_map]
  apply congrArg₂ (fun x y : ℝ => (1/2)*x+(1/2)*y)
  · apply FiniteLaw.prob_congr
    intro ω
    rw [balanced_eq]
  · apply FiniteLaw.prob_congr
    intro ω
    rw [unbalanced_eq]

theorem marginal (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (e : Fin n) :
    (law Z C p q hp hq).real.prob (fun A => e∈A)=
      if e∈Z then (1/2)*(SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => e∈FiniteLaw.selected C ω) else (1/2)*(q e:ℝ) := by
  rw [prob_eq]
  by_cases he : e∈Z
  · simp only [PhysicalBatchLaw.balanced,PhysicalBatchLaw.unbalanced,mem_inter,mem_filter,
      mem_univ,he,and_true,not_true_eq_false,and_false,ite_true,FiniteLaw.prob_false,mul_zero,add_zero]
  · simp only [PhysicalBatchLaw.balanced,PhysicalBatchLaw.unbalanced,mem_inter,mem_filter,
      mem_univ,true_and,he,and_false,not_false_eq_true,and_true,ite_false,FiniteLaw.prob_false,
      SparseBernoulli.real_marginal q hq (by norm_num : 1 ≤ 4),mul_zero,zero_add]

theorem marginal_error (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hqq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e∉C e) (e : Fin n) :
    |(law Z C p q hp hq).real.prob (fun A => e∈A)-(p:ℝ)/2| ≤
      (N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2 := by
  rw [marginal]
  have hp0 : (0:ℝ) ≤ p := by exact_mod_cast hp.1
  have hnonneg := mul_nonneg hφ hp0
  have hN0 : 0 ≤ (N:ℝ)*(p:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (p:ℝ))
  by_cases he : e∈Z
  · rw [ite_eq_left he]
    have herror := SparseBernoulli.filtered_error p hp (by norm_num : 2 ≤ 4) C e (hself e)
    have hN : (C e).card*(p:ℝ)^2 ≤ (N:ℝ)*(p:ℝ)^2 :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hC e)) (sq_nonneg (p:ℝ))
    have heq : (1/2)*(SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => e∈FiniteLaw.selected C ω)-(p:ℝ)/2 =
      ((SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => e∈FiniteLaw.selected C ω)-(p:ℝ))/2 := by ring
    rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [herror,hN,hnonneg]
  · rw [ite_eq_right he, abs_of_nonneg (by linarith only [(hqq e).1])]
    nlinarith only [(hqq e).2,hN0]

end MetricKMedian.SparsePhysicalBatch

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedBatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem marginal_error_oai (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hqq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e∉C e) (e : E) :
    |(law enum Z C p q hp hq).real.prob (fun A => e∈A)-(p:ℝ)/2| ≤
      (N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2 := by
  rw [law,SparseIntegerLaw.prob_map]
  have hs : ∀ a : Fin n, a ∉ (C (enum a)).map enum.symm.toEmbedding := by
    intro a ha
    simp only [mem_map_equiv,Equiv.symm_symm] at ha
    exact hself _ ha
  have hh := SparsePhysicalBatch.marginal_error (Z.map enum.symm.toEmbedding)
    (fun a => (C (enum a)).map enum.symm.toEmbedding) p (fun a => q (enum a)) hp
    (fun a => hq (enum a)) hφ (fun a => hqq (enum a))
    (fun a => by simpa only [card_map] using hC (enum a)) hs (enum.symm e)
  simpa only [mem_map_equiv,Equiv.apply_symm_apply] using hh

end MetricKMedian.SparseEnumeratedBatch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error_oai := @OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error_oai
