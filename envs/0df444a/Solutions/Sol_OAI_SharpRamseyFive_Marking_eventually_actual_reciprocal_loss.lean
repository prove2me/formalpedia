-- Prove2me | solution 1 for OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:28:05.01042+00:00
-- url     : https://prove2.me/submissions/f2d21ce6-da84-459a-ac84-9c968d7b1083

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_Marking_eventually_window_failure_small

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

theorem divergence_test (p q : Law α) (hpq : ∀ a,0 < p a → 0 < q a)
    (f : α → ℝ) :
    (∑ a,p a*f a)+1-(∑ a,q a*Real.exp (f a)) ≤ divergence p q := by
  have hpw (a : α) : p a*f a+p a-q a*Real.exp (f a) ≤
      p a*Real.log (p a/q a) := by
    have h := point_log_ratio (p a) (q a*Real.exp (f a)) (p.nonneg a)
      (mul_nonneg (q.nonneg a) (Real.exp_pos _).le)
      (fun hp => mul_pos (hpq a hp) (Real.exp_pos _))
    by_cases hz : p a=0
    · simp only [hz,zero_mul,zero_add] at h ⊢
      exact h
    · have hq : q a ≠ 0 := ne_of_gt (hpq a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz)))
      rw [Real.log_div hz (mul_ne_zero hq (Real.exp_ne_zero _)),
        Real.log_mul hq (Real.exp_ne_zero _),Real.log_exp] at h
      rw [Real.log_div hz hq]
      nlinarith
  have hs := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => hpw a)
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,p.sum_one,divergence] using hs

theorem event_comparison (p q : Law α) (hpq : ∀ a,0 < p a → 0 < q a)
    (E : Finset α) : (∑ a∈E,q a) ≤ 2*(divergence p q+∑ a∈E,p a) := by
  classical
  have ht := divergence_test p q hpq (fun a => if a∈E then -1 else 0)
  have he1 : (∑ a,p a*(if a∈E then -1 else 0)) = -(∑ a∈E,p a) := by
    simp only [mul_ite,mul_neg_one,mul_zero,←Finset.sum_filter,Finset.filter_univ_mem,Finset.sum_neg_distrib]
  have he2 : (∑ a,q a*Real.exp (if a∈E then -1 else 0)) =
      1-(1-Real.exp (-1))*(∑ a∈E,q a) := by
    have he (a : α) : q a*Real.exp (if a∈E then -1 else 0) =
        q a-(1-Real.exp (-1))*(if a∈E then q a else 0) := by
      split_ifs
      · ring
      · simp
    simp only [he,Finset.sum_sub_distrib,←Finset.mul_sum,q.sum_one,←Finset.sum_filter,
      Finset.filter_univ_mem]
  rw [he1,he2] at ht
  have hhalf : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg]
    have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) he
  have hqE : 0 ≤ ∑ a∈E,q a := Finset.sum_nonneg fun a _ => q.nonneg a
  nlinarith

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ProductHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A : Type} [Fintype B] [Fintype A]

lemma piLaw_update_balance (μ : B → Law A) (s : B → A) (b : B) (a : A) :
    piLaw μ s * μ b a = piLaw μ (Function.update s b a) * μ b (s b) := by
  classical
  have h₁ := Finset.mul_prod_erase Finset.univ (fun c => μ c (s c)) (Finset.mem_univ b)
  have h₂ := Finset.mul_prod_erase Finset.univ
    (fun c => μ c (Function.update s b a c)) (Finset.mem_univ b)
  have hprod : (∏ c ∈ Finset.univ.erase b, μ c (Function.update s b a c)) =
      ∏ c ∈ Finset.univ.erase b, μ c (s c) := by
    apply Finset.prod_congr rfl
    intro c hc
    rw [Function.update_of_ne (Finset.mem_erase.mp hc).1]
  simp only [Function.update_self, hprod] at h₂
  change (∏ c, μ c (s c)) * μ b a = (∏ c, μ c (Function.update s b a c)) * μ b (s b)
  rw [←h₁, ←h₂]
  ring

theorem independent_selected_identity (μ : B → Law A)
    (f : (B → A) → B → A → ℝ)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (∑ s, piLaw μ s * f s b (s b)) =
      ∑ s, piLaw μ s * (∑ a, μ b a * f s b a) := by
  classical
  have hh := Fintype.sum_equiv (RepresentativeAverage.swapAt (A := A) b)
    (fun z => piLaw μ z.1 * μ b z.2 * f z.1 b (z.1 b))
    (fun z => piLaw μ z.1 * μ b z.2 * f z.1 b z.2) (by
      intro z
      simp only [RepresentativeAverage.swapAt, Function.Involutive.toPerm, Equiv.coe_fn_mk]
      rw [hown]
      rw [←piLaw_update_balance]
      )
  simp only [Fintype.sum_prod_type] at hh
  calc
    _ = ∑ s, ∑ a, piLaw μ s * μ b a * f s b (s b) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [←Finset.sum_mul, ←Finset.mul_sum, (μ b).sum_one, mul_one]
    _ = ∑ s, ∑ a, piLaw μ s * μ b a * f s b a := hh
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RepresentativeSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical NNReal
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions
noncomputable local instance instDecidableEqSubtypeSumProdMemFinset_solutions_r4b79d9_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
lemma blockInformation_own_independent (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a i : A) :
    blockInformation p (Function.update s b a) b i=blockInformation p s b i := by
  apply Finset.sup_congr rfl
  intro c hc
  rw [Function.update_of_ne (Finset.mem_erase.mp hc).1]

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UnusedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions_1
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_1_r4b79d9_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
lemma uniformOn_expectation (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    (∑ a, uniformOn S hS a * f a) = (S.card : ℝ)⁻¹ * ∑ a ∈ S, f a := by
  simp only [uniformOn]
  calc
    _ = ∑ a, if a ∈ S then (S.card : ℝ)⁻¹ * f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by rw [←Finset.sum_filter, Finset.filter_univ_mem, Finset.mul_sum]

theorem unused_selected_identity (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (f : (B → A) → B → A → ℝ)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (S b).card * (∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * f s b (s b)) =
      ∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * (∑ a ∈ S b, f s b a) := by
  classical
  rw [independent_selected_identity _ f hown]
  simp_rw [uniformOn_expectation]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hc : ((S b).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hS b))
  field_simp

end

open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_nonneg (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ mean p f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (hf a)
lemma mean_mono (p : Law α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : mean p f ≤ mean p g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a)
lemma mean_add (p : Law α) (f g : α → ℝ) : mean p (fun a => f a + g a) = mean p f + mean p g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]
lemma mean_smul (p : Law α) (c : ℝ) (f : α → ℝ) : mean p (fun a => c * f a) = c * mean p f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]
lemma mean_finset_sum {ι : Type*} (p : Law α) (s : Finset ι) (f : ι → α → ℝ) :
    mean p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean p (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm
lemma mean_sum {ι : Type*} [Fintype ι] (p : Law α) (f : ι → α → ℝ) :
    mean p (fun a => ∑ i, f i a) = ∑ i, mean p (f i) := mean_finset_sum p Finset.univ f
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BlockReveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions_2
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_2_r4b79d9_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
lemma freshBlockLaw_eq (S : B → Finset A) (hS : ∀ b, (S b).Nonempty) :
    freshBlockLaw S = piLaw (fun b => uniformOn (S b) (hS b)) := by
  simp only [freshBlockLaw, dite_eq_left (hS _)]

omit [Fintype B] [Fintype A] [Nonempty A] in
lemma eraseBlock_card (S : B → Finset A) (s : B → A) (n : ℕ)
    (hS : ∀ b, n+1 ≤ (S b).card) : ∀ b, n ≤ (eraseBlock S s b).card := by
  intro b
  have := hS b
  simp only [eraseBlock, Finset.card_erase_eq_ite]
  split_ifs <;> omega

end
end

open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RevealDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions_3
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_3_r4b79d9_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
omit [Nonempty A] in
lemma mem_blockActive_left (S : B → Finset A) (b : B) (a : A) :
    Sum.inl (b,a) ∈ blockActive (T := T) S ↔ a ∈ S b := by simp [blockActive]
omit [Nonempty A] in
lemma mem_blockActive_right (S : B → Finset A) (t : T) :
    Sum.inr t ∈ blockActive S := by simp [blockActive]

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BlockSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

local instance instDecidableEqSumProd_solutions_4_r4b79d9_1 : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_4_r4b79d9_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
theorem fresh_selected_fraction (S : B → Finset A) (r : ℕ) (hr : 0 < r)
    (hS : ∀ b, r ≤ (S b).card) (f : (B → A) → B → A → ℝ)
    (hf : ∀ s b a, 0 ≤ f s b a)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) :
    r * mean (freshBlockLaw S) (fun s => ∑ b, f s b (s b)) ≤
      mean (freshBlockLaw S) (fun s => ∑ b, ∑ a ∈ S b, f s b a) := by
  have hn : ∀ b, (S b).Nonempty := fun b => Finset.card_pos.mp (hr.trans_le (hS b))
  rw [freshBlockLaw_eq S hn]
  simp only [mean_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have hc : (r : ℝ) ≤ (S b).card := by exact_mod_cast hS b
  have hnp : 0 ≤ mean (piLaw (fun b => uniformOn (S b) (hn b))) (fun s => f s b (s b)) :=
    mean_nonneg _ _ fun s => hf s b (s b)
  exact (mul_le_mul_of_nonneg_right hc hnp).trans_eq (unused_selected_identity S hn f hown b)

end

open scoped Classical BigOperators
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CollisionSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T : Type} [Fintype B] [Fintype A] [Fintype T] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.collisionSamplingDecEq
omit [Fintype A] [Fintype T] [Nonempty A] in
lemma otherCollision_own (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (s : B → A) (b : B) (a i : A) :
    otherCollision c (Function.update s b a) b i=otherCollision c s b i := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [Function.update_of_ne (Finset.mem_erase.mp hd).1]

end

open scoped Classical BigOperators

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.goodDeleteIndexDecEq
omit [Nonempty A] in
lemma indexBad_own (J d e : ℝ) (p : Law (((B×A)⊕T)→β))
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (s : B→A) (b : B) (a i : A) :
    indexBad J d e p c (Function.update s b a) (Sum.inl (b,i))=
      indexBad J d e p c s (Sum.inl (b,i)) := by
  simp only [indexBad,indexInformation,indexCollision,Sum.elim_inl,
    blockInformation_own_independent,otherCollision_own]

omit [Nonempty A] in
lemma blockActive_sum (S : B→Finset A) (f : ((B×A)⊕T)→ℝ) :
    (∑ i∈blockActive S,f i)=(∑ b,∑ a∈S b,f (Sum.inl (b,a)))+∑ t,f (Sum.inr t) := by
  calc
    _ = ∑ i,if i∈blockActive S then f i else 0 := by
      simp only [Finset.sum_ite_mem,Finset.univ_inter]
    _ = _ := by
      rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
      simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
        Finset.sum_ite_mem,Finset.univ_inter]

theorem selected_bad_fraction (J d e : ℝ)
    (p : Law (((B×A)⊕T)→β)) (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (S : B→Finset A) (r : ℕ) (hr : 0 < r) (hS : ∀ b,r≤(S b).card) :
    r*mean (freshBlockLaw S) (fun s=>∑ b,indexBad J d e p c s (Sum.inl (b,s b)))≤
      mean (freshBlockLaw S) (fun s=>∑ i∈blockActive S,indexBad J d e p c s i) := by
  have hh:=fresh_selected_fraction S r hr hS
    (fun s b a=>indexBad J d e p c s (Sum.inl (b,a)))
    (fun _ _ _=>badIndexIndicator_nonneg _ _ _ _) (indexBad_own J d e p c)
  apply hh.trans
  apply mean_mono
  intro s
  rw [blockActive_sum]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>badIndexIndicator_nonneg _ _ _ _)

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype α] in
lemma uniformWeight_nonneg (S : Finset α) (a : α) : 0 ≤ uniformWeight S a := by
  unfold uniformWeight;split_ifs <;> positivity

lemma relationMass_uniform (R : α→β→Prop) (S : Finset α) (T : Finset β) :
    relationMass R (uniformWeight S) (uniformWeight T)=
      (((S×ˢT).filter (fun z=>R z.1 z.2)).card:ℝ)/((S.card:ℝ)*T.card) := by
  have he : (S×ˢT).filter (fun z=>R z.1 z.2)=
      (Finset.univ.filter (fun z : α×β=>R z.1 z.2)).filter (fun z=>z.1∈S ∧ z.2∈T) := by
    ext z;simp [and_comm]
  rw [he]
  unfold relationMass
  have hterm (z : α×β) :
      uniformWeight S z.1*uniformWeight T z.2=
      if z.1∈S ∧ z.2∈T then 1/((S.card:ℝ)*T.card) else 0 := by
    by_cases hS : z.1∈S <;> by_cases hT : z.2∈T <;> simp [uniformWeight,hS,hT,mul_comm]
  simp_rw [hterm]
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  ring

end

open scoped BigOperators Classical
variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

lemma independent_support_relation (R : α→β→Prop) (μ : Law ι) (ν : Law κ)
    (X : ι→Finset α) (Y : κ→Finset β) :
    (∑i,∑j,μ i*ν j*relationMass R (uniformWeight (X i)) (uniformWeight (Y j)))=
      relationMass R (fun a=>∑i,μ i*uniformWeight (X i) a)
        (fun b=>∑j,ν j*uniformWeight (Y j) b) := by
  let E := Finset.univ.filter (fun z : α×β=>R z.1 z.2)
  change (∑i,∑j,μ i*ν j*(∑z∈E,uniformWeight (X i) z.1*uniformWeight (Y j) z.2))=
    ∑z∈E,(∑i,μ i*uniformWeight (X i) z.1)*(∑j,ν j*uniformWeight (Y j) z.2)
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑i,∑z∈E,∑j,μ i*ν j*(uniformWeight (X i) z.1*uniformWeight (Y j) z.2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑z∈E,∑i,∑j,μ i*ν j*(uniformWeight (X i) z.1*uniformWeight (Y j) z.2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma independent_support_domination (R : α→β→Prop) (p : Law α) (r : Law β)
    (μ : Law ι) (ν : Law κ) (X : ι→Finset α) (Y : κ→Finset β) (L : ℝ)
    (hL : 0 ≤ L) (hX : ∀a,(∑i,μ i*uniformWeight (X i) a) ≤ L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b) ≤ L*r b) :
    (∑i,∑j,μ i*ν j*relationMass R (uniformWeight (X i)) (uniformWeight (Y j))) ≤
      L^2*relationMass R p r := by
  rw [independent_support_relation]
  unfold relationMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hn : 0 ≤ ∑j,ν j*uniformWeight (Y j) z.2 := Finset.sum_nonneg
    (fun j _=>mul_nonneg (ν.nonneg j) (uniformWeight_nonneg _ _))
  have hh := mul_le_mul (hX z.1) (hY z.2) hn (mul_nonneg hL (p.nonneg z.1))
  nlinarith only [hh]

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Swap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mass_eq_second_mul_fiber (p : Law (α × β)) (a : α) (b : β) :
    p (a,b)=second p b*fiber (swap p) b a := by
  simpa only [first_swap,swap_mass] using mass_eq_first_mul_fiber (swap p) b a

theorem product_crossed_expectation (p : Law (α × β)) (q : Law (γ × δ))
    (F : α → β → γ → δ → ℝ) :
    (∑ z : (α × β) × (γ × δ),product p q z*F z.1.1 z.1.2 z.2.1 z.2.2)=
      ∑ a,∑ y,(first p a*second q y)*
        (∑ b,∑ c,(fiber p a b*fiber (swap q) y c)*F a b c y) := by
  simp only [Fintype.sum_prod_type]
  change (∑ a,∑ b,∑ c,∑ y,p (a,b)*q (c,y)*F a b c y)=_
  apply Finset.sum_congr rfl
  intro a _
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [mass_eq_first_mul_fiber p a b,mass_eq_second_mul_fiber q c y]
  ring

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Failure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {α β : Type*} [Fintype α] [Fintype β]

lemma mem_core (p : Law α) (v : α → V) (ρ : ℝ) (x : V) :
    x∈core (K := K) p v ρ ↔ ∀ f : Module.Dual K V,failure p v f≤ρ → f x=0 := by
  simp only [core,Submodule.mem_iInf,LinearMap.mem_ker]
  exact ⟨fun h f hf => h ⟨f,hf⟩,fun h f => h f.val f.property⟩

theorem core_failure [FiniteDimensional K V] (p : Law α) (v : α → V) (ρ : ℝ) (hρ : 0≤ρ) :
    (∑ a,if v a∉core (K := K) p v ρ then p a else 0)≤finrank K V*ρ := by
  let S : Set (Module.Dual K V) := {f | failure p v f≤ρ}
  obtain ⟨T,hTS,hcard,hspan,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn K S
  have hT : T.card≤finrank K V := by
    rw [hcard]
    exact (Submodule.finrank_le (Submodule.span K S)).trans_eq Subspace.dual_finrank_eq
  have hex (x : V) (hx : x∉core (K := K) p v ρ) : ∃ f∈T,f x≠0 := by
    by_contra hn
    have hz : ∀ f∈T,f x=0 := by simpa only [not_exists,not_and,not_not] using hn
    have hle : Submodule.span K (T:Set (Module.Dual K V))≤LinearMap.ker (Module.Dual.eval K V x) := by
      apply Submodule.span_le.mpr
      intro f hf
      exact hz f hf
    rw [hspan] at hle
    apply hx
    apply (mem_core (K := K) p v ρ x).mpr
    intro f hf
    exact hle (Submodule.subset_span (show f∈S from hf))
  have hpoint (a : α) :
      (if v a∉core (K := K) p v ρ then p a else 0)≤∑ f∈T,if f (v a)≠0 then p a else 0 := by
    by_cases h : v a∈core (K := K) p v ρ
    · simp only [h,not_true_eq_false,ite_false]
      exact Finset.sum_nonneg fun _ _ => by split_ifs; exact p.nonneg a; exact le_rfl
    · obtain ⟨f,hf,hfa⟩ := hex (v a) h
      simp only [h,not_false_eq_true,ite_true]
      have hh := Finset.single_le_sum (s := T) (f := fun f => if f (v a)≠0 then p a else 0)
        (fun _ _ => by split_ifs; exact p.nonneg a; exact le_rfl) hf
      simpa only [ite_eq_left hfa] using hh
  calc
    _ ≤ ∑ a,∑ f∈T,if f (v a)≠0 then p a else 0 := Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ f∈T,failure p v f := by rw [Finset.sum_comm]; rfl
    _ ≤ ∑ _f∈T,ρ := Finset.sum_le_sum fun f hf => hTS hf
    _ = (T.card:ℝ)*ρ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hρ

lemma capture_zero_one (p : Law α) (v : α → V) (ρ : ℝ) :
    0 ≤ capture (K := K) p v ρ ∧ capture (K := K) p v ρ≤1 := by
  constructor
  · apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact p.nonneg a
    · exact le_rfl
  · calc
      _ ≤ ∑ a,p a := Finset.sum_le_sum fun a _ => by
        split_ifs
        · exact le_rfl
        · exact p.nonneg a
      _ = 1 := p.sum_one

lemma capture_failure (p : Law α) (v : α → V) (ρ : ℝ) :
    capture (K := K) p v ρ+(∑ a,if v a∉core (K := K) p v ρ then p a else 0)=1 := by
  rw [capture,←Finset.sum_add_distrib]
  convert p.sum_one using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

 theorem capture_lower [FiniteDimensional K V] (p : Law α) (v : α → V) (ρ : ℝ) (hρ : 0≤ρ) :
    1-(finrank K V:ℝ)*ρ ≤ capture (K := K) p v ρ := by
  linarith [capture_failure (K := K) p v ρ,core_failure (K := K) p v ρ hρ]

theorem product_core_capture [FiniteDimensional K V]
    (p : Law α) (q : Law β) (v : α → Module.Dual K V) (w : β → V)
    (ρ : ℝ) (hρ : 0≤ρ) :
    1-2*(finrank K V:ℝ)*ρ≤
      ∑ a,∑ b,if v a∈core (K := K) p v ρ ∧ w b∈core (K := K) q w ρ
        then p a*q b else 0 := by
  have he : (∑ a,∑ b,if v a∈core (K := K) p v ρ ∧ w b∈core (K := K) q w ρ
        then p a*q b else 0)=capture (K := K) p v ρ*capture (K := K) q w ρ := by
    rw [capture,capture,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp_all
  rw [he]
  have hp := capture_lower (K := K) p v ρ hρ
  have hq := capture_lower (K := K) q w ρ hρ
  rw [Subspace.dual_finrank_eq] at hp
  have hp1 := (capture_zero_one (K := K) p v ρ).2
  have hq1 := (capture_zero_one (K := K) q w ρ).2
  have hprod := mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)
  nlinarith

lemma source_core_capture [FiniteDimensional K V] (hdim : finrank K V=5)
    (p : Law α) (q : Law β) (v : α → Module.Dual K V) (w : β → V) :
    (19/20:ℝ)≤∑ a,∑ b,
      if v a∈core (K := K) p v (1/200) ∧ w b∈core (K := K) q w (1/200)
      then p a*q b else 0 := by
  have h := product_core_capture p q v w (1/200) (by norm_num)
  norm_num [hdim] at h
  exact h
end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReverseMiss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

omit [FiniteDimensional K V] in
lemma reverseMiss_nonneg (p : Law β) (q : Law γ)
    (v : β → Module.Dual K V) (w : γ → V) : 0 ≤ reverseMiss p q v w := by
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact mul_nonneg (p.nonneg b) (q.nonneg c)
  · exact le_rfl

lemma conditional_charge (hdim : finrank K V=5) (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop) (a : α) (y : δ) :
    (19/20:ℝ)*(if good a y then 1 else 0) ≤
      38000*(if good a y then reverseMiss (fiber p a) (fiber (swap q) y) v w else 0)+
      ∑ b,∑ c,if capturedEvent p q v w good a b c y then
        fiber p a b*fiber (swap q) y c else 0 := by
  by_cases hg : good a y
  · simp only [hg,ite_true]
    by_cases hm : reverseMiss (fiber p a) (fiber (swap q) y) v w≤(1/40000:ℝ)
    · have hc := source_core_capture hdim (fiber p a) (fiber (swap q) y) v w
      have hz := reverseMiss_nonneg (fiber p a) (fiber (swap q) y) v w
      simp only [capturedEvent,hg,hm,true_and]
      nlinarith
    · have hh : (19/20:ℝ)≤38000*reverseMiss (fiber p a) (fiber (swap q) y) v w := by
        linarith
      simpa only [capturedEvent,hg,hm,true_and,false_and,ite_false,Finset.sum_const_zero,add_zero,mul_one] using hh
  · simp only [hg,ite_false,mul_zero,zero_add,capturedEvent,false_and,Finset.sum_const_zero,le_refl]
end SharpRamseyFive.LowConflict

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EventWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]
lemma eventWeight_comparison (p q : Law α) (h : ∀ a,0<p a → 0<q a) (E : α → Prop) :
    eventWeight q E≤2*(divergence p q+eventWeight p E) := by
  simpa only [Finset.sum_filter,eventWeight] using
    event_comparison p q h (Finset.univ.filter E)
lemma eventWeight_zero (p : Law α) (E : α → Prop) (h : ∀ a,E a → p a=0) :
    eventWeight p E=0 := by
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with he
  · exact h a he
  · rfl
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma crossed_eventWeight (p : Law (α × β)) (q : Law (γ × δ))
    (E : α → β → γ → δ → Prop) :
    eventWeight (product p q) (fun z => E z.1.1 z.1.2 z.2.1 z.2.2)=
      ∑ a,∑ y,(first p a*second q y)*
        (∑ b,∑ c,if E a b c y then fiber p a b*fiber (swap q) y c else 0) := by
  have h := product_crossed_expectation p q (fun a b c y => if E a b c y then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero,eventWeight] using h

lemma crossed_endpoint (p : Law (α × β)) (q : Law (γ × δ)) (good : α → δ → Prop) :
    eventWeight (product p q) (fun z => good z.1.1 z.2.2)=
      ∑ a,∑ y,(first p a*second q y)*(if good a y then 1 else 0) := by
  rw [crossed_eventWeight p q (fun a _ _ y => good a y)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : good a y
  · simp only [h,ite_true,←Finset.mul_sum,(fiber (swap q) y).sum_one,mul_one,
      (fiber p a).sum_one]
  · simp only [h,ite_false,Finset.sum_const_zero,mul_zero]

lemma crossed_conflict (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop) :
    eventWeight (product p q) (fun z => good z.1.1 z.2.2 ∧ v z.1.2 (w z.2.1)≠0)=
      ∑ a,∑ y,(first p a*second q y)*
        (if good a y then reverseMiss (fiber p a) (fiber (swap q) y) v w else 0) := by
  rw [crossed_eventWeight p q (fun a b c y => good a y ∧ v b (w c)≠0)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : good a y
  · simp only [h,true_and,ite_true,reverseMiss]
  · simp only [h,false_and,ite_false,Finset.sum_const_zero]

theorem integrated_charge [FiniteDimensional K V] (hdim : finrank K V=5)
    (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop) :
    (19/20:ℝ)*eventWeight (product p q) (fun z => good z.1.1 z.2.2)≤
      38000*eventWeight (product p q) (fun z => good z.1.1 z.2.2 ∧ v z.1.2 (w z.2.1)≠0)+
      eventWeight (product p q) (fun z => capturedEvent p q v w good z.1.1 z.1.2 z.2.1 z.2.2) := by
  rw [crossed_endpoint,crossed_conflict,crossed_eventWeight]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  have h := mul_le_mul_of_nonneg_left (conditional_charge hdim p q v w good a y)
    (mul_nonneg ((first p).nonneg a) ((second q).nonneg y))
  nlinarith

theorem low_conflict_bound [FiniteDimensional K V] (hdim : finrank K V=5)
    (p : Law ((α × β) × (γ × δ)))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop)
    (hconsistent : ∀ z,0<p z → good z.1.1 z.2.2 → v z.1.2 (w z.2.1)=0) :
    eventWeight (product (first p) (second p)) (fun z => good z.1.1 z.2.2)≤
      80004*(entropy (first p)+entropy (second p)-entropy p+
        eventWeight p (fun z => capturedEvent (first p) (second p) v w good
          z.1.1 z.1.2 z.2.1 z.2.2)) := by
  have hz : eventWeight p (fun z => good z.1.1 z.2.2 ∧ v z.1.2 (w z.2.1)≠0)=0 := by
    apply eventWeight_zero
    intro z hz
    apply le_antisymm _ (p.nonneg z)
    by_contra h
    exact hz.2 (hconsistent z (lt_of_not_ge h) hz.1)
  have hc := eventWeight_comparison p (product (first p) (second p)) (ac_product p)
    (fun z => good z.1.1 z.2.2 ∧ v z.1.2 (w z.2.1)≠0)
  rw [hz,add_zero,mutual_information] at hc
  have he := eventWeight_comparison p (product (first p) (second p)) (ac_product p)
    (fun z => capturedEvent (first p) (second p) v w good z.1.1 z.1.2 z.2.1 z.2.2)
  rw [mutual_information] at he
  have hi := entropy_subadditive p
  have hcap := eventWeight_nonneg p
    (fun z => capturedEvent (first p) (second p) v w good z.1.1 z.1.2 z.2.1 z.2.2)
  have h := integrated_charge hdim (first p) (second p) v w good
  linarith
end SharpRamseyFive.LowConflict

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.historyProducerIndexDecEq
local instance historyProducerSubtypeDecEq_r4b79d9_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
omit [Fintype β] [Nonempty A] in
lemma history_unused_card (S : B→Finset A) (r n : ℕ)
    (hS : ∀ b,r+n≤(S b).card) (h : BlockHistory B A T β n) :
    ∀ b,r≤(historyUnused S h b).card := by
  induction n generalizing S with
  | zero => simpa only [historyUnused,Nat.add_zero] using hS
  | succ n ih =>
    apply ih (eraseBlock S h.1) _ h.2.2
    apply eraseBlock_card S h.1 (r+n)
    intro b
    have := hS b
    omega

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.historySupportIndexDecEq
lemma preRound_positive (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) (z : (κ×BlockHistory B A T β n)×(B→A))
    (hz : 0<preRoundLaw μ p S n z) :
    0<μ z.1.1 ∧ 0<historyLaw (p z.1.1) (S z.1.1) n z.1.2 ∧
      0<freshBlockLaw (historyUnused (S z.1.1) z.1.2) z.2 := by
  change 0<(μ z.1.1*historyLaw (p z.1.1) (S z.1.1) n z.1.2)*
    freshBlockLaw (historyUnused (S z.1.1) z.1.2) z.2 at hz
  have h1:=(mul_pos_iff.mp hz).resolve_right (fun h=>
    ((freshBlockLaw (historyUnused (S z.1.1) z.1.2)).nonneg z.2).not_gt h.2)
  have h2:=(mul_pos_iff.mp h1.1).resolve_right (fun h=>(μ.nonneg _).not_gt h.1)
  exact ⟨h2.1,h2.2,h1.2⟩
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RelationMassCrossed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma relationMass_crossed (p : Law (α×β)) (q : Law (γ×δ)) (R : α→δ→Prop) :
    relationMass R (first p) (second q)=
      eventWeight (product p q) (fun z=>R z.1.1 z.2.2) := by
  rw [SharpRamseyFive.LowConflict.crossed_endpoint]
  unfold relationMass
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_Collisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
noncomputable section
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
lemma eventWeight_map (p : Law Ω) (f : Ω → Ξ) (P : Ξ → Prop) :
    eventWeight (map p f) P = eventWeight p (fun x => P (f x)) := by
  have h := sum_map p f (fun z => if P z then (1:ℝ) else 0)
  simpa only [eventWeight,mul_ite,mul_one,mul_zero,ite_mul,one_mul,zero_mul] using h
end
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
noncomputable section
variable {K V α β : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype α] [Fintype β] {n : ℕ}

theorem tuple_low_conflict (hdim : finrank K V=5)
    (p : Law (Fin n → α × β)) (v : α → V) (w : β → Module.Dual K V)
    (good : Fin n → Fin n → α → β → Prop)
    (hc : ∀ x,0<p x → ∀ i j,i<j → good i j (x i).1 (x j).2 →
      w (x i).2 (v (x j).1)=0) (i j : Fin n) (hij : i<j) :
    relationMass (good i j) (first (tupleMarginal p i)) (second (tupleMarginal p j)) ≤
      80004*(entropy (tupleMarginal p i)+entropy (tupleMarginal p j)-
        entropy (pair p (fun x => x i) (fun x => x j)) + tupleCollision p v w good i j) := by
  let pp := pair p (fun x => x i) (fun x => x j)
  have he : eventWeight pp (fun z => capturedEvent (first pp) (second pp) w v
      (good i j) z.1.1 z.1.2 z.2.1 z.2.2) = tupleCollision p v w good i j := by
    dsimp only [pp]
    rw [first_pair, second_pair, pair, eventWeight_map]
    unfold tupleCollision
    congr 1
    funext x
    simp only [tupleCapture,tupleMarginal,hij,true_and]
  have h := low_conflict_bound hdim pp w v (good i j) (by
    intro z hz hg
    obtain ⟨x,hx,he⟩ := map_positive p (fun x => (x i,x j)) z hz
    subst z
    exact hc x hx i j hij hg)
  rw [he] at h
  simpa only [pp,first_pair,second_pair,tupleMarginal,relationMass_crossed] using h

end
end SharpRamseyFive.LowConflict

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLowConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {n : ℕ}

omit [Finite K] in
lemma reciprocal_low_conflict (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (u : Fin n→ℝ) (s : ℝ)
    (hcons : ∀ x,0<p x→TupleConsistent x) (i j : Fin n) (hij : i<j) :
    relationMass (reciprocalGood p u s i j) (first (tupleMarginal p i)) (second (tupleMarginal p j))≤
      80004*(entropy (tupleMarginal p i)+entropy (tupleMarginal p j)-
        entropy (pair p (fun x=>x i) (fun x=>x j))+
        tupleCollision p Projectivization.rep Projectivization.rep (reciprocalGood p u s) i j) := by
  apply tuple_low_conflict hdim p Projectivization.rep Projectivization.rep (reciprocalGood p u s) ?_ i j hij
  intro x hx i j hij hg
  exact (incident_iff _ _).mp (hcons x hx i j hij hg.2.2)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedReciprocalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {I β : Type} [Fintype I] [Fintype β] {n : ℕ}

lemma orderedLaw_marginal (p : Law (I→β)) (e : I≃Fin n) (i : I) :
    map (orderedLaw p e) (fun x=>x (e i))=map p (fun x=>x i) := by
  rw [orderedLaw,map_comp]
  simp only [Function.comp_def,Equiv.symm_apply_apply]
lemma orderedLaw_pair (p : Law (I→β)) (e : I≃Fin n) (i j : I) :
    pair (orderedLaw p e) (fun x=>x (e i)) (fun x=>x (e j))=
      pair p (fun x=>x i) (fun x=>x j) := by
  rw [pair,orderedLaw,map_comp]
  simp only [Function.comp_def,Equiv.symm_apply_apply,pair]
lemma orderedLaw_positive (p : Law (I→β)) (e : I≃Fin n)
    (x : Fin n→β) (hx : 0<orderedLaw p e x) :
    ∃ y,0<p y ∧ ∀ i,x (e i)=y i := by
  obtain ⟨y,hy,rfl⟩:=map_positive p (fun x i=>x (e.symm i)) x hx
  exact ⟨y,hy,fun i=>by simp only [Equiv.symm_apply_apply]⟩
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

omit [Finite K] in
lemma ordered_reciprocal_low_conflict (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j) :
    relationMass (fun a b=>a∈goodFirstEndpoints (map p (fun x=>x i))
        (32*Real.exp (5*Real.log (Nat.card K)-u i)) ((Nat.card K:ℝ)^4) s ∧
      b∈goodFirstEndpoints (swap (map p (fun x=>x j))) (32*Real.exp (u j)) ((Nat.card K:ℝ)^4) s ∧ Incident a b)
      (first (map p (fun x=>x i))) (second (map p (fun x=>x j)))≤
      80004*(entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
        entropy (pair p (fun x=>x i) (fun x=>x j))+orderedCollision p e u s i j) := by
  have hc : ∀ x,0<orderedLaw p e x→TupleConsistent x := by
    intro x hx a b hab hf
    obtain ⟨y,hy,he⟩:=orderedLaw_positive p e x hx
    have h:=hcons y hy (e.symm a) (e.symm b) (by simpa using hab)
    simpa only [←he,Equiv.apply_symm_apply] using h (by simpa only [←he,Equiv.apply_symm_apply] using hf)
  have h:=reciprocal_low_conflict hdim (orderedLaw p e) (u∘e.symm) s hc (e i) (e j) hij
  unfold reciprocalGood tupleMarginal at h
  simp only [orderedLaw_marginal,orderedLaw_pair,Function.comp_apply,Equiv.symm_apply_apply] at h
  apply h.trans
  have hn:=tupleCollision_nonneg (orderedLaw p e) Projectivization.rep Projectivization.rep
    (reciprocalGood (orderedLaw p e) (u∘e.symm) s) (e j) (e i)
  dsimp only [orderedCollision]
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact add_le_add le_rfl (le_add_of_nonneg_right hn)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedWindowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section

theorem ordered_window_drop_sum {n : ℕ} (e l : Fin n→ℝ) (lo hi c : ℝ)
    (hc : 0 ≤ c) (hlohi : lo≤hi) (he : ∀i,e i≤hi) (hl : ∀i,lo≤l i)
    (hw : ∀i,l i≤e i+c) (ho : ∀i j,i<j→e j≤l i+c) :
    (∑i,max 0 (e i-l i))≤hi-lo+2*(n:ℝ)*c := by
  induction n generalizing lo hi with
  | zero => simpa using sub_nonneg.mpr hlohi
  | succ n ih =>
    have hh:=ih (fun i=>e i.succ) (fun i=>l i.succ) lo (l 0+c)
      (by linarith [hl 0])
      (fun i=>ho 0 i.succ (by simp)) (fun i=>hl i.succ)
      (fun i=>hw i.succ) (fun i j hij=>ho i.succ j.succ (by simpa using hij))
    have hhead : max 0 (e 0-l 0)≤hi-l 0+c :=
      max_le (by linarith [hw 0,he 0]) (by linarith [he 0])
    rw [Fin.sum_univ_succ]
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith

theorem good_large_window_count {w : ℕ} (G : Finset (Fin w))
    (e l : Fin w→ℝ) (lo hi c k : ℝ)
    (hc : 0 ≤ c) (hk : 0<k) (hlohi : lo≤hi)
    (he : ∀i∈G,e i≤hi) (hl : ∀i∈G,lo≤l i)
    (hw : ∀i∈G,l i≤e i+c)
    (ho : ∀i∈G,∀j∈G,i<j→e j≤l i+c) :
    ((G.filter fun i=>k<e i-l i).card:ℝ)≤(hi-lo+2*(G.card:ℝ)*c)/k := by
  let a:=G.orderEmbOfFin rfl
  have H:=ordered_window_drop_sum (fun i=>e (a i)) (fun i=>l (a i)) lo hi c hc hlohi
    (fun i=>he _ (Finset.orderEmbOfFin_mem ..)) (fun i=>hl _ (Finset.orderEmbOfFin_mem ..))
    (fun i=>hw _ (Finset.orderEmbOfFin_mem ..)) (fun i j hij=>ho _
      (Finset.orderEmbOfFin_mem ..) _ (Finset.orderEmbOfFin_mem ..) (a.strictMono hij))
  have hcard : (G.filter fun i=>k<e i-l i).card=
      (Finset.univ.filter fun i : Fin G.card=>k<e (a i)-l (a i)).card := by
    symm
    apply Finset.card_bij (fun i _=>a i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem ..,(Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ hij
      exact a.injective hij
    · intro v hv
      have hvG := (Finset.mem_filter.mp hv).1
      let i := (G.orderIsoOfFin rfl).symm ⟨v,hvG⟩
      have hi : a i=v := congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨v,hvG⟩)
      refine ⟨i,?_,hi⟩
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hi]
      exact (Finset.mem_filter.mp hv).2
  rw [hcard]
  apply (le_div_iff₀ hk).mpr
  calc
    _ = ∑i∈Finset.univ.filter (fun i : Fin G.card=>k<e (a i)-l (a i)),k := by simp
    _ ≤ ∑i∈Finset.univ.filter (fun i : Fin G.card=>k<e (a i)-l (a i)),max 0 (e (a i)-l (a i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact ((Finset.mem_filter.mp hi).2.le).trans (le_max_right _ _)
    _ ≤ ∑i,max 0 (e (a i)-l (a i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
    _ ≤ _ := H
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PreRoundDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.preRoundDeletionIndexDecEq
theorem preRound_selected_bad (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n r : ℕ) (hr : 0 < r)
    (hS : ∀ a,0<μ a→∀ b,r+n≤(S a b).card)
    (J d e : ℝ)
    (c : κ→BlockHistory B A T β n→((B×A)⊕T)→((B×A)⊕T)→ℝ) :
    r*mean (preRoundLaw μ p S n) (fun z=>∑ b,preRoundBad μ p S n J d e c z
      (Sum.inl (b,z.2 b)))≤
    mean (preRoundLaw μ p S n) (fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),
      preRoundBad μ p S n J d e c z i) := by
  simp only [preRoundLaw,mean_adaptive,preRoundBad]
  rw [←mean_smul]
  apply mean_mono_pos
  intro a ha
  rw [←mean_smul]
  exact mean_mono (historyLaw (p a) (S a) n) fun h=>
    selected_bad_fraction J d e _ _ _ r hr (history_unused_card (S a) r n (hS a ha) h)

end

open scoped Classical BigOperators
variable {Ω W T : Type*} [Fintype Ω] [Fintype W] [Fintype T]

lemma badIndexIndicator_zero_or_one (δ g d e : ℝ) :
    badIndexIndicator δ g d e=0 ∨ badIndexIndicator δ g d e=1 := by
  unfold badIndexIndicator
  split_ifs <;> simp

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReciprocalSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α : Type*} [Fintype α]
lemma mean_exists_le (p : Law α) (f : α→ℝ) :
    ∃ a,0<p a ∧ f a≤ mean p f := by
  obtain ⟨a,ha,hh⟩:=mean_exists_ge p (fun a=> -f a)
  refine ⟨a,ha,?_⟩
  have he : mean p (fun a=> -f a)= -mean p f := by
    simp only [mean,mul_neg,Finset.sum_neg_distrib]
  rw [he] at hh
  linarith
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem reciprocal_support_product (hdim : finrank K V=5)
    (μ : Law (Finset (ℙ K V))) (ν : Law (Finset (ℙ K (Dual K V))))
    (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hA : ∀ A,0<μ A→a≤(A.card:ℝ)) (hB : ∀ B,0<ν B→b≤(B.card:ℝ))
    (hs : (∑ A,∑ B,μ A*ν B*relationMass Incident (uniformWeight A) (uniformWeight B))≤
      1/(4*(Nat.card K:ℝ))) :
    a*b≤16*(Nat.card K:ℝ)^5 := by
  let p:=adaptiveLaw μ (fun _=>ν)
  let f:=fun z:Finset (ℙ K V)×Finset (ℙ K (Dual K V))=>
    relationMass Incident (uniformWeight z.1) (uniformWeight z.2)
  obtain ⟨⟨A,B⟩,hp,hh⟩:=mean_exists_le p f
  have hμ : 0<μ A := by
    change 0<μ A*ν B at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h=>(μ.nonneg A).not_gt h.1) |>.1
  have hν : 0<ν B := by
    change 0<μ A*ν B at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h=>(μ.nonneg A).not_gt h.1) |>.2
  have hm : mean p f≤1/(4*(Nat.card K:ℝ)) := by
    dsimp only [p]
    rw [mean_adaptive]
    simpa only [mean,Finset.mul_sum,mul_assoc,f] using hs
  have hAc : 0<(A.card:ℝ):=ha.trans_le (hA A hμ)
  have hBc : 0<(B.card:ℝ):=hb.trans_le (hB B hν)
  have hsparse : (incidences A B:ℝ)≤(A.card:ℝ)*B.card/(4*(Nat.card K:ℝ)) := by
    have ht:=hh.trans hm
    dsimp only [f] at ht
    rw [relationMass_uniform,div_le_iff₀ (mul_pos hAc hBc)] at ht
    simpa only [incidences,div_mul_eq_mul_div,one_mul] using ht
  exact (mul_le_mul (hA A hμ) (hB B hν) hb.le hAc.le).trans
    (sparse_rectangle_size (d:=4) hdim (by decide) A B hsparse)

theorem reciprocal_u_monotone (hdim : finrank K V=5)
    (μ : Law (Finset (ℙ K V))) (ν : Law (Finset (ℙ K (Dual K V))))
    (u v k : ℝ)
    (hA : ∀ A,0<μ A→Real.exp (5*Real.log (Nat.card K)-u-k)/2≤(A.card:ℝ))
    (hB : ∀ B,0<ν B→Real.exp (v-k)/2≤(B.card:ℝ))
    (hs : (∑ A,∑ B,μ A*ν B*relationMass Incident (uniformWeight A) (uniformWeight B))≤
      1/(4*(Nat.card K:ℝ))) : v≤u+2*k+Real.log 64 := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hh:=reciprocal_support_product hdim μ ν _ _ (by positivity) (by positivity) hA hB hs
  have he : Real.exp (5*Real.log (Nat.card K)-u-k)/2*(Real.exp (v-k)/2)=
      (Nat.card K:ℝ)^5*Real.exp (v-u-2*k)/4 := by
    rw [div_mul_div_comm,←Real.exp_add]
    have heck : (5*Real.log (Nat.card K)-u-k)+(v-k)=5*Real.log (Nat.card K)+(v-u-2*k) := by ring
    have hfive : Real.exp (5*Real.log (Nat.card K))=Real.exp (Real.log (Nat.card K))^5 := by
      simpa using Real.exp_nat_mul (Real.log (Nat.card K)) 5
    rw [heck,Real.exp_add,hfive,Real.exp_log hq]
    norm_num
  rw [he] at hh
  have hexp : Real.exp (v-u-2*k)≤64 := by nlinarith [pow_pos hq 5]
  have hhlog := (Real.log_le_log (Real.exp_pos _) hexp)
  rw [Real.log_exp] at hhlog
  linarith
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLevelProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
lemma relationMass_good_uniform (R : α→β→Prop) (A GA : Finset α) (B GB : Finset β)
    (hA : A⊆GA) (hB : B⊆GB) :
    relationMass (fun a b=>a∈GA ∧ b∈GB ∧ R a b) (uniformWeight A) (uniformWeight B)=
      relationMass R (uniformWeight A) (uniformWeight B) := by
  simp only [relationMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : z.1∈A
  · by_cases hb : z.2∈B
    · simp only [hA ha,hB hb,true_and]
    · simp only [uniformWeight,ite_eq_right hb,mul_zero,ite_self]
  · simp only [uniformWeight,ite_eq_right ha,zero_mul,ite_self]
end
end SharpRamseyFive.FiniteEntropy

end

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalLevels.first_size {p : Law (FlagPair K V)} {u s : ℝ}
    (L : ReciprocalLevels p u s) (A : Finset (ℙ K V)) (hA : 0<L.firstLaw A) :
    Real.exp (5*Real.log (Nat.card K)-u-s)/2≤(A.card:ℝ) := by
  have h:=(L.first_good A hA).2.2.1
  have he : Real.exp (5*Real.log (Nat.card K)-u)*Real.exp (-s)=
      Real.exp (5*Real.log (Nat.card K)-u-s) := by rw [←Real.exp_add]; congr 1
  nlinarith [Real.exp_pos (5*Real.log (Nat.card K)-u-s)]
omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalLevels.second_size {p : Law (FlagPair K V)} {u s : ℝ}
    (L : ReciprocalLevels p u s) (B : Finset (ℙ K (Dual K V))) (hB : 0<L.secondLaw B) :
    Real.exp (u-s)/2≤(B.card:ℝ) := by
  have h:=(L.second_good B hB).2.2.1
  have he : Real.exp u*Real.exp (-s)=Real.exp (u-s) := by rw [←Real.exp_add]; congr 1
  nlinarith [Real.exp_pos (u-s)]

omit [Finite K] [FiniteDimensional K V] in
theorem reciprocal_levels_cross (p q : Law (FlagPair K V)) (u v s ρ : ℝ)
    (L : ReciprocalLevels p u s) (R : ReciprocalLevels q v s)
    (hρ : relationMass (fun a b=>a∈goodFirstEndpoints p
        (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s ∧
      b∈goodFirstEndpoints (swap q) (32*Real.exp v) ((Nat.card K:ℝ)^4) s ∧ Incident a b)
      (first p) (second q)≤ρ) :
    (∑ A,∑ B,L.firstLaw A*R.secondLaw B*
      relationMass Incident (uniformWeight A) (uniformWeight B))≤(4*Real.exp 1)^2*ρ := by
  let GA:=goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s
  let GB:=goodFirstEndpoints (swap q) (32*Real.exp v) ((Nat.card K:ℝ)^4) s
  have h:=independent_support_domination (fun a b=>a∈GA ∧ b∈GB ∧ Incident a b)
    (first p) (second q) L.firstLaw R.secondLaw id id (4*Real.exp 1)
    (by positivity) L.first_dom R.second_dom
  have he : (∑ A,∑ B,L.firstLaw A*R.secondLaw B*
      relationMass (fun a b=>a∈GA ∧ b∈GB ∧ Incident a b) (uniformWeight A) (uniformWeight B))=
      ∑ A,∑ B,L.firstLaw A*R.secondLaw B*relationMass Incident (uniformWeight A) (uniformWeight B) := by
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    by_cases ha : 0<L.firstLaw A
    · by_cases hb : 0<R.secondLaw B
      · rw [relationMass_good_uniform Incident A GA B GB (L.first_good A ha).2.1 (R.second_good B hb).2.1]
      · rw [show R.secondLaw B=0 from le_antisymm (le_of_not_gt hb) (R.secondLaw.nonneg B)]
        ring
    · rw [show L.firstLaw A=0 from le_antisymm (le_of_not_gt ha) (L.firstLaw.nonneg A)]
      ring
  dsimp only [id_eq] at h
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))

variable [Fintype I] {n : ℕ}

omit [Finite K] in
theorem ordered_level_sparsity (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j)
    (L : ReciprocalLevels (map p (fun x=>x i)) (u i) s)
    (R : ReciprocalLevels (map p (fun x=>x j)) (u j) s) :
    (∑ A,∑ B,L.firstLaw A*R.secondLaw B*
      relationMass Incident (uniformWeight A) (uniformWeight B))≤
      ((4*Real.exp 1)^2*80004)*(entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
        entropy (pair p (fun x=>x i) (fun x=>x j))+orderedCollision p e u s i j) := by
  have h:=reciprocal_levels_cross _ _ _ _ s _ L R
    (ordered_reciprocal_low_conflict hdim p e u s hcons i j hij)
  simpa only [mul_assoc] using h

theorem ordered_good_u_monotone (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j)
    (L : ReciprocalLevels (map p (fun x=>x i)) (u i) s)
    (R : ReciprocalLevels (map p (fun x=>x j)) (u j) s)
    (hgood : entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
      entropy (pair p (fun x=>x i) (fun x=>x j))+orderedCollision p e u s i j≤ε)
    (hsmall : ((4*Real.exp 1)^2*80004)*ε≤1/(4*(Nat.card K:ℝ))) :
    u j≤u i+2*s+Real.log 64 := by
  apply reciprocal_u_monotone hdim L.firstLaw R.secondLaw (u i) (u j) s
    L.first_size R.second_size
  exact (ordered_level_sparsity hdim p e u s hcons i j hij L R).trans
    ((mul_le_mul_of_nonneg_left hgood (by positivity)).trans hsmall)
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowReciprocalScores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical
noncomputable section
variable {w r : ℕ}
lemma early_late_le (sel : (Fin w×Bool)→Fin r) (i j : Fin w) (hij : i≤j) :
    slotEmbedding (earlySlot sel i) < slotEmbedding (lateSlot sel j) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · exact ordered_windows _ _ h
  · simp only [earlySlot,lateSlot,Fin.lt_def,slotEmbedding_val,windowCoordinates]
    have hh:=(sel (i,false)).isLt
    omega
end
end SharpRamseyFive.Windows

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowLossAggregation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem retained_filter_loss (p : Law Ω) (eligible : I→Prop)
    (kept : Ω→I→Prop) (B : ℝ) (hB : 0≤B)
    (hkeep : ∀i,eligible i→mean p (fun z=>if kept z i then 0 else 1)≤B) :
    mean p (fun z=>(((Finset.univ.filter fun i=>eligible i ∧ kept z i)ᶜ).card:ℝ))≤
      ((Finset.univ.filter fun i=>¬eligible i).card:ℝ)+(Fintype.card I:ℝ)*B := by
  have hcard (z : Ω) :
      (((Finset.univ.filter fun i=>eligible i ∧ kept z i)ᶜ).card:ℝ)=
      ∑i,if eligible i ∧ kept z i then (0:ℝ) else 1 := by
    have heq : (Finset.univ.filter fun i=>eligible i ∧ kept z i)ᶜ =
        Finset.univ.filter (fun i=>¬(eligible i ∧ kept z i)) := by ext i; simp
    rw [heq,←Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  simp_rw [hcard]
  rw [mean_sum]
  calc
    _ ≤ ∑i,((if eligible i then 0 else 1)+B) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : eligible i
      · simpa only [hi,true_and,ite_true,zero_add] using hkeep i hi
      · simpa only [hi,false_and,ite_false,mean_const] using le_add_of_nonneg_right hB
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      congr 1
      simp only [←Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowReadiness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section
variable {κ β : Type} [Fintype κ] [Fintype β] {w r n rem : ℕ} [Nonempty (Fin r)]

local instance readinessBlockDE_r4b79d9_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.readinessIndexDE
omit [Nonempty (Fin r)] in
lemma window_not_ready_le (bad : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r)
    (hb : ∀ i,bad i=0 ∨ bad i=1) (v : Fin w) (t : Fin (2*r)) :
    (if windowReady bad sel v t then (0:ℝ) else 1)≤
      bad (Sum.inr (v,t))+∑ b : Bool,bad (Sum.inl ((v,b),sel (v,b))) := by
  simp only [Fintype.sum_bool]
  rcases hb (Sum.inr (v,t)) with h|h <;>
    rcases hb (Sum.inl ((v,true),sel (v,true))) with he|he <;>
      rcases hb (Sum.inl ((v,false),sel (v,false))) with hl|hl
  all_goals (simp only [windowReady,Bool.forall_bool,h,he,hl]; norm_num)

theorem preRound_ready_loss (μ : Law κ) (p : κ→Law (Slots w r→β))
    (S : κ→(Fin w×Bool)→Finset (Fin r)) (hrem : 0 < rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card) (J d e : ℝ)
    (c : κ→BlockHistory (Fin w×Bool) (Fin r) (Fin w×Fin (2*r)) β n→Slots w r→Slots w r→ℝ) :
    mean (preRoundLaw μ p S n) (fun z=>∑ v,∑ t,
      if windowReady (preRoundBad μ p S n J d e c z) z.2 v t then (0:ℝ) else 1)≤
      5*mean (preRoundLaw μ p S n) (fun z=>
        ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S n J d e c z i) := by
  let ν:=preRoundLaw μ p S n
  let bad:=preRoundBad μ p S n J d e c
  let all:=fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),bad z i
  let selected:=fun z=>∑ b,bad z (Sum.inl (b,z.2 b))
  have hnon (z : (κ×BlockHistory (Fin w×Bool) (Fin r) (Fin w×Fin (2*r)) β n)×
      ((Fin w×Bool)→Fin r)) (i : Slots w r) : 0≤bad z i := badIndexIndicator_nonneg ..
  have hmid : mean ν (fun z=>∑ v,∑ t,bad z (Sum.inr (v,t)))≤ mean ν all := by
    apply mean_mono
    intro z
    dsimp only [all]
    rw [blockActive_sum]
    conv_rhs => arg 2; rw [Fintype.sum_prod_type]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun b _=>Finset.sum_nonneg fun a _=>hnon z _)
  have hsel : (rem:ℝ)*mean ν selected≤ mean ν all := preRound_selected_bad μ p S n rem hrem hS J d e c
  have hsel0 : 0≤ mean ν selected := mean_nonneg _ _ (fun z=>Finset.sum_nonneg fun b _=>hnon z _)
  have hr' : (2*r:ℝ)≤4*rem := by exact_mod_cast (show 2*r≤4*rem by omega)
  have hweight := mul_le_mul_of_nonneg_right hr' hsel0
  have hpoint : mean ν (fun z=>∑ v,∑ t,
      if windowReady (bad z) z.2 v t then (0:ℝ) else 1)≤
      mean ν (fun z=>∑ v,∑ t,bad z (Sum.inr (v,t)))+(2*r:ℝ)*mean ν selected := by
    have hh:=mean_mono ν (fun z=>Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin w)))
      (fun v _=>Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin (2*r))))
        (fun t _=>window_not_ready_le (bad z) z.2 (fun i=>badIndexIndicator_zero_or_one ..) v t)))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,←Finset.mul_sum,mean_add,mean_smul] at hh
    simpa only [selected,Fintype.sum_prod_type] using hh
  change mean ν (fun z=>∑ v,∑ t,if windowReady (bad z) z.2 v t then (0:ℝ) else 1)≤5*mean ν all
  linarith
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowDeletionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {w r : ℕ}
attribute [local instance] OAI.SharpRamseyFive.Windows.deletionTargetDE
lemma mem_survivingWindowSet (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r)
    (drop : Fin w→ℝ) (k : ℝ) (v : Fin w) :
    v∈survivingWindowSet bad sel drop k ↔
      (∀b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0) ∧ drop v≤k := by
  simp only [survivingWindowSet,Finset.mem_filter,mem_goodWindowSet]

theorem ineligible_middle_count (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r)
    (drop : Fin w→ℝ) (k : ℝ) :
    ((Finset.univ.filter fun i : Fin w×Fin (2*r)=>
      ¬(i.1∈survivingWindowSet bad sel drop k ∧ bad (Sum.inr i)=0)).card:ℝ)≤
      (∑v,∑t,if windowReady bad sel v t then (0:ℝ) else 1)+
      (2*r:ℝ)*((goodWindowSet bad sel).filter fun v=>k<drop v).card := by
  rw [←Finset.sum_boole,Fintype.sum_prod_type]
  have hp (v : Fin w) (t : Fin (2*r)) :
      (if ¬(v∈survivingWindowSet bad sel drop k ∧ bad (Sum.inr (v,t))=0) then (1:ℝ) else 0)≤
      (if windowReady bad sel v t then 0 else 1)+
        (if v∈goodWindowSet bad sel ∧ k<drop v then 1 else 0) := by
    by_cases hg : ∀b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0
    · by_cases hd : drop v≤k <;> by_cases ht : bad (Sum.inr (v,t))=0 <;>
        simp [mem_survivingWindowSet,mem_goodWindowSet,windowReady,hg,hd,ht,
          true_and,and_true,and_false,not_true_eq_false,
          not_false_eq_true] <;> split_ifs <;> (first | (solve | norm_num) | linarith)
    · simp only [mem_survivingWindowSet,mem_goodWindowSet,windowReady,hg,
        false_and,and_false,not_false_eq_true,ite_true,ite_false,add_zero,le_refl]
  calc
    _ ≤ ∑v,∑t,((if windowReady bad sel v t then (0:ℝ) else 1)+
        (if v∈goodWindowSet bad sel ∧ k<drop v then (1:ℝ) else 0)) :=
      Finset.sum_le_sum (fun v _=>Finset.sum_le_sum (fun t _=>hp v t))
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,←Finset.mul_sum]
      congr 1
      congr 1
      rw [Finset.sum_boole]
      congr 2
      ext v
      simp

theorem reciprocal_loss_aggregate {Ω : Type*} [Fintype Ω] (p : Law Ω)
    (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r) (drop : Fin w→ℝ) (k B : ℝ)
    (kept : Ω→Fin w×Fin (2*r)→Prop) (hB : 0≤B)
    (hkeep : ∀v∈survivingWindowSet bad sel drop k,∀t,bad (Sum.inr (v,t))=0→
      mean p (fun z=>if kept z (v,t) then 0 else 1)≤B) :
    mean p (fun z=>((Finset.univ.filter (fun i : Fin w×Fin (2*r)=>
      i.1∈survivingWindowSet bad sel drop k ∧ bad (Sum.inr i)=0 ∧ kept z i))ᶜ.card:ℝ))≤
      (∑v,∑t,if windowReady bad sel v t then (0:ℝ) else 1)+
      (2*r:ℝ)*((goodWindowSet bad sel).filter fun v=>k<drop v).card+
      (w*(2*r):ℝ)*B := by
  let eligible := fun i : Fin w×Fin (2*r)=>i.1∈survivingWindowSet bad sel drop k ∧ bad (Sum.inr i)=0
  have hh:=retained_filter_loss p eligible kept B hB (fun i hi=>hkeep i.1 hi.1 i.2 hi.2)
  have hi:=ineligible_middle_count bad sel drop k
  have he : (Fintype.card (Fin w×Fin (2*r)):ℝ)=(w*(2*r):ℝ) := by simp
  rw [he] at hh
  simp only [eligible,and_assoc] at hh
  exact hh.trans (add_le_add hi le_rfl)
end
end SharpRamseyFive.Windows

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
attribute [local instance] OAI.SharpRamseyFive.Marking.allWindowProp
attribute [local instance] OAI.SharpRamseyFive.Marking.allWindowTDE
local instance allWindowBDE_r4b79d9_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.allWindowIDE
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V))) ]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
  {s : ℝ} (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

omit [Nonempty (Fin n)] in
theorem allWindow_loss (bad : Slots w n→ℝ) (drop : Fin w→ℝ) (k B : ℝ)
    (hE : E=survivingWindowSet bad sel drop k) (hB : 0≤B)
    (hh : ∀v∈E,∀t,bad (middleSlot v t)=0→
      allWindowFailure f r p u sel E W σ hσ hq hd c δ τ P hδ v t≤B) :
    mean (allWindowExperiment f r p u sel E W) (fun z=>
      ((allWindowPositions f r p u sel E W σ hσ hq hd c δ τ P hδ bad z.2.2 (z.1,z.2.1))ᶜ.card:ℝ))≤
      (∑v,∑t,if windowReady bad sel v t then (0:ℝ) else 1)+
      (2*n:ℝ)*((goodWindowSet bad sel).filter fun v=>k<drop v).card+(w*(2*n):ℝ)*B := by
  let kept := fun (z : (Slots w n→FlagPair K V)×
    (WindowLevelsData (K:=K) (V:=V) E.card×VariableTreeTape f r w)) (i : Fin w×Fin (2*n))=>
    z.1 (Sum.inr i)∈variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd c δ τ P hδ z.2.2 z.2.1) (survivorRank E i.1)
  have hk (v : Fin w) (hv : v∈survivingWindowSet bad sel drop k) (t : Fin (2*n))
      (ht : bad (Sum.inr (v,t))=0) :
      mean (allWindowExperiment f r p u sel E W) (fun z=>if kept z (v,t) then 0 else 1)≤B := by
    have hv' : v∈E := by rwa [hE]
    have hb:=hh v hv' t ht
    unfold allWindowFailure at hb
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext z
    dsimp only [kept,middleSlot]
    split_ifs <;> simp_all
  have h:=reciprocal_loss_aggregate (allWindowExperiment f r p u sel E W) bad sel drop k B kept hB (by
    intro v hv t ht
    convert hk v hv t ht using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext z
    by_cases hb : kept z (v,t) <;> simp only [hb,ite_true,ite_false])
  simpa only [allWindowPositions,hE,kept] using h
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_AllHistoryWindowLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance allHistBDE_r4b79d9_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.allHistIDE
attribute [local instance] OAI.SharpRamseyFive.Marking.allHistTDE
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ]
  {w n steps rem : ℕ} [Nonempty (Fin n)]

theorem allHistory_window_loss
    (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (S : κ→(Fin w×Bool)→Finset (Fin n)) (hrem : 0 < rem) (hn : n≤2*rem)
    (hS : ∀a,0<μ a→∀b,rem+steps≤(S a b).card)
    (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (J d ε s k B : ℝ) (hB : 0≤B)
    (c : κ→BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps→
      Slots w n→Slots w n→ℝ)
    (drop : WindowHistory κ K V w n steps→Fin w→ℝ)
    (E : WindowHistory κ K V w n steps→Finset (Fin w))
    (W : ∀z,∀hE : (E z).Nonempty,
      ReciprocalWindows (windowPosterior p z) (u z) z.2 (survivingOriginal (E z) hE) s)
    (hE : ∀z,0<preRoundLaw μ p S steps z→
      E z=survivingWindowSet (preRoundBad μ p S steps J d ε c z) z.2 (drop z) k)
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (c₀ δ τ P : ℝ) (hδ : 0<δ)
    (hh : ∀z,0<preRoundLaw μ p S steps z→∀v∈E z,∀t,
      preRoundBad μ p S steps J d ε c z (middleSlot v t)=0→
      allWindowFailure f r (windowPosterior p z) (u z) z.2 (E z) (W z)
        σ hσ hq hd c₀ δ τ P hδ v t≤B) :
    mean (preRoundLaw μ p S steps) (fun h=>
      mean (allWindowExperiment f r (windowPosterior p h) (u h) h.2 (E h) (W h)) (fun z=>
        ((allWindowPositions f r (windowPosterior p h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c₀ δ τ P hδ (preRoundBad μ p S steps J d ε c h)
          z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
      5*mean (preRoundLaw μ p S steps) (fun h=>
        ∑i∈blockActive (historyUnused (S h.1.1) h.1.2),preRoundBad μ p S steps J d ε c h i)+
      (2*n:ℝ)*mean (preRoundLaw μ p S steps) (fun h=>
        ((goodWindowSet (preRoundBad μ p S steps J d ε c h) h.2).filter fun v=>k<drop h v).card)+
      (w*(2*n):ℝ)*B := by
  have hb:=mean_mono_pos (preRoundLaw μ p S steps) (fun h hh'=>
    allWindow_loss f r (windowPosterior p h) (u h) h.2 (E h) (W h)
      σ hσ hq hd c₀ δ τ P hδ (preRoundBad μ p S steps J d ε c h) (drop h) k B
      (hE h hh') hB (hh h hh'))
  simp only [mean_add,mean_smul,mean_const] at hb
  have hrdy:=preRound_ready_loss μ p S hrem hn hS J d ε c
  exact hb.trans (add_le_add (add_le_add hrdy le_rfl) le_rfl)
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_GoodWindowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]

local instance goodVarBDE_r4b79d9_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.goodVarIDE
omit [Nonempty (Fin r)] in
theorem reciprocal_large_window_count (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ)
    (sel : (Fin w×Bool)→Fin r) (s d ε k lo hi : ℝ) (G : Finset (Fin w))
    (W : ReciprocalWindows p u sel (fun i : G=>i.val) s)
    (hcons : ∀x,0<p x→∀i j,slotEmbedding i < slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hgood : ∀i∈G,indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (earlySlot sel i)=0 ∧
      indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (lateSlot sel i)=0)
    (hu : ∀i,lo≤u i ∧ u i≤hi) (hlohi : lo≤hi) (hc : 0≤2*s+Real.log 64) (hk : 0<k)
    (hsmall : ((4*Real.exp 1)^2*80004)*ε≤1/(4*(Nat.card K:ℝ))) :
    ((G.filter fun i=>k<u (earlySlot sel i)-u (lateSlot sel i)).card:ℝ)≤
      (hi-lo+2*(G.card:ℝ)*(2*s+Real.log 64))/k := by
  apply good_large_window_count G (fun i=>u (earlySlot sel i)) (fun i=>u (lateSlot sel i))
    lo hi (2*s+Real.log 64) k hc hk hlohi (fun i _=>(hu _).2) (fun i _=>(hu _).1)
  · intro i hi
    rw [←add_assoc]
    apply ordered_good_u_monotone hdim p (slotEquiv w r) u s ε hcons
      (earlySlot sel i) (lateSlot sel i) (early_late_le sel i i le_rfl)
      (W.early ⟨i,hi⟩) (W.late ⟨i,hi⟩) _ hsmall
    exact (good_index_scores _ d ε p _ (fun _ _=>orderedCollision_nonneg ..)
      sel _ (hgood i hi).1).2 (i,true) (by simp [OtherBlock,earlySlot])
  · intro i hi j hj hij
    rw [←add_assoc]
    apply ordered_good_u_monotone hdim p (slotEquiv w r) u s ε hcons
      (lateSlot sel i) (earlySlot sel j) (ordered_windows _ _ hij)
      (W.late ⟨i,hi⟩) (W.early ⟨j,hj⟩) _ hsmall
    exact (good_index_scores _ d ε p _ (fun _ _=>orderedCollision_nonneg ..)
      sel _ (hgood i hi).2).2 (j,false) (by simp [OtherBlock,lateSlot])
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {w n : ℕ} [Nonempty (Fin n)]

attribute [local instance] OAI.SharpRamseyFive.Marking.wfcIDE
local instance wfcBDE_r4b79d9_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
variable (hdim : finrank K V=5) (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (J d ε s C : ℝ)
  (hcap : ReciprocalCaps p u C) (hs : 0 < s) (hJ : 4*Real.log (Nat.card K)≤J)
  (hmass : reciprocalBadMass s d C≤1/2)
  (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
    2*Real.exp 1*reciprocalBadMass s d C≤1/2)

include hdim hcap hs hJ hmass hsmall

omit [Nonempty (Fin n)] in
theorem goodWindows_drop_bound (k lo hi : ℝ)
    (hcons : ∀x,0<p x→∀i j,slotEmbedding i < slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hu : ∀i,lo≤u i ∧ u i≤hi) (hlohi : lo≤hi) (hc : 0≤2*s+Real.log 64) (hk : 0<k)
    (hε : ((4*Real.exp 1)^2*80004)*ε≤1/(4*(Nat.card K:ℝ))) :
    (((goodWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel) sel).filter
      fun v=>k<u (earlySlot sel v)-u (lateSlot sel v)).card:ℝ)≤
      (hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k := by
  let G:=goodWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel) sel
  let W:=Classical.choice (goodWindows_exist hdim p u sel J d ε s C hcap hs hJ hmass hsmall
    (fun i : G=>i.val) (fun i=>i.property))
  have h:=reciprocal_large_window_count hdim p u sel s d ε k lo hi G W hcons
    (fun _ h=>goodWindow_scores hJ h) hu hlohi hc hk hε
  apply h.trans
  gcongr
  exact_mod_cast (show G.card≤w from (Finset.card_le_univ G).trans_eq (Fintype.card_fin w))
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalDomainCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance histWinBDE_r4b79d9_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.histWinIDE
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ]
  {w n steps : ℕ} [Nonempty (Fin n)]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma actualWindowSet_eq (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (S : κ→(Fin w×Bool)→Finset (Fin n)) (u : κ→Slots w n→ℝ) (J d ε s k : ℝ)
    (z : WindowHistory κ K V w n steps) (hz : 0<preRoundLaw μ p S steps z) :
    actualWindowSet μ p u J d ε s k z=survivingWindowSet
      (preRoundBad μ p S steps J d ε (historyCollision p u s) z) z.2
      (fun v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) k := by
  rw [actualWindowSet,ite_eq_left (preRound_positive μ p S steps z hz).1]
  rfl

omit [Fintype (ℙ K (Dual K (Dual K V)))] in
theorem actualWindows_drop_mean (hdim : finrank K V=5) (μ : Law κ)
    (p : κ→Law (Slots w n→FlagPair K V)) (S : κ→(Fin w×Bool)→Finset (Fin n))
    (u : κ→Slots w n→ℝ) (J d ε s k C lo hi : ℝ)
    (hcap : ∀a,0<μ a→ReciprocalCaps (p a) (u a) C)
    (hs : 0 < s) (hJ : 4*Real.log (Nat.card K)≤J)
    (hmass : reciprocalBadMass s d C≤1/2)
    (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
      2*Real.exp 1*reciprocalBadMass s d C≤1/2)
    (hcons : ∀a,0<μ a→∀x,0<p a x→∀i j,slotEmbedding i < slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hu : ∀a,0<μ a→∀i,lo≤u a i ∧ u a i≤hi) (hlohi : lo≤hi)
    (hc : 0≤2*s+Real.log 64) (hk : 0<k)
    (hε : ((4*Real.exp 1)^2*80004)*ε≤1/(4*(Nat.card K:ℝ))) :
    mean (preRoundLaw μ p S steps) (fun z=>
      (((goodWindowSet (preRoundBad μ p S steps J d ε (historyCollision p u s) z) z.2).filter
        fun v=>k<u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)).card:ℝ))≤
      (hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k := by
  rw [←mean_const (preRoundLaw μ p S steps) ((hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k)]
  apply mean_mono_pos
  intro z hz
  have ha:=(preRound_positive μ p S steps z hz).1
  exact goodWindows_drop_bound hdim (windowPosterior p z) (u z.1.1) z.2 J d ε s C
    ((hcap z.1.1 ha).history _ _ _ steps z.1.2) hs hJ hmass hsmall k lo hi
    (fun x hx=>hcons z.1.1 ha x (history_support (p z.1.1) steps z.1.2 x hx))
    (hu z.1.1 ha) hlohi hc hk hε
end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowSmallFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section

attribute [local irreducible] actualWindows actualWindowSet

local instance arlBDE_r4b79d9_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.arlTDE
attribute [local instance] OAI.SharpRamseyFive.Marking.arlIDE
theorem eventually_actual_reciprocal_loss_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J lo hi B : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V κ : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n H steps rem : ℕ) [Nonempty (Fin n)]
      (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
      (elig : κ→(Fin w×Bool)→Finset (Fin n)) (u : κ→Slots w n→ℝ)
      (hcap : ∀a,0<μ a→ReciprocalCaps (p a) (u a) C₀)
      (hcons : ∀a,0<μ a→∀x,0<p a x→∀i j,slotEmbedding i < slotEmbedding j→
        Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
      (hu : ∀a,0<μ a→∀i,lo≤u a i ∧ u a i≤hi)
      (hlohi : lo≤hi) (hk : 0<k) (hJ : 4*Real.log (Nat.card K)≤J)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
      (hcard : Nat.card K=q₀) (hrange : Range η σ D R) (hL : (L₀:ℝ)=L η σ D)
      (hb0 : 0≤k+2*(D*σ^(2*beta η))+Real.log 4)
      (hbhi : k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η))
      (hw : w<2^H) (hH : (H:ℝ)≤σ^beta η)
      (hmass : reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2)
      (hsmall : 2*(D*σ^beta η+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/(D*σ^(2*beta η))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2)
      (_hε : ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*(Nat.card K:ℝ)))
      (_hrem : 0 < rem) (_hn : n≤2*rem)
      (_hS : ∀a,0<μ a→∀b,rem+steps≤(elig a b).card)
      (_hbad : mean (preRoundLaw μ p elig steps) (fun z=>
        ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
          preRoundBad μ p elig steps J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
            (historyCollision p u (D*σ^(2*beta η))) z j)≤B),
      let s:=D*σ^(2*beta η)
      let d:=D*σ^beta η
      let ε:=σ^(-2000*beta η)/Real.exp σ
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let E:=actualWindowSet μ p u J d ε s k
      ∃ W : ∀z,∀hE : (E z).Nonempty,
        ReciprocalWindows (windowPosterior p z) (u z.1.1) z.2 (survivingOriginal (E z) hE) s,
      mean (preRoundLaw μ p elig steps) (fun h=>
        mean (allWindowExperiment f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)
            σ hσ hq hd.le (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num)
            (preRoundBad μ p elig steps J d ε (historyCollision p u s) h)
            z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
        5*B+(2*n:ℝ)*((hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k)+(w*(2*n):ℝ)*ρ := by
  filter_upwards [eventually_window_failure_small hη hη' Cb C₀ ρ hCb hC hρ] with σ hfail
  intro D k J lo hi B R L₀ q₀ K V κ _ _ _ _ _ _ _ _ _ _ hd hq3 w n H steps rem _
    μ p elig u hcap hcons hu hlohi hk hJ hσ hq hcard hrange hL hb0 hbhi hw hH hmass hsmall hε hrem hn hS hbad
  dsimp only
  have hD : 0<D := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hσ) _).trans_le hrange.dlo
  have hs : 0<D*σ^(2*beta η) := by positivity
  let E:=actualWindowSet μ p u J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) (D*σ^(2*beta η)) k (steps:=steps)
  let W:=actualWindows hd μ p u J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
    (D*σ^(2*beta η)) k C₀ hcap hs hJ hmass hsmall (steps:=steps)
  refine ⟨W,?_⟩
  have hdrop:=actualWindows_drop_mean (steps:=steps) hd μ p elig u J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
    (D*σ^(2*beta η)) k C₀ lo hi hcap hs hJ hmass hsmall hcons hu hlohi
    (by positivity) hk hε
  apply (allHistory_window_loss _ _ μ p elig hrem hn hS (fun z=>u z.1.1)
    J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) (D*σ^(2*beta η)) k ρ hρ.le
    (historyCollision p u (D*σ^(2*beta η)))
    (fun z v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) E W
    (actualWindowSet_eq μ p elig u _ _ _ _ _)
    σ hσ hq hd.le (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) ?_).trans
  · exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbad (by norm_num))
      (mul_le_mul_of_nonneg_left hdrop (by positivity))) le_rfl
  · intro z hz v hv t ht
    have ha:=(preRound_positive μ p elig steps z hz).1
    have hcp:=(hcap z.1.1 ha).history _ _ _ steps z.1.2
    have he : E z=survivingWindowSet
        (preRoundBad μ p elig steps J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
          (historyCollision p u (D*σ^(2*beta η))) z) z.2
        (fun v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) k :=
      actualWindowSet_eq μ p elig u _ _ _ _ _ z hz
    apply hfail D k J R L₀ q₀ K V hd hq3 w n H (windowPosterior p z) (u z.1.1) z.2
      (E z) (W z) (fun x hx=>hcons z.1.1 ha x (history_support (p z.1.1) steps z.1.2 x hx))
      hcp.incident hcp.first hcp.second hcp.flag hJ ?_ ?_ hσ hq hcard hrange hL hb0 hbhi hw hH v hv t ht
    · intro v hv
      rw [he] at hv
      exact (mem_goodWindowSet _ _ _).mp (Finset.mem_filter.mp hv).1 false
    · intro v hv
      rw [he] at hv
      exact (Finset.mem_filter.mp hv).2
end

end SharpRamseyFive.Marking

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss_oai := @OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss_oai
