-- Prove2me | solution 1 for OAI.SharpRamseyFive.SelectedTuple.eventually_high_three_prepared_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:46:50.996773+00:00
-- url     : https://prove2.me/submissions/35d3e845-0bb5-4ce6-a3cc-190242f3cd56

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_Marking_exists_high_three_round

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_HighRoundNumbers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section
lemma high_integer_ranges {σ q D η c : ℝ} (hη : 0<η) (hσ : 1≤σ) (hq : 2≤q)
    (hc : 0 < c) (hD : σ^beta η≤D)
    (hscale : D*σ^(3000*beta η) ≤ c*σ/4) (n : ℕ)
    (hlen : c*q*σ^(1+η)≤n) :
    let T:=⌊q*D*σ^(3000*beta η)⌋₊
    let rem:=n-T
    let h:=⌈q*σ^beta η⌉₊
    0<n ∧ 0<T ∧ 0 < rem ∧ n≤2*rem ∧ rem+T≤n ∧
      q*D*σ^(3000*beta η)/2≤T ∧ q*σ^(1+η/2)/(2/c) ≤ rem ∧
      q*σ^beta η≤h ∧ (h:ℝ)≤2*q*σ^beta η := by
  dsimp only
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqpos : 0<q := by linarith
  have hb:=beta_pos hη
  have hD1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hp : 1≤σ^(3000*beta η) := Real.one_le_rpow hσ (by positivity)
  let x:=q*D*σ^(3000*beta η)
  have hx : 2≤x := by
    calc
      2 ≤ q := hq
      _ = q*1*1 := by ring
      _ ≤ _ := by dsimp [x];gcongr
  have hσhi : σ≤σ^(1+η) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hT : (⌊x⌋₊:ℝ)≤x := Nat.floor_le (by linarith)
  have hTx := Nat.lt_floor_add_one x
  have hThalf : x/2≤(⌊x⌋₊:ℝ) := by linarith
  have hxn : x≤(n:ℝ)/4 := by
    calc
      _ = q*(D*σ^(3000*beta η)) := by dsimp [x];ring
      _ ≤ q*(c*σ/4) := mul_le_mul_of_nonneg_left hscale hqpos.le
      _ ≤ q*(c*σ^(1+η)/4) := by gcongr
      _ ≤ _ := by nlinarith [hlen]
  have hTn : 2*⌊x⌋₊≤n := by
    have hh : (2:ℝ)*⌊x⌋₊≤n := by linarith
    exact_mod_cast hh
  have hn0 : 0<n := by
    have : 0<(n:ℝ) := (by positivity : 0 < c*q*σ^(1+η)).trans_le hlen
    exact_mod_cast this
  have hTpos : 0<⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hTle : ⌊x⌋₊≤n := by omega
  have hrem : (n:ℝ)/2≤((n-⌊x⌋₊:ℕ):ℝ) := by
    rw [Nat.cast_sub hTle]
    have hh : (2:ℝ)*⌊x⌋₊≤n := by exact_mod_cast hTn
    linarith
  have hlrem : q*σ^(1+η/2)/(2/c)≤((n-⌊x⌋₊:ℕ):ℝ) := by
    apply le_trans _ hrem
    have hpow : σ^(1+η/2)≤σ^(1+η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
    calc
      _ = c*q*σ^(1+η/2)/2 := by field_simp
      _ ≤ c*q*σ^(1+η)/2 := by gcongr
      _ ≤ _ := by linarith
  have hsm : 1≤q*σ^beta η := by
    have := Real.one_le_rpow hσ hb.le
    nlinarith
  have hceil := Nat.le_ceil (q*σ^beta η)
  have hceilhi := Nat.ceil_lt_add_one (by linarith : 0≤q*σ^beta η)
  dsimp only [x] at hTn hTpos hTle hThalf hlrem
  exact ⟨hn0,hTpos,by omega,by omega,by omega,hThalf,hlrem,hceil,by linarith⟩
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EventMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma eventMass_le_one (p : Law α) (E : Finset α) : eventMass p E≤1 := by
  rw [←p.sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => p.nonneg a)

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
noncomputable local instance instDecidableEqSubtypeSumProdMemFinset_solutions_r3f8671_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_1_r3f8671_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_2_r3f8671_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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

section
open scoped Classical BigOperators
variable {ι β : Type*} [Fintype ι] [Fintype β]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEq_solutions
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSubtypeMemFinset_solutions_2
lemma InDomains.fiber {p : Law (ι → β)} {D : ι → Finset β} (h : InDomains p D)
    (E : Finset ι) (a : E → β) : InDomains (fiber (reveal p E) a) D := by
  intro x hx i
  exact h x (fiber_reveal_support p E a x hx) i

end

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions_3
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_3_r3f8671_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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

local instance instDecidableEqSumProd_solutions_4_r3f8671_1 : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_4_r3f8671_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DeletionNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma deletion_budget_monomial {σ q D k budget rounds rem C Cb Cc Cn b η : ℝ}
    (hσ : 1≤σ) (hq : 0<q) (hD : 0<D) (hk : 0≤k)
    (hCb : 0≤Cb) (hCc : 0≤Cc) (hCn : 0<Cn)
    (hb : budget≤Cb*k*D*σ^(-b))
    (hr : q*D*σ^(3000*b)/2 ≤ rounds)
    (hn : q*σ^(1+η/2)/Cn ≤ rem) (hC : C≤Cc*σ*k) :
    budget/(D*σ^b)+(2*budget/rounds+C/rem)/(σ^(-2000*b)/q)≤
      k*(Cb*σ^(-2*b)+4*Cb*σ^(-1001*b)+Cc*Cn*σ^(2000*b-η/2)) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hround : 0<q*D*σ^(3000*b)/2 := by positivity
  have hrem : 0<q*σ^(1+η/2)/Cn := by positivity
  have hd : 0<D*σ^b := by positivity
  have he : 0<σ^(-2000*b)/q := by positivity
  have h1 : budget/(D*σ^b)≤Cb*k*σ^(-2*b) := by
    calc
      _ ≤ (Cb*k*D*σ^(-b))/(D*σ^b) := div_le_div_of_nonneg_right hb hd.le
      _ = Cb*k*(σ^(-b)/σ^b) := by field_simp
      _ = _ := by rw [←Real.rpow_sub hs];congr 2;ring
  have h2 : (2*budget/rounds)/(σ^(-2000*b)/q)≤4*Cb*k*σ^(-1001*b) := by
    have ht : 2*budget/rounds≤(2*(Cb*k*D*σ^(-b)))/(q*D*σ^(3000*b)/2) := by
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (hround.trans_le hr).le).trans
      exact div_le_div_of_nonneg_left (by positivity) hround hr
    calc
      _ ≤ ((2*(Cb*k*D*σ^(-b)))/(q*D*σ^(3000*b)/2))/(σ^(-2000*b)/q) :=
        div_le_div_of_nonneg_right ht he.le
      _ =4*Cb*k*(σ^(-b)/(σ^(3000*b)*σ^(-2000*b))) := by field_simp;ring
      _ = _ := by rw [←Real.rpow_add hs,←Real.rpow_sub hs];congr 2;ring
  have h3 : (C/rem)/(σ^(-2000*b)/q)≤Cc*Cn*k*σ^(2000*b-η/2) := by
    have ht : C/rem≤(Cc*σ*k)/(q*σ^(1+η/2)/Cn) := by
      apply (div_le_div_of_nonneg_right hC (hrem.trans_le hn).le).trans
      exact div_le_div_of_nonneg_left (by positivity) hrem hn
    calc
      _ ≤ ((Cc*σ*k)/(q*σ^(1+η/2)/Cn))/(σ^(-2000*b)/q) :=
        div_le_div_of_nonneg_right ht he.le
      _ = Cc*Cn*k*(σ/(σ^(1+η/2)*σ^(-2000*b))) := by field_simp
      _ = _ := by
        rw [←Real.rpow_add hs]
        nth_rw 1 [←Real.rpow_one σ]
        rw [←Real.rpow_sub hs]
        congr 2
        ring
  rw [add_div]
  calc
    _ ≤ Cb*k*σ^(-2*b)+ (4*Cb*k*σ^(-1001*b)+Cc*Cn*k*σ^(2000*b-η/2)) :=
      add_le_add h1 (add_le_add h2 h3)
    _ = _ := by ring

theorem eventually_deletion_budget {η : ℝ} (hη : 0<η) (Cb Cc Cn ε : ℝ)
    (hCb : 0≤Cb) (hCc : 0≤Cc) (hCn : 0<Cn) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop,∀q D k budget rounds rem C : ℝ,
      0<q→0<D→0≤k→budget≤Cb*k*D*σ^(-beta η)→
      q*D*σ^(3000*beta η)/2 ≤ rounds→q*σ^(1+η/2)/Cn ≤ rem→C≤Cc*σ*k→
      budget/(D*σ^beta η)+(2*budget/rounds+C/rem)/(σ^(-2000*beta η)/q)≤ε*k := by
  have hb:=beta_pos hη
  have h1 : 0<2*beta η := by positivity
  have h2 : 0<1001*beta η := by positivity
  have h3 : 0<η/2-2000*beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>Cb*σ^(-2*beta η)+4*Cb*σ^(-1001*beta η)+
      Cc*Cn*σ^(2000*beta η-η/2)) atTop (𝓝 0) := by
    convert ((tendsto_rpow_neg_atTop h1).const_mul Cb).add
      ((tendsto_rpow_neg_atTop h2).const_mul (4*Cb)) |>.add
      ((tendsto_rpow_neg_atTop h3).const_mul (Cc*Cn)) using 1 <;> ring_nf
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hε] with σ hσ hsmall
  intro q D k budget rounds rem C hq hD hk hb hr hn hC
  exact (deletion_budget_monomial hσ hq hD hk hCb hCc hCn hb hr hn hC).trans
    (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hsmall.le hk)
end
end SharpRamseyFive.ParameterHierarchy

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

open scoped BigOperators Classical
variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

lemma relationMass_by_target (R : α→β→Prop) (f : α→ℝ) (g : β→ℝ) :
    relationMass R f g=∑b,g b*(∑a∈Finset.univ.filter (fun a=>R a b),f a) := by
  unfold relationMass
  rw [Finset.sum_filter,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GoodPairScores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local irreducible] indexInformation indexCollision indexBad coordinateInformation

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.goodPairIndexDecEq
omit [Nonempty A] in
lemma good_index_scores_reverse (J d e : ℝ) (p : Law (((B×A)⊕T)→β))
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0 ≤ c i j) (hcs : ∀ i j,c i j=c j i)
    (s : B→A) (i : ((B×A)⊕T)) (hg : indexBad J d e p c s i=0)
    (b : B) (hi : OtherBlock i b) :
      entropy (map p (fun x=>x (Sum.inl (b,s b))))+entropy (map p (fun x=>x i))-
        entropy (pair p (fun x=>x (Sum.inl (b,s b))) (fun x=>x i))+c (Sum.inl (b,s b)) i≤e := by
  rw [pair_entropy_swap p (fun x=>x (Sum.inl (b,s b))) (fun x=>x i),hcs (Sum.inl (b,s b)) i,add_comm
    (entropy (map p (fun x=>x (Sum.inl (b,s b)))))]
  exact (good_index_scores J d e p c hc s i hg).2 b hi

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
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section

lemma representative_early {w r : ℕ} (v : Fin w) (a : Fin r) (t : Fin (2*r)) :
    slotEmbedding (Sum.inl ((v,false),a)) < slotEmbedding (Sum.inr (v,t)) := by
  simp only [Fin.lt_def,slotEmbedding_val,windowCoordinates]
  omega

end
end SharpRamseyFive.Windows

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

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighEndpointCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma first_entropy_of_partner_cap (p : Law (α×β)) (M : ℝ) (_hM : 0<M)
    (hpartner : ∀ a,0<first p a →
      (((support p).filter fun z=>z.1=a).card:ℝ)≤M) :
    entropy p ≤ entropy (first p)+Real.log M := by
  have hh := entropy_partition_bound p Prod.fst (fun _=>Real.log M) (by
    intro a ha
    rw [map_fst] at ha
    have hc:=hpartner a ha
    have hp : 0<(((support p).filter fun z=>z.1=a).card:ℝ) := by
      obtain ⟨z,hz,hf⟩ := map_positive p Prod.fst a (by simpa [map_fst] using ha)
      exact_mod_cast Finset.card_pos.mpr ⟨z,Finset.mem_filter.mpr ⟨(mem_support p z).mpr hz,hf⟩⟩
    exact Real.log_le_log hp hc)
  simpa only [map_fst,←Finset.sum_mul,(first p).sum_one,one_mul] using hh

theorem high_first_upper_tail (p : Law (α×β)) (N S M K : ℝ)
    (hN : 0<N) (hM : 0<M) (hK : 0<K)
    (hcap : ((support (first p)).card:ℝ)≤S)
    (hpartner : ∀ a,0<first p a →
      (((support p).filter fun z=>z.1=a).card:ℝ)≤M) :
    eventMass (first p) (Finset.univ.filter fun a=>N*first p a>Real.exp K) ≤
      (Real.log N+Real.log M-entropy p+S/N)/K := by
  have hh := first_entropy_of_partner_cap p M hM hpartner
  have ht := scaled_heavy_atom_mass (first p) N S K hN hK hcap
  change eventMass (first p) _ ≤ _ at ht
  apply ht.trans
  apply div_le_div_of_nonneg_right _ hK.le
  linarith

theorem high_bad_first_mass (p : Law (α×β)) (NA N U S M T K : ℝ)
    (hNA : 0<NA) (hN : 0<N) (hU : 0<U) (hM : 0<M) (hK : 0<K)
    (hA : ((support (first p)).card:ℝ)≤NA)
    (hS : ((support (first p)).card:ℝ)≤S)
    (hflag : ((support p).card:ℝ)≤T)
    (hpartner : ∀ a,0<first p a →
      (((support p).filter fun z=>z.1=a).card:ℝ)≤M) :
    eventMass (first p) (highGoodFirst p NA N U K)ᶜ ≤
      Real.exp (-K)+50*(Real.log N-entropy p+T/N)/K+
      (Real.log U+Real.log M-entropy p+S/U)/K := by
  let E := Finset.univ.filter fun a=>U*first p a>Real.exp K
  have hsub : (highGoodFirst p NA N U K)ᶜ ⊆ (goodFirstEndpoints p NA N K)ᶜ ∪ E := by
    intro a ha
    simp only [Finset.mem_compl,highGoodFirst,Finset.mem_filter] at ha
    by_cases hg : a∈goodFirstEndpoints p NA N K
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge (fun hu=>ha ⟨hg,hu⟩)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_compl.mpr hg)
  have hs : eventMass (first p) (highGoodFirst p NA N U K)ᶜ ≤
      eventMass (first p) (goodFirstEndpoints p NA N K)ᶜ+eventMass (first p) E := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _=>(first p).nonneg a)).trans
    have hh := Finset.sum_union_inter (s₁:=(goodFirstEndpoints p NA N K)ᶜ) (s₂:=E) (f:=fun a=>first p a)
    have hn : 0≤∑ a∈(goodFirstEndpoints p NA N K)ᶜ∩E,first p a :=
      Finset.sum_nonneg fun a _=>(first p).nonneg a
    change ∑ a∈(goodFirstEndpoints p NA N K)ᶜ∪E,first p a ≤
      (∑ a∈(goodFirstEndpoints p NA N K)ᶜ,first p a)+∑ a∈E,first p a
    linarith
  exact hs.trans (add_le_add (bad_first_endpoint_mass p NA N T K hNA hN hK hA hflag)
    (high_first_upper_tail p U S M K hU hM hK hS hpartner))

lemma support_first_subset_image (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) : support (first p)⊆D.image Prod.fst := by
  intro a ha
  obtain ⟨z,hz,hf⟩:=map_positive p Prod.fst a (by simpa only [map_fst] using (mem_support _ _).mp ha)
  exact Finset.mem_image.mpr ⟨z,hD ((mem_support _ _).mpr hz),hf⟩

lemma support_fiber_card (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) (a : α) :
    ((support p).filter fun z=>z.1=a).card≤(Finset.univ.filter fun b=>(a,b)∈D).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro z hz
    obtain ⟨hz,he⟩:=Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [←he,Prod.mk.eta] using hD hz⟩
  · intro z hz y hy he
    exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hy).2.symm) he

theorem high_endpoint_bad (p : Law (α×β)) (q s d C0 : ℝ) (r : ℕ)
    (hq : 0<q) (hs : 0 < s) (hr : r≤4)
    (hcap : ((support (first p)).card:ℝ)≤32*q^r)
    (hflag : ((support p).card:ℝ)≤C0*q^4)
    (hpartner : ∀ a,0<first p a→
      (((support p).filter fun z=>z.1=a).card:ℝ)≤2*q^(4-r))
    (hent : 4*Real.log q-entropy p≤d) :
    eventMass (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0 := by
  have hq0 : q≠0:=ne_of_gt hq
  have hpow : (r:ℝ)+(4-r:ℕ)=4 := by exact_mod_cast Nat.add_sub_of_le hr
  have hl : Real.log (q^r)+Real.log (2*q^(4-r))=4*Real.log q+Real.log 2 := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hq0),Real.log_pow,Real.log_pow]
    calc
      _ = ((r:ℝ)+(4-r:ℕ))*Real.log q+Real.log 2 := by ring
      _ = _ := by rw [hpow]
  have h:=high_bad_first_mass p (32*q^r) (q^4) (q^r) (32*q^r) (2*q^(4-r)) (C0*q^4) s
    (by positivity) (by positivity) (by positivity) (by positivity) hs hcap hcap hflag hpartner
  rw [Real.log_pow,hl,mul_div_cancel_right₀ _ (pow_ne_zero 4 hq0),
    mul_div_cancel_right₀ _ (pow_ne_zero r hq0)] at h
  apply h.trans
  unfold highBadMass
  exact add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hent (le_refl C0)) (by norm_num)) hs.le))
    (div_le_div_of_nonneg_right (by linarith) hs.le)

theorem high_endpoint_bad_of_domain (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) (q s d C0 : ℝ) (r : ℕ)
    (hq : 0<q) (hs : 0 < s) (hr : r≤4)
    (hcap : ((D.image Prod.fst).card:ℝ)≤32*q^r)
    (hflag : (D.card:ℝ)≤C0*q^4)
    (hpartner : ∀ a,((Finset.univ.filter fun b=>(a,b)∈D).card:ℝ)≤2*q^(4-r))
    (hent : 4*Real.log q-entropy p≤d) :
    eventMass (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0 := by
  apply high_endpoint_bad p q s d C0 r hq hs hr
  · exact (Nat.cast_le.mpr (Finset.card_le_card (support_first_subset_image p D hD))).trans hcap
  · exact (Nat.cast_le.mpr (Finset.card_le_card hD)).trans hflag
  · intro a _
    exact (Nat.cast_le.mpr (support_fiber_card p D hD a)).trans (hpartner a)
  · exact hent

lemma support_swap_first_fiber (p : Law (α×β)) (b : β) :
    ((support (swap p)).filter fun z=>z.1=b).card=
      ((support p).filter fun z=>z.2=b).card := by
  apply Finset.card_bij (fun z _=>z.swap)
  · intro z hz
    obtain ⟨hp,he⟩:=Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨(mem_support p _).mpr ?_,he⟩
    exact (mem_support (swap p) z).mp hp
  · intro z hz y hy he
    exact Prod.swap_injective he
  · intro z hz
    obtain ⟨hp,he⟩:=Finset.mem_filter.mp hz
    refine ⟨z.swap,Finset.mem_filter.mpr ⟨?_,he⟩,Prod.swap_swap _⟩
    apply (mem_support (swap p) _).mpr
    exact (mem_support p z).mp hp

theorem high_endpoint_bad_second (p : Law (α×β)) (q s d C0 : ℝ) (r : ℕ)
    (hq : 0<q) (hs : 0 < s) (hr : r≤4)
    (hcap : ((support (second p)).card:ℝ)≤32*q^r)
    (hflag : ((support p).card:ℝ)≤C0*q^4)
    (hpartner : ∀ b,0 < second p b→
      (((support p).filter fun z=>z.2=b).card:ℝ)≤2*q^(4-r))
    (hent : 4*Real.log q-entropy p≤d) :
    eventMass (second p) (highGoodFirst (swap p) (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0 := by
  have h:=high_endpoint_bad (swap p) q s d C0 r hq hs hr
    (by simpa only [first_swap] using hcap)
    (by simpa only [support_swap_card] using hflag)
    (by intro b hb; rw [support_swap_first_fiber]; exact hpartner b (by simpa only [first_swap] using hb))
    (by simpa only [entropy_swap] using hent)
  simpa only [first_swap] using h

lemma support_second_subset_image (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) : support (second p)⊆D.image Prod.snd := by
  intro b hb
  obtain ⟨z,hz,hf⟩:=map_positive p Prod.snd b (by simpa only [map_snd] using (mem_support _ _).mp hb)
  exact Finset.mem_image.mpr ⟨z,hD ((mem_support _ _).mpr hz),hf⟩

lemma support_second_fiber_card (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) (b : β) :
    ((support p).filter fun z=>z.2=b).card≤(Finset.univ.filter fun a=>(a,b)∈D).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro z hz
    obtain ⟨hz,he⟩:=Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [←he,Prod.mk.eta] using hD hz⟩
  · intro z hz y hy he
    exact Prod.ext he ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hy).2.symm)

theorem high_endpoint_bad_second_of_domain (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) (q s d C0 : ℝ) (r : ℕ)
    (hq : 0<q) (hs : 0 < s) (hr : r≤4)
    (hcap : ((D.image Prod.snd).card:ℝ)≤32*q^r)
    (hflag : (D.card:ℝ)≤C0*q^4)
    (hpartner : ∀ b,((Finset.univ.filter fun a=>(a,b)∈D).card:ℝ)≤2*q^(4-r))
    (hent : 4*Real.log q-entropy p≤d) :
    eventMass (second p) (highGoodFirst (swap p) (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0 := by
  apply high_endpoint_bad_second p q s d C0 r hq hs hr
  · exact (Nat.cast_le.mpr (Finset.card_le_card (support_second_subset_image p D hD))).trans hcap
  · exact (Nat.cast_le.mpr (Finset.card_le_card hD)).trans hflag
  · intro b _
    exact (Nat.cast_le.mpr (support_second_fiber_card p D hD b)).trans (hpartner b)
  · exact hent

lemma high_endpoint_mass (p : Law (α×β)) (q s d C0 : ℝ) (r : ℕ)
    (hbad : eventMass (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0)
    (hsmall : highBadMass s d C0≤(1:ℝ)/4) :
    (3:ℝ)/4≤eventMass (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s) := by
  have hc:=eventMass_complement (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s)
  linarith

end
end SharpRamseyFive.FiniteEntropy

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
local instance historyProducerSubtypeDecEq_r3f8671_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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

omit [Nonempty A] in
lemma history_in_domains (p : Law (((B×A)⊕T)→β)) (D : ((B×A)⊕T)→Finset β)
    (hp : InDomains p D) (n : ℕ) (h : BlockHistory B A T β n) :
    InDomains (historyPosterior p h) D := by
  induction n generalizing p with
  | zero => exact hp
  | succ n ih => exact ih _ (hp.fiber _ _) h.2.2

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
lemma marginal_support_subset {I γ : Type*} [Fintype I] [Fintype γ]
    (p : Law (I→γ)) (D : I→Finset γ) (hp : InDomains p D) (i : I) :
    support (map p (fun x=>x i))⊆D i := by
  intro b hb
  obtain ⟨x,hx,rfl⟩:=map_positive p (fun x=>x i) b ((mem_support _ _).mp hb)
  exact hp x hx i
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MarkedActualBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω κ α β I : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β] [Fintype I]

lemma pair_fiber_pred (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (P : α→Prop)
    (hP : ∀z,0<p z→P (x z)) (c : κ) (hc : 0<first (pair p ctx x) c) :
    ∀y,0<fiber (pair p ctx x) c y→P y := by
  intro y hy
  obtain ⟨z,hz,he,rfl⟩:=fiber_pair_source p ctx x c y hc hy
  exact hP z hz

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

theorem exists_good_window_pair (p : Law Ω) (a : Ω→W→T→ℝ) (b : Ω→W→ℝ)
    (ha : ∀ z v t,a z v t=0 ∨ a z v t=1)
    (hb : ∀ z v,b z v=0 ∨ b z v=1)
    (hsmall : mean p (fun z=>∑ v,∑ t,a z v t)+Fintype.card T*
      mean p (fun z=>∑ v,b z v)<(Fintype.card W:ℝ)*Fintype.card T) :
    ∃ z,0< p z ∧ ∃ v t,a z v t=0 ∧ b z v=0 := by
  by_contra hn
  push Not at hn
  have hp (z : Ω) (hz : 0< p z) :
      (Fintype.card W:ℝ)*Fintype.card T ≤
        (∑ v,∑ t,a z v t)+(Fintype.card T:ℝ)*∑ v,b z v := by
    have hpoint (v : W) (t : T) : 1≤ a z v t+b z v := by
      rcases ha z v t with h|h <;> rcases hb z v with h'|h'
      · exact False.elim (hn z hz v t h h')
      all_goals rw [h,h']; norm_num
    have H := Finset.sum_le_sum (s:=(Finset.univ:Finset W))
      (fun v _=> Finset.sum_le_sum (s:=(Finset.univ:Finset T)) (fun t _=> hpoint v t))
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,←Finset.mul_sum] using H
  have H:= mean_mono_pos p hp
  rw [mean_const,mean_add,mean_smul] at H
  linarith

variable {κ β : Type} [Fintype κ] [Fintype β] {w r n rem : ℕ}
  [Nonempty (Fin r)]

local instance goodWindowBlockDecEq_r3f8671_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.goodWindowIndexDecEq
theorem preRound_good_early_middle (μ : Law κ)
    (p : κ→Law (SharpRamseyFive.Windows.Slots w r→β))
    (S : κ→(Fin w×Bool)→Finset (Fin r)) (hrem : 0< rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card)
    (J d e : ℝ)
    (c : κ→BlockHistory (Fin w×Bool) (Fin r) (Fin w×Fin (2*r)) β n→
      SharpRamseyFive.Windows.Slots w r→SharpRamseyFive.Windows.Slots w r→ℝ)
    (hsmall : 5*mean (preRoundLaw μ p S n) (fun z=>
      ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S n J d e c z i)<2*r*w) :
    ∃ z,0< preRoundLaw μ p S n z ∧ ∃ v t,
      preRoundBad μ p S n J d e c z (Sum.inr (v,t))=0 ∧
      preRoundBad μ p S n J d e c z (Sum.inl ((v,false),z.2 (v,false)))=0 := by
  let ν:= preRoundLaw μ p S n
  let bad:= preRoundBad μ p S n J d e c
  let all:= fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),bad z i
  let selected:= fun z=>∑ b,bad z (Sum.inl (b,z.2 b))
  have hnon (z : (κ×BlockHistory (Fin w×Bool) (Fin r) (Fin w×Fin (2*r)) β n)×
      ((Fin w×Bool)→Fin r)) (i : SharpRamseyFive.Windows.Slots w r) : 0≤ bad z i :=
    badIndexIndicator_nonneg ..
  have hmid : mean ν (fun z=>∑ v,∑ t,bad z (Sum.inr (v,t)))≤ mean ν all := by
    apply mean_mono
    intro z
    dsimp only [all]
    rw [blockActive_sum]
    conv_rhs => arg 2; rw [Fintype.sum_prod_type]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun b _=> Finset.sum_nonneg fun a _=> hnon z _)
  have hearly : mean ν (fun z=>∑ v,bad z (Sum.inl ((v,false),z.2 (v,false))))≤ mean ν selected := by
    apply mean_mono
    intro z
    dsimp only [selected]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro v _
    exact Finset.single_le_sum (f:=fun b=>bad z (Sum.inl ((v,b),z.2 (v,b)))) (fun b _=>hnon z _) (Finset.mem_univ false)
  have hsel : (rem:ℝ)*mean ν selected≤ mean ν all := preRound_selected_bad μ p S n rem hrem hS J d e c
  have hsel0 : 0≤ mean ν selected := mean_nonneg _ _ (fun z=> Finset.sum_nonneg fun b _=> hnon z _)
  have hr' : (2*r:ℕ)≤4*rem := by omega
  have hx : (2*r:ℝ)*mean ν (fun z=>∑ v,bad z (Sum.inl ((v,false),z.2 (v,false))))≤4*mean ν all := by
    have h:= mul_le_mul_of_nonneg_left hearly (show (0:ℝ)≤2*r by positivity)
    have hr'' : (2*r:ℝ)≤4*rem := by exact_mod_cast hr'
    nlinarith [mul_le_mul_of_nonneg_right hr'' hsel0]
  apply exists_good_window_pair ν (fun z v t=> bad z (Sum.inr (v,t)))
    (fun z v=> bad z (Sum.inl ((v,false),z.2 (v,false))))
  · intro z v t
    exact badIndexIndicator_zero_or_one ..
  · intro z v
    exact badIndexIndicator_zero_or_one ..
  · simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using
      (show mean ν (fun z=>∑ v,∑ t,bad z (Sum.inr (v,t)))+(2*r:ℝ)*
        mean ν (fun z=>∑ v,bad z (Sum.inl ((v,false),z.2 (v,false))))<(w:ℝ)*(2*r) by
          dsimp only [ν,all,bad] at hmid hx ⊢
          nlinarith)
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WeightedLowHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem lowHits_card (hdim : finrank K V=5) (w : ℙ K V → ℝ) (A : ℝ)
    (hA : 0≤A) (hw : ∀ x,0≤w x ∧ w x≤A)
    (hm₀ : (3:ℝ)/4≤∑ x,w x) (hm₁ : ∑ x,w x≤1) :
    ((lowHits w).card:ℝ)≤64*(Nat.card K:ℝ)^5*A := by
  let q : ℝ:=Nat.card K
  let μ : ℝ:=((Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4)*(∑ x,w x)
  have hq : 0<q := by
    dsimp [q]
    exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hμ : 3/(8*q)≤μ := by
    have hd := mul_le_mul_of_nonneg_right (density_lower (K:=K) (d:=4) (by decide))
      (show 0≤∑ x,w x from Finset.sum_nonneg fun x _=>(hw x).1)
    have hh := mul_le_mul_of_nonneg_left hm₀ (show 0≤1/(2*q) by positivity)
    change (1/(2*q))*(∑ x,w x)≤μ at hd
    have he : (1/(2*q))*(3/4)=3/(8*q) := by ring
    rw [he] at hh
    exact hh.trans hd
  have hv := incidence_variance (d:=4) hdim (by decide) w
  have hs : ∑ x,w x^2≤A := by
    calc
      _ ≤ ∑ x,A*w x := Finset.sum_le_sum fun x _=>by nlinarith [(hw x).1,(hw x).2]
      _ = A*(∑ x,w x) := (Finset.mul_sum _ _ _).symm
      _ ≤ A := by nlinarith
  have hv' : (∑ y,(weightOnHyperplane w y-μ)^2)≤q^3*A := by
    exact hv.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hb : ((lowHits w).card:ℝ)*(1/(8*q))^2≤q^3*A := by
    calc
      _ = ∑ _y∈lowHits w,(1/(8*q))^2 := by simp
      _ ≤ ∑ y∈lowHits w,(weightOnHyperplane w y-μ)^2 := by
        apply Finset.sum_le_sum
        intro y hy
        have hh : weightOnHyperplane w y<1/(4*q) := (Finset.mem_filter.mp hy).2
        have he : 3/(8*q)-1/(4*q)=1/(8*q) := by ring
        have hh' : 1/(8*q)≤μ-weightOnHyperplane w y := by linarith
        nlinarith [show 0<1/(8*q) by positivity]
      _ ≤ ∑ y,(weightOnHyperplane w y-μ)^2 :=
        Finset.sum_le_univ_sum_of_nonneg fun _=>sq_nonneg _
      _ ≤ _ := hv'
  calc
    _ ≤ (q^3*A)/(1/(8*q))^2 := (le_div_iff₀ (by positivity)).mpr hb
    _ = 64*q^5*A := by field_simp; ring

theorem lowHits_mass (hdim : finrank K V=5) (w : ℙ K V → ℝ)
    (p : Law (ℙ K (Dual K V))) (G : Finset (ℙ K (Dual K V))) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hw : ∀ x,0≤w x ∧ w x≤A)
    (hm₀ : (3:ℝ)/4≤∑ x,w x) (hm₁ : ∑ x,w x≤1)
    (hp : ∀ y∈G,p y≤B) :
    eventMass p (G∩lowHits w)≤64*(Nat.card K:ℝ)^5*A*B := by
  calc
    _ ≤ ((G∩lowHits w).card:ℝ)*B := by
      unfold eventMass
      calc
        _ ≤ ∑ _y∈G∩lowHits w,B := Finset.sum_le_sum fun y hy=>hp y (Finset.mem_inter.mp hy).1
        _ = _ := by simp
    _ ≤ ((lowHits w).card:ℝ)*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    _ ≤ _ := mul_le_mul_of_nonneg_right (lowHits_card hdim w A hA hw hm₀ hm₁) hB

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α] {N w n : ℕ} [Nonempty (Fin n)]
  {admissible : (Fin N→α)→Prop}
local instance wpBDE_r3f8671_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance wpTDE_r3f8671_1 : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.wpSDE
omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (Fin n)] in
lemma windowTuple_injective : Function.Injective (fun x : Fin (w*(4*n))→FlagPair K V=>fun i : Slots w n=>x (slotEmbedding i)) := by
  intro x y h
  funext i
  obtain ⟨j,rfl⟩:=(slotEquiv w n).surjective i
  exact congrFun h j

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_domains (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (D : κ→Fin (w*(4*n))→Finset (FlagPair K V))
    (hD : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→
      InDomains (fiber (pair S.law ctx (windowTuple S)) c) (fun i=>D c (slotEmbedding i)) := by
  exact pair_fiber_domains S.law ctx (windowTuple S) _ (fun z hz i=>hD z hz (slotEmbedding i))

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_consistent (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→∀x,0<fiber (pair S.law ctx (windowTuple S)) c x→
      ∀i j,slotEmbedding i < slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2 := by
  apply pair_fiber_pred
  intro z hz i j hij
  exact hcons z hz _ _ hij
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_incident (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z)) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→∀x,0<fiber (pair S.law ctx (windowTuple S)) c x→
      ∀i,Incident (x i).1 (x i).2 := by
  apply pair_fiber_pred
  intro z hz i
  exact hinc z hz _
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_occupancy (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (M : ℝ) (hocc : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→∀x,0<fiber (pair S.law ctx (windowTuple S)) c x→
      ∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M := by
  apply pair_fiber_pred
  intro z hz
  exact occupancy_reindex (S.tuple z) slotEmbedding slotEmbedding.injective M (hocc z hz)
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_deficit (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (J : ℝ) :
    mean (first (pair S.law ctx (windowTuple S))) (fun c=>activeDeficit
      (fiber (pair S.law ctx (windowTuple S)) c) (blockActive (fun _=>Finset.univ)) J)=
    mean (first (pair S.law ctx S.tuple)) (fun c=>(w*(4*n):ℝ)*J-entropy (fiber (pair S.law ctx S.tuple) c)) := by
  simp only [blockActive_univ,activeDeficit,Finset.card_univ,card_slots,Nat.cast_mul,Nat.cast_ofNat]
  exact mean_fiber_entropy_injective S.law ctx S.tuple _ windowTuple_injective _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighPairVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma relationMass_good_incident (p : Law (ℙ K V)) (r : Law (ℙ K (Dual K V)))
    (G : Finset (ℙ K V)) (H : Finset (ℙ K (Dual K V))) :
    relationMass (fun a b=>a∈G ∧ b∈H ∧ Incident a b) p r =
      ∑ b∈H,r b*weightOnHyperplane (fun a=>if a∈G then p a else 0) b := by
  rw [relationMass_by_target]
  have he : (∑ b∈H,r b*weightOnHyperplane (fun a=>if a∈G then p a else 0) b)=
      ∑ b,if b∈H then r b*weightOnHyperplane (fun a=>if a∈G then p a else 0) b else 0 := by
    simp only [Finset.sum_ite_mem,Finset.univ_inter]
  rw [he]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_filter]
  by_cases hb : b∈H
  · simp only [hb,true_and,ite_true,weightOnHyperplane,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a∈G <;> by_cases hi : Incident a b <;>
      simp only [ha,hi,incidenceEntry,ite_true,ite_false,and_true,and_false,
        one_mul,zero_mul,mul_zero]
  · simp only [hb,and_false,false_and,ite_false,Finset.sum_const_zero,mul_zero]

theorem high_pair_incident_lower (hdim : finrank K V=5)
    (p : Law (ℙ K V)) (r : Law (ℙ K (Dual K V)))
    (G : Finset (ℙ K V)) (H : Finset (ℙ K (Dual K V))) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hp : ∀ a∈G,p a≤A) (hr : ∀ b∈H,r b≤B)
    (hG : (3:ℝ)/4≤eventMass p G) (hH : (3:ℝ)/4≤eventMass r H)
    (hsmall : 64*(Nat.card K:ℝ)^5*A*B≤(1:ℝ)/4) :
    1/(8*(Nat.card K:ℝ)) ≤ relationMass (fun a b=>a∈G ∧ b∈H ∧ Incident a b) p r := by
  let w : ℙ K V→ℝ:=fun a=>if a∈G then p a else 0
  have hw : ∀ a,0≤w a ∧ w a≤A := by
    intro a
    dsimp [w]
    split_ifs with ha
    · exact ⟨p.nonneg a,hp a ha⟩
    · exact ⟨le_rfl,hA⟩
  have hm : (∑ a,w a)=eventMass p G := by simp [w,eventMass,Finset.sum_ite_mem]
  have hlow := lowHits_mass hdim w r H A B hA hB hw (hm ▸ hG)
    (hm ▸ eventMass_le_one p G) hr
  have hpart : eventMass r (H\lowHits w)+eventMass r (H∩lowHits w)=eventMass r H := by
    unfold eventMass
    exact by
      rw [←Finset.sum_union (Finset.disjoint_sdiff_inter H (lowHits w)),
        Finset.sdiff_union_inter]
  have hmass : (1:ℝ)/2≤eventMass r (H\lowHits w) := by linarith
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hn : ∀ b,0≤weightOnHyperplane w b := by
    intro b
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (by unfold incidenceEntry;split_ifs <;> norm_num) (hw a).1
  rw [relationMass_good_incident]
  calc
    _ = ((1:ℝ)/2)*(1/(4*(Nat.card K:ℝ))) := by ring
    _ ≤ eventMass r (H\lowHits w)*(1/(4*(Nat.card K:ℝ))) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = ∑ b∈H\lowHits w,r b*(1/(4*(Nat.card K:ℝ))) := by unfold eventMass; rw [Finset.sum_mul]
    _ ≤ ∑ b∈H\lowHits w,r b*weightOnHyperplane w b := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_left _ (r.nonneg b)
      have hh := (Finset.mem_sdiff.mp hb).2
      have he : ¬weightOnHyperplane w b<1/(4*(Nat.card K:ℝ)) := by
        intro he
        exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
      exact le_of_not_gt he
    _ ≤ ∑ b∈H,r b*weightOnHyperplane w b :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun b _ _=>mul_nonneg (r.nonneg b) (hn b))
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighLowConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {n : ℕ}

omit [Finite K] [FiniteDimensional K V] in
lemma high_collision_nonneg (p : Law (Fin n→FlagPair K V)) (s : ℝ) (i j : Fin n) :
    0≤highCollision p s i j := tupleCollision_nonneg ..

omit [Finite K] in
lemma high_three_low_conflict (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (s : ℝ)
    (hcons : ∀ x,0<p x→TupleConsistent x) (i j : Fin n) (hij : i<j) :
    relationMass (highThreeGood p s i j) (first (tupleMarginal p i)) (second (tupleMarginal p j))≤
      80004*(entropy (tupleMarginal p i)+entropy (tupleMarginal p j)-
        entropy (pair p (fun x=>x i) (fun x=>x j))+highCollision p s i j) := by
  apply tuple_low_conflict hdim p Projectivization.rep Projectivization.rep (highThreeGood p s) ?_ i j hij
  intro x hx i j hij hg
  exact (incident_iff _ _).mp (hcons x hx i j hij hg.2.2)

theorem high_three_pair_impossible (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (s ε : ℝ)
    (hcons : ∀ x,0<p x→TupleConsistent x) (i j : Fin n) (hij : i<j)
    (hA : (3:ℝ)/4≤eventMass (first (tupleMarginal p i)) (highThreeLeft (tupleMarginal p i) s))
    (hB : (3:ℝ)/4≤eventMass (second (tupleMarginal p j)) (highThreeRight (tupleMarginal p j) s))
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*(Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hgood : entropy (tupleMarginal p i)+entropy (tupleMarginal p j)-
      entropy (pair p (fun x=>x i) (fun x=>x j))+highCollision p s i j≤ε)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ))) : False := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hl:=high_pair_incident_lower hdim (first (tupleMarginal p i)) (second (tupleMarginal p j))
    _ _ (Real.exp s/(Nat.card K:ℝ)^3) (Real.exp s/(Nat.card K:ℝ)^3) (by positivity) (by positivity)
    (by
      intro a ha
      have hh:=(Finset.mem_filter.mp (show a∈highGoodFirst _ _ _ _ _ from ha)).2
      exact (le_div_iff₀ (pow_pos hq 3)).mpr (by simpa only [mul_comm] using hh))
    (by
      intro b hb
      have hh:=(Finset.mem_filter.mp (show b∈highGoodFirst _ _ _ _ _ from hb)).2
      rw [first_swap] at hh
      exact (le_div_iff₀ (pow_pos hq 3)).mpr (by simpa only [mul_comm] using hh)) hA hB hvar
  have hu:=high_three_low_conflict hdim p s hcons i j hij
  exact (hl.trans (hu.trans (mul_le_mul_of_nonneg_left hgood (by norm_num)))).not_gt hsmall
end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighDomainEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module ProjectiveIncidence FiniteEntropy HighSamples
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

attribute [local instance] OAI.SharpRamseyFive.Marking.hdePDE
attribute [local instance] OAI.SharpRamseyFive.Marking.hdeDDE
omit [FiniteDimensional K V] in
lemma HighCaps.endpoint_bad {D : Finset (FlagPair K V)} {r r' : ℕ}
    (h : HighCaps D r r') (p : Law (FlagPair K V)) (hD : support p⊆D)
    (hr : r≤4) (hr' : r'≤4) (s d : ℝ) (hs : 0 < s)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d) :
    eventMass (FiniteEntropy.first p) (highLeft p r' s)ᶜ≤highBadMass s d 153 ∧
      eventMass (FiniteEntropy.second p) (highRight p r s)ᶜ≤highBadMass s d 153 := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  constructor
  · exact high_endpoint_bad_of_domain p D hD (Nat.card K) s d 153 r' hq hs hr'
      h.first h.flag h.firstPartners hent
  · exact high_endpoint_bad_second_of_domain p D hD (Nat.card K) s d 153 r hq hs hr
      h.second h.flag h.secondPartners hent

omit [FiniteDimensional K V] in
lemma HighCaps.three_mass {D : Finset (FlagPair K V)} (h : HighCaps D 3 3)
    (p : Law (FlagPair K V)) (hD : support p⊆D) (s d : ℝ) (hs : 0 < s)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d) (hsmall : highBadMass s d 153≤(1:ℝ)/4) :
    (3:ℝ)/4≤eventMass (FiniteEntropy.first p) (highThreeLeft p s) ∧
      (3:ℝ)/4≤eventMass (FiniteEntropy.second p) (highThreeRight p s) := by
  have hb:=h.endpoint_bad p hD (by decide) (by decide) s d hs hent
  constructor
  · exact high_endpoint_mass p (Nat.card K) s d 153 3 hb.1 hsmall
  · have hcomp:=eventMass_complement (FiniteEntropy.second p) (highThreeRight p s)
    change eventMass (FiniteEntropy.first p) (highThreeLeft p s)ᶜ≤highBadMass s d 153 ∧
      eventMass (FiniteEntropy.second p) (highThreeRight p s)ᶜ≤highBadMass s d 153 at hb
    linarith [hb.2]

end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Filter Asymptotics Real ParameterHierarchy FiniteEntropy
open scoped Topology
noncomputable section

lemma high_bad_uniform {σ D b C : ℝ} (hσ : 1≤σ) (_ : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    highBadMass (D*σ^(3*b)) (D*σ^b) C≤
      Real.exp (-σ^(4*b))+51*σ^(-2*b)+(50*C+Real.log 2+32)/σ^(4*b) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hd : 0<D := (Real.rpow_pos_of_pos hs b).trans_le hD
  have hlow : σ^(4*b)≤D*σ^(3*b) := by
    calc
      _ = σ^b*σ^(3*b) := by rw [←Real.rpow_add hs];congr 1;ring
      _ ≤_ := mul_le_mul_of_nonneg_right hD (by positivity)
  have he : (D*σ^b)/(D*σ^(3*b))=σ^(-2*b) := by
    rw [mul_div_mul_left _ _ hd.ne',←Real.rpow_sub hs]
    congr 1
    ring
  have hc : 0≤50*C+Real.log 2+32 := by have := Real.log_nonneg (by norm_num : (1:ℝ)≤2);positivity
  have hc' := div_le_div_of_nonneg_left hc (Real.rpow_pos_of_pos hs _) hlow
  unfold highBadMass
  calc
    _ =Real.exp (-(D*σ^(3*b)))+51*((D*σ^b)/(D*σ^(3*b)))+
      (50*C+Real.log 2+32)/(D*σ^(3*b)) := by ring
    _ ≤_ := by rw [he];gcongr

lemma high_four_variance {q s σ : ℝ} {r' : ℕ} (hq : 1≤q)
    (he : Real.exp σ=q) (hr : 2 ≤ r') (hs : 2*s≤σ/2) :
    64*q^5*(2*Real.exp s/q^r')*(Real.exp s/q^4)≤128*Real.exp (-σ/2) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hp := pow_le_pow_right₀ hq hr
  calc
    _ ≤64*q^5*(2*Real.exp s/q^2)*(Real.exp s/q^4) := by gcongr
    _ =128*(Real.exp s*Real.exp s/q) := by field_simp;ring
    _ =128*Real.exp (2*s-σ) := by rw [Real.exp_sub,←Real.exp_add,he];congr 2;congr 1;ring
    _ ≤_ := by gcongr;linarith

lemma high_four_growth {q σ b : ℝ} {h : ℕ} (hq : 1≤q)
    (hl : q*σ^b≤h) :
    (1-1/(5*q))^h≤Real.exp (-(σ^b)/5) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hnon : 0≤1-1/(5*q) := by
    have hh : 1/(5*q)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  calc
    _ ≤(Real.exp (-(1/(5*q))))^h := pow_le_pow_left₀ hnon (Real.one_sub_le_exp_neg _) h
    _ = Real.exp (-(h:ℝ)/(5*q)) := by rw [←Real.exp_nat_mul];congr 1;ring
    _ ≤_ := by
      apply Real.exp_le_exp.mpr
      have hh : σ^b/5≤(h:ℝ)/(5*q) := (le_div_iff₀ (by positivity)).mpr (by nlinarith [hl])
      simpa only [neg_div] using neg_le_neg hh

lemma high_four_conflict {σ q b : ℝ} {h : ℕ} (hσ : 0<σ) (hq : 0<q)
    (hh : (h:ℝ)≤2*q*σ^b) :
    12*h*(σ^(-2000*b)/q)≤24*σ^(-1999*b) := by
  calc
    _ ≤12*(2*q*σ^b)*(σ^(-2000*b)/q) := by gcongr
    _ =24*(σ^b*σ^(-2000*b)) := by field_simp;ring
    _ =_ := by rw [←Real.rpow_add hσ];congr 2;ring

lemma highFourLoss_bound {σ D b : ℝ} {q r' h : ℕ}
    (hσ : 1≤σ) (hb : 0<b) (hD : σ^b≤D) (hq : 1≤q)
    (he : Real.exp σ=q) (hr : 2 ≤ r') (hs : 2*(D*σ^(3*b))≤σ/2)
    (hl : (q:ℝ)*σ^b≤h) (hh : (h:ℝ)≤2*q*σ^b) :
    highFourLoss q r' h (D*σ^(3*b)) (D*σ^b) (σ^(-2000*b)/q)≤
      Real.exp (-σ^(4*b))+51*σ^(-2*b)+(50*153+Real.log 2+32)/σ^(4*b)+
      128*Real.exp (-σ/2)+3*Real.exp (-(σ^b)/5)+24*σ^(-1999*b) := by
  unfold highFourLoss
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  apply add_le_add
  · apply add_le_add
    · exact add_le_add (high_bad_uniform hσ hb hD (by norm_num)) (high_four_variance hq' he hr hs)
    · exact mul_le_mul_of_nonneg_left (high_four_growth hq' hl) (by norm_num)
  · exact high_four_conflict (zero_lt_one.trans_le hσ) (zero_lt_one.trans_le hq') hh

theorem eventually_high_four_loss {η : ℝ} (hη : 0<η) (ρ : ℝ) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (q r' h : ℕ),σ^beta η≤D→D≤σ^(1-η/2)→
      1≤q→Real.exp σ=q→2 ≤ r'→(q:ℝ)*σ^beta η≤h→(h:ℝ)≤2*q*σ^beta η→
      highFourLoss q r' h (D*σ^(3*beta η)) (D*σ^beta η) (σ^(-2000*beta η)/q)≤ρ := by
  have hb:=beta_pos hη
  have hpow:=tendsto_rpow_atTop hb
  have h4 : 0<4*beta η := by positivity
  have ht1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop h4)
  have ht2 := (tendsto_rpow_neg_atTop (by positivity : 0<2*beta η)).const_mul 51
  have ht3 : Tendsto (fun σ : ℝ=>(50*153+Real.log 2+32)/σ^(4*beta η)) atTop (𝓝 0) :=
    (tendsto_rpow_atTop h4).const_div_atTop _
  have ht4 : Tendsto (fun σ : ℝ=>128*Real.exp (-σ/2)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
    simpa only [Function.comp_apply,id_eq,neg_div,mul_zero] using ht.const_mul 128
  have ht5 : Tendsto (fun σ : ℝ=>3*Real.exp (-(σ^beta η)/5)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.atTop_div_const (by norm_num : (0:ℝ)<5))
    simpa only [Function.comp_apply,id_eq,neg_div,mul_zero] using ht.const_mul 3
  have ht6 := (tendsto_rpow_neg_atTop (by positivity : 0<1999*beta η)).const_mul 24
  have ht:=((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6
  simp only [Function.comp_apply,mul_zero,add_zero] at ht
  have he : 0<η/2-3*beta η := by unfold beta;linarith
  have hsmall:=(tendsto_rpow_neg_atTop he).eventually_lt_const (by norm_num : (0:ℝ)<1/4)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hρ,hsmall] with σ hσ hρ' hsmall
  intro D q r' h hlo hhi hq heq hr hhlo hhhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hDsmall : 2*(D*σ^(3*beta η))≤σ/2 := by
    have hl : D*σ^(3*beta η)≤σ*σ^(-(η/2-3*beta η)) := by
      calc
        _ ≤σ^(1-η/2)*σ^(3*beta η) := mul_le_mul_of_nonneg_right hhi (by positivity)
        _ =_ := by
          rw [←Real.rpow_add hs]
          nth_rw 2 [←Real.rpow_one σ]
          rw [←Real.rpow_add hs]
          congr 1
          ring
    nlinarith [mul_lt_mul_of_pos_left hsmall hs]
  exact (highFourLoss_bound hσ hb hlo hq heq hr hDsmall hhlo hhhi).trans (by simpa only [neg_mul] using hρ'.le)
end
end

open Filter Real ParameterHierarchy FiniteEntropy
open scoped Topology
noncomputable section

lemma eventually_stage_scale {η : ℝ} (_ : 0<η) (a δ : ℝ)
    (ha : a*beta η<η/2) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,D≤σ^(1-η/2)→D*σ^(a*beta η)≤δ*σ := by
  have he : 0<η/2-a*beta η := sub_pos.mpr ha
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_neg_atTop he).eventually_lt_const hδ] with σ hσ ht
  intro D hD
  have hs : 0<σ := zero_lt_one.trans_le hσ
  calc
    _ ≤ σ^(1-η/2)*σ^(a*beta η) := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = σ^(-(η/2-a*beta η))*σ := by
      rw [←Real.rpow_add hs,show 1-η/2+a*beta η= -(η/2-a*beta η)+1 by ring,
        Real.rpow_add hs,Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right ht.le hs.le

lemma highBadMass_le_highFourLoss (q r' h : ℕ) (hq : 1≤q) (s d ε : ℝ) (he : 0≤ε) :
    highBadMass s d 153≤highFourLoss q r' h s d ε := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hh : 0<5*(q:ℝ) := by linarith
  have hz : 0≤1-1/(5*(q:ℝ)) := sub_nonneg.mpr ((div_le_one hh).mpr (by linarith))
  unfold highFourLoss
  have h1 : 0≤64*(q:ℝ)^5*(2*Real.exp s/(q:ℝ)^r')*(Real.exp s/(q:ℝ)^4) := by positivity
  have h2 : 0≤3*(1-1/(5*(q:ℝ)))^h := by positivity
  have h3 : 0≤12*h*ε := by positivity
  linarith

lemma high_small_geometry {q s ε : ℝ} (hq : 0<q)
    (h1 : 80*Real.exp s≤q) (h2 : 256*Real.exp (2*s)≤q)
    (h3 : 640032*(ε*q)<1) :
    2*q^2*(2*Real.exp s/q^4)≤1/(20*q) ∧
    64*q^5*(Real.exp s/q^3)*(Real.exp s/q^3)≤(1:ℝ)/4 ∧
    80004*ε<1/(8*q) := by
  refine ⟨?_,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : 0<20*q)).mpr
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg q)]
  · have he : Real.exp (2*s)=Real.exp s*Real.exp s := by rw [two_mul,Real.exp_add]
    rw [he] at h2
    have hh : 64*q^5*(Real.exp s/q^3)*(Real.exp s/q^3)=64*Real.exp s*Real.exp s/q := by field_simp
    rw [hh]
    exact (div_le_iff₀ hq).mpr (by linarith)
  · apply (lt_div_iff₀ (by positivity : 0<8*q)).mpr
    nlinarith

theorem eventually_high_geometry {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,D≤σ^(1-η/2)→
      2*(Real.exp σ)^2*(2*Real.exp (D*σ^(3*beta η))/(Real.exp σ)^4)≤1/(20*Real.exp σ) ∧
      64*(Real.exp σ)^5*(Real.exp (D*σ^(3*beta η))/(Real.exp σ)^3)*
        (Real.exp (D*σ^(3*beta η))/(Real.exp σ)^3)≤(1:ℝ)/4 ∧
      80004*(σ^(-2000*beta η)/Real.exp σ)<1/(8*Real.exp σ) := by
  have ha : 3*beta η<η/2 := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>640032*σ^(-2000*beta η)) atTop (𝓝 0) := by
    have hb : 0<2000*beta η := by exact mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul,mul_zero] using (tendsto_rpow_neg_atTop hb).const_mul 640032
  filter_upwards [eventually_stage_scale hη 3 (1/4) ha (by norm_num),
    eventually_ge_atTop (4*Real.log 256),eventually_ge_atTop (0:ℝ),
    ht.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hscale hσ hσ0 he
  intro D hD
  have hs:=hscale D hD
  apply high_small_geometry (Real.exp_pos σ)
  · calc
      _ ≤256*Real.exp (D*σ^(3*beta η)) := mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_nonneg _)
      _ =Real.exp (Real.log 256+D*σ^(3*beta η)) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
      _ ≤_ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ =Real.exp (Real.log 256+2*(D*σ^(3*beta η))) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
      _ ≤_ := Real.exp_le_exp.mpr (by linarith)
  · simpa only [div_mul_cancel₀ _ (Real.exp_ne_zero σ)] using he
end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_OrderedHighConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

omit [Finite K] [FiniteDimensional K V] in
lemma orderedHighCollision_nonneg (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s : ℝ) (i j : I) :
    0≤orderedHighCollision p e s i j := add_nonneg (high_collision_nonneg ..) (high_collision_nonneg ..)
omit [Finite K] [FiniteDimensional K V] in
lemma orderedHighCollision_symm (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s : ℝ) (i j : I) :
    orderedHighCollision p e s i j=orderedHighCollision p e s j i := add_comm _ _

omit [Finite K] [FiniteDimensional K V] in
lemma orderedLaw_consistent (p : Law (I→FlagPair K V)) (e : I≃Fin n)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2) :
    ∀ x,0<orderedLaw p e x→TupleConsistent x := by
  intro x hx a b hab hf
  obtain ⟨y,hy,he⟩:=orderedLaw_positive p e x hx
  have h:=hcons y hy (e.symm a) (e.symm b) (by simpa using hab)
  simpa only [←he,Equiv.apply_symm_apply] using h (by simpa only [←he,Equiv.apply_symm_apply] using hf)

lemma orderedHigh_pair_impossible (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j)
    (hA : (3:ℝ)/4≤eventMass (first (map p (fun x=>x i))) (highThreeLeft (map p (fun x=>x i)) s))
    (hB : (3:ℝ)/4≤eventMass (second (map p (fun x=>x j))) (highThreeRight (map p (fun x=>x j)) s))
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*(Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hgood : entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
      entropy (pair p (fun x=>x i) (fun x=>x j))+orderedHighCollision p e s i j≤ε)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ))) : False := by
  apply high_three_pair_impossible hdim (orderedLaw p e) s ε (orderedLaw_consistent p e hcons)
    (e i) (e j) hij
  · simpa only [tupleMarginal,orderedLaw_marginal] using hA
  · simpa only [tupleMarginal,orderedLaw_marginal] using hB
  · exact hvar
  · simp only [tupleMarginal,orderedLaw_marginal,orderedLaw_pair]
    apply le_trans _ hgood
    dsimp only [orderedHighCollision]
    linarith [high_collision_nonneg (orderedLaw p e) s (e j) (e i)]
  · exact hsmall
end
end SharpRamseyFive.Marking

end

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N w r : ℕ} [Nonempty (Fin r)]

local instance highDomainThreeBlockDE_r3f8671_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.highDomainThreeIndexDE
omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
  [Nonempty (Fin r)] in
theorem high_three_domain_good_pair_impossible (hdim : finrank K V=5)
    (D : Slots w r→Finset (FlagPair K V))
    (p : Law (Slots w r→FlagPair K V))
    (hD : ∀i,support (map p (fun x=>x i))⊆D i)
    (hcap : ∀i,HighCaps (D i) 3 3)
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i < slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (J d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hs : 0 < s)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*
      (Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ)))
    (sel : (Fin w×Bool)→Fin r) (v : Fin w) (t : Fin (2*r))
    (hgoodE : indexBad J d ε p (orderedHighCollision p (slotEquiv w r) s) sel
      (Sum.inl ((v,false),sel (v,false)))=0)
    (hgoodM : indexBad J d ε p (orderedHighCollision p (slotEquiv w r) s) sel
      (Sum.inr (v,t))=0) : False := by
  let i : Slots w r:=Sum.inl ((v,false),sel (v,false))
  let j : Slots w r:=Sum.inr (v,t)
  have hi:=good_index_scores J d ε p _ (orderedHighCollision_nonneg p (slotEquiv w r) s) sel i hgoodE
  have hj:=good_index_scores J d ε p _ (orderedHighCollision_nonneg p (slotEquiv w r) s) sel j hgoodM
  have hA:=(hcap i).three_mass (map p (fun x=>x i)) (hD i) s d hs (by linarith [hi.1]) hbad
  have hB:=(hcap j).three_mass (map p (fun x=>x j)) (hD j) s d hs (by linarith [hj.1]) hbad
  apply orderedHigh_pair_impossible hdim p (slotEquiv w r) s ε hcons i j
    (representative_early v (sel (v,false)) t) hA.1 hB.2 hvar ?_ hsmall
  exact good_index_scores_reverse J d ε p _
    (orderedHighCollision_nonneg p (slotEquiv w r) s)
    (orderedHighCollision_symm p (slotEquiv w r) s) sel j hgoodM (v,false) trivial

omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_three_domain_preRound_impossible {κ : Type} [Fintype κ] {n rem : ℕ}
    (hdim : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots w r→FlagPair K V))
    (D : κ→Slots w r→Finset (FlagPair K V))
    (hD : ∀a,0<μ a→InDomains (p a) (D a))
    (hcap : ∀a,0<μ a→∀i,HighCaps (D a i) 3 3)
    (hcons : ∀ a,0<μ a→∀ x,0<p a x→∀ i j,slotEmbedding i < slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (S : κ→(Fin w×Bool)→Finset (Fin r)) (hrem : 0 < rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card)
    (J d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hs : 0 < s)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*
      (Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ)))
    (hbudget : 5*mean (preRoundLaw μ p S n) (fun z=>
      ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),
        preRoundBad μ p S n J d ε
          (fun a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w r) s) z i)<2*r*w) :
    False := by
  obtain ⟨z,hz,v,t,hM,hE⟩:=preRound_good_early_middle (n:=n) (rem:=rem) μ p S hrem hr hS J d ε
    (fun a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w r) s) hbudget
  have ha:=(preRound_positive μ p S n z hz).1
  apply high_three_domain_good_pair_impossible hdim (D z.1.1)
    (historyPosterior (p z.1.1) z.1.2) _ (hcap _ ha) _
    J d s ε hJ hs hbad hvar hsmall z.2 v t hE hM
  · intro i
    exact marginal_support_subset _ _ (history_in_domains _ _ (hD _ ha) n z.1.2) i
  · intro x hx i j hij hi
    exact hcons _ ha x (history_support (p z.1.1) n z.1.2 x hx) i j hij hi

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_HighThreePrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}

local instance htpBDE_r3f8671_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance htpTDE_r3f8671_1 : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.htpIDE
omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_three_prepared_impossible (hd : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
    (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
    (hcap : ∀c,0 < map S.law ctx c→∀i,HighCaps (P.domain c i) 3 3)
    (rounds rem : ℕ) (hrounds : 0 < rounds) (hrem : 0 < rem)
    (hn : n≤2*rem) (hroom : rem+rounds≤n)
    (d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hdp : 0<d) (hs : 2 ≤ s) (he : 0<ε)
    (hlog : Real.log 32+3*s<Real.log (Nat.card K))
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*
      (Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ)))
    (hbudget : 5*(B/d+(2*B/rounds+(16*n*M)/rem)/ε)<2*n) : False := by
  let μ:=first (pair S.law ctx (windowTuple S))
  let p:=fiber (pair S.law ctx (windowTuple S))
  let elig:=fun _ : κ=>fun _ : Fin 1×Bool=>(Finset.univ : Finset (Fin n))
  have hS : ∀c,0<μ c→∀b,rem+rounds≤(elig c b).card := by
    intro c hc b
    simpa only [elig,Finset.card_univ,Fintype.card_fin] using hroom
  have hD:=window_posterior_domains S ctx P.domain P.contains
  have hdef : mean μ (fun c=>activeDeficit (p c) (blockActive (elig c)) J)≤B := by
    dsimp only [μ,p,elig]
    rw [window_posterior_deficit]
    have h:=P.deficit
    simp only [Nat.cast_mul,Nat.cast_ofNat] at h
    have he : psFinDE (1*(4*n)) = (inferInstance : DecidableEq (Fin (1*(4*n)))) := Subsingleton.elim _ _
    rw [he] at h
    exact h
  obtain ⟨i,hi⟩:=exists_high_three_round hd μ p elig rounds rem hrounds hrem hS J d ε B s M
    hdp he (fun c i=>P.domain c (slotEmbedding i)) (fun c i=>P.cap c (slotEmbedding i)) hD
    (fun c _=>by simpa only [elig,blockActive_univ] using fixedOutside_univ (p c)) hdef hs hlog
    (window_posterior_incident S ctx P.incident) (window_posterior_occupancy S ctx M P.occupancy)
  apply high_three_domain_preRound_impossible (n:=i.val) (rem:=rem) hd μ p
    (fun c i=>P.domain c (slotEmbedding i)) hD
    (fun c hc i=>hcap c (by simpa only [μ,first_pair] using hc) (slotEmbedding i))
    (window_posterior_consistent S ctx P.consistent) elig hrem hn
    (fun c hc b=>by have:=hS c hc b;have:=i.isLt;omega)
    J d s ε hJ (by linarith) hbad hvar hsmall
  have hh:=mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤5)
  simp only [Nat.cast_one,one_mul,mul_one] at hh ⊢
  have heq : 4*(4*(n:ℝ))*M=16*n*M := by ring
  rw [heq] at hh
  exact hh.trans_lt hbudget
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

theorem eventually_high_three_prepared_impossible_oai {η : ℝ} (hη : 0<η) (c Cb Cm : ℝ)
    (hc : 0 < c) (hCb : 0≤Cb) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
      [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
    ∀ (N n : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (D J B M : ℝ) (P : Prepared S ctx J B M),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      c*Real.exp σ*σ^(1+η)≤n→σ^beta η≤D→D≤σ^(1-η/2)→
      B≤Cb*n*D*σ^(-beta η)→M≤Cm*σ→4*σ≤J→
      (∀a,0 < map S.law ctx a→∀i,HighCaps (P.domain a i) 3 3)→False := by
  have ha : 3000*beta η<η/2 := by unfold beta;linarith
  have ha3 : 3*beta η<η/2 := by unfold beta;linarith
  filter_upwards [eventually_deletion_budget hη Cb (16*Cm) (2/c) (1/1000) hCb (by positivity) (by positivity) (by norm_num),
    eventually_high_four_loss hη (1/1000) (by norm_num),eventually_high_geometry hη,
    eventually_stage_scale hη 3000 (c/4) ha (by positivity),
    eventually_stage_scale hη 3 (1/8) ha3 (by norm_num),
    (tendsto_rpow_atTop (beta_pos hη)).eventually_ge_atTop 2,
    eventually_ge_atTop (8*(Real.log 32+1))] with σ hdel hfour hgeom hscale hsc3 ht hlog
  intro K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ _ _ N n _ admissible S ctx D J B M P
    hd hσ hq hlen hD hDhi hB hM hJ hcap
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqp : 2≤Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card (α:=K))
  have hqr : (2:ℝ)≤Nat.card K := by exact_mod_cast hqp
  have hqpos : (0:ℝ)<Nat.card K := by linarith
  have hDpos : 0<D := (Real.rpow_pos_of_pos hs _).trans_le hD
  have hσeq : Real.log (Nat.card K)=σ := by rw [←hq,Real.log_exp]
  let T:=⌊(Nat.card K:ℝ)*D*σ^(3000*beta η)⌋₊
  let rem:=n-T
  let h:=⌈(Nat.card K:ℝ)*σ^beta η⌉₊
  obtain ⟨hn,hT,hrem,hnrem,hroom,hTlo,hremlo,hhlo,hhhi⟩:=
    high_integer_ranges hη hσ hqr hc hD (by nlinarith [hscale D hDhi]) n (by simpa only [hq] using hlen)
  have hfour':=hfour D (Nat.card K) 3 h hD hDhi (by omega) hq (by norm_num) hhlo hhhi
  have hgeom':=hgeom D hDhi
  rw [hq] at hgeom'
  have hcol : 16*(n:ℝ)*M≤(16*Cm)*σ*n := by nlinarith [mul_le_mul_of_nonneg_left hM (by positivity : (0:ℝ)≤16*n)]
  have hbudget:=hdel (Nat.card K) D n B T rem (16*n*M) hqpos hDpos (Nat.cast_nonneg _) hB hTlo hremlo hcol
  have hε : 0<σ^(-2000*beta η)/(Nat.card K:ℝ) := by positivity
  have hbad : highBadMass (D*σ^(3*beta η)) (D*σ^beta η) 153≤(1:ℝ)/4 :=
    (highBadMass_le_highFourLoss (Nat.card K) 3 h (by omega) _ _ _ hε.le).trans
      (hfour'.trans (by norm_num))
  have hslo : 2≤D*σ^(3*beta η) := by
    have hh : 1≤σ^(3*beta η) := Real.one_le_rpow hσ (by have:=beta_pos hη;positivity)
    have h2 := ht.trans hD
    nlinarith
  apply high_three_prepared_impossible hd S ctx J B M P hcap T rem hT hrem hnrem hroom
    (D*σ^beta η) (D*σ^(3*beta η)) (σ^(-2000*beta η)/(Nat.card K:ℝ))
    (by simpa only [hσeq] using hJ) (by positivity) hslo hε
    (by rw [hσeq];have:=hsc3 D hDhi;linarith) hbad hgeom'.2.1 hgeom'.2.2
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  linarith

end

end SharpRamseyFive.SelectedTuple

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.SelectedTuple.eventually_high_three_prepared_impossible_oai := @OAI.SharpRamseyFive.SelectedTuple.eventually_high_three_prepared_impossible_oai
