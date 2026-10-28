-- Prove2me | solution 1 for OAI.SharpRamseyFive.SelectedTuple.high_prepared_round
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:49:03.959628+00:00
-- url     : https://prove2.me/submissions/cda9ce36-35db-4f56-9ccb-1b37ae09f102

import Mathlib
import Definitions.Def_OAIQ060R004

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem conditional_deficit_le (p : Law (α × β)) (capA capB : ℝ)
    (hcap : entropy (first p) ≤ capA) :
    (∑ a,first p a*(capB-entropy (fiber p a))) ≤ capA+capB-entropy p := by
  have he : (∑ a,first p a*(capB-entropy (fiber p a))) =
      capB-∑ a,first p a*entropy (fiber p a) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,(first p).sum_one,one_mul]
  rw [he,entropy_chain]
  linarith

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

lemma rejection_mass (p : Law α) (E : Finset α) :
    (∑ a,if a∈E then 0 else p a)=1-eventMass p E := by
  have h : (∑ a,if a∈E then p a else 0)+(∑ a,if a∈E then 0 else p a)=1 := by
    rw [←Finset.sum_add_distrib]
    convert p.sum_one using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have he : (∑ a,if a∈E then p a else 0)=eventMass p E := by
    classical
    simp [eventMass]
  linarith

lemma iid_cons (p : Law α) {n : ℕ} (a : α) (x : Fin n → α) :
    iid p (Fin (n+1)) (Fin.cons a x)=p a*iid p (Fin n) x := by
  simp [iid,Fin.prod_univ_succ]

omit [Fintype α] in
lemma firstAccepted_cons (E : Finset α) {n : ℕ} (a : α) (x : Fin n → α) :
    firstAccepted E (Fin.cons a x)=if a∈E then some a else firstAccepted E x := by
  simp only [firstAccepted,Fin.cons_zero,Fin.cons_succ]

lemma sum_iid_succ (p : Law α) (n : ℕ) (f : (Fin (n+1) → α) → ℝ) :
    (∑ x,iid p (Fin (n+1)) x*f x)=
      ∑ a,∑ x,p a*iid p (Fin n) x*f (Fin.cons a x) := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α))
    (fun z => p z.1*iid p (Fin n) z.2*f (Fin.cons z.1 z.2))
    (fun x => iid p (Fin (n+1)) x*f x) (by
      intro z
      change _ = iid p (Fin (n+1)) (Fin.cons z.1 z.2)*f (Fin.cons z.1 z.2)
      rw [iid_cons])
  simpa only [Fintype.sum_prod_type] using h.symm

lemma first_integrand (p : Law α) (E : Finset α) (n : ℕ) (y : Option α)
  (a : α) (x : Fin n → α) :
    p a*iid p (Fin n) x*(if firstAccepted E (Fin.cons a x)=y then 1 else 0) =
    (if a∈E ∧ some a=y then p a else 0)*iid p (Fin n) x+
    (if a∈E then 0 else p a)*
      (if firstAccepted E x=y then iid p (Fin n) x else 0) := by
  rw [firstAccepted_cons]
  by_cases ha : a∈E
  · by_cases hy : some a=y <;> simp [ha,hy]
  · by_cases hy : firstAccepted E x=y <;> simp [ha,hy]

lemma first_law_succ (p : Law α) (E : Finset α) (n : ℕ) (y : Option α) :
    map (iid p (Fin (n+1))) (firstAccepted E (n := n+1)) y =
      (∑ a,if a∈E ∧ some a=y then p a else 0)+
      (1-eventMass p E)*map (iid p (Fin n)) (firstAccepted E (n := n)) y := by
  have h := sum_iid_succ p n (fun x => if firstAccepted E x=y then 1 else 0)
  calc
    _ = ∑ x,iid p (Fin (n+1)) x*(if firstAccepted E x=y then 1 else 0) := by
      simp only [map,mul_ite,mul_one,mul_zero]
      congr 2
      funext x
      congr 1
    _ = ∑ a,∑ x,p a*iid p (Fin n) x*
        (if firstAccepted E (Fin.cons a x)=y then 1 else 0) := h
    _ = _ := by
      simp only [first_integrand,Finset.sum_add_distrib,←Finset.mul_sum,(iid p (Fin n)).sum_one,
        mul_one,←Finset.sum_mul,rejection_mass,map]
      congr 3
      funext x
      congr 1

lemma first_law_zero_none (p : Law α) (E : Finset α) :
    map (iid p (Fin 0)) (firstAccepted E (n := 0)) none=1 := by
  simp [map,firstAccepted,iid]

lemma first_law_none (p : Law α) (E : Finset α) (n : ℕ) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) none=(1-eventMass p E)^n := by
  induction n with
  | zero => simpa using first_law_zero_none p E
  | succ n hn =>
    rw [first_law_succ,hn,pow_succ]
    simp only [Option.some_ne_none,and_false,ite_false,Finset.sum_const_zero,zero_add]
    ring

end SharpRamseyFive.FiniteEntropy

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

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FiniteGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {S A : Type*}

lemma growthFailures_cons (step : S→A→S) (rank : S→ℕ) (d : ℕ) (s : S)
    {n : ℕ} (a : A) (x : Fin n→A) :
    growthFailures step rank d s (Fin.cons a x)=
      (if failedGrowth step rank d s a then 1 else 0)+growthFailures step rank d (step s a) x := by
  simp only [growthFailures,Fin.cons_zero,Fin.cons_succ]

lemma runSamples_rank_mono (step : S→A→S) (rank : S→ℕ)
    (hmono : ∀ s a,rank s ≤ rank (step s a)) (s : S) {n : ℕ} (x : Fin n→A) :
    rank s ≤ rank (runSamples step s x) := by
  induction n generalizing s with
  | zero=>exact le_rfl
  | succ n ih=>exact (hmono _ _).trans (ih _ _)

lemma zero_growthFailures (step : S→A→S) (rank : S→ℕ) (d : ℕ)
    (hmono : ∀ s a,rank s ≤ rank (step s a)) (s : S) {n : ℕ} (x : Fin n→A)
    (h : growthFailures step rank d s x=0) :
    min d (rank s+n) ≤ rank (runSamples step s x) := by
  induction n generalizing s with
  | zero=>simpa only [Nat.add_zero,runSamples] using Nat.min_le_right d (rank s)
  | succ n ih=>
    have hn : ¬failedGrowth step rank d s (x 0) := by
      intro hn
      simp only [growthFailures,hn,ite_true] at h
      omega
    have ht : growthFailures step rank d (step s (x 0)) (fun i=>x i.succ)=0 := by
      simpa only [growthFailures,hn,ite_false,Nat.zero_add] using h
    have hh:=ih (step s (x 0)) (fun i=>x i.succ) ht
    have hm:=hmono s (x 0)
    have hm':=runSamples_rank_mono step rank hmono (step s (x 0)) (fun i=>x i.succ)
    change min d (rank s+(n+1)) ≤ rank (runSamples step (step s (x 0)) (fun i=>x i.succ))
    unfold failedGrowth at hn
    omega

variable [Fintype A]

theorem growthFailures_mean (p : Law A) (step : S→A→S) (rank : S→ℕ) (d : ℕ)
    (e : ℝ) (hstep : ∀ s,eventWeight p (failedGrowth step rank d s)≤e)
    (s : S) (n : ℕ) :
    (∑ x,iid p (Fin n) x*(growthFailures step rank d s x:ℝ))≤n*e := by
  induction n generalizing s with
  | zero=>simp [growthFailures]
  | succ n ih=>
    rw [sum_iid_succ]
    have he : (∑ a,∑ x,p a*iid p (Fin n) x*
        (growthFailures step rank d s (Fin.cons a x):ℝ))=
        eventWeight p (failedGrowth step rank d s)+
        ∑ a,p a*(∑ x,iid p (Fin n) x*(growthFailures step rank d (step s a) x:ℝ)) := by
      simp only [growthFailures_cons,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
        mul_add,Finset.sum_add_distrib,eventWeight]
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        rw [←Finset.sum_mul,←Finset.mul_sum,(iid p (Fin n)).sum_one,mul_one]
        simp only [mul_ite,mul_one,mul_zero]
      · apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
    rw [he]
    calc
      _ ≤ e+∑ a,p a*(n*e) := add_le_add (hstep s)
        (Finset.sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (ih _) (p.nonneg a))
      _ = _ := by rw [←Finset.sum_mul,p.sum_one]; push_cast; ring

theorem iid_growth_failure (p : Law A) (step : S→A→S) (rank : S→ℕ) (d : ℕ)
    (hmono : ∀ s a,rank s ≤ rank (step s a)) (e : ℝ)
    (hstep : ∀ s,eventWeight p (failedGrowth step rank d s)≤e)
    (s : S) (n : ℕ) (hstart : d ≤ rank s+n) :
    eventWeight (iid p (Fin n)) (fun x=>rank (runSamples step s x)<d)≤n*e := by
  apply le_trans _ (growthFailures_mean p step rank d e hstep s n)
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · have hp : 0<growthFailures step rank d s x := by
      by_contra hh
      have hz : growthFailures step rank d s x=0 := by omega
      have hb:=zero_growthFailures step rank d hmono s x hz
      omega
    exact le_mul_of_one_le_right ((iid p (Fin n)).nonneg x) (by exact_mod_cast hp)
  · exact mul_nonneg ((iid p (Fin n)).nonneg x) (Nat.cast_nonneg _)
end

noncomputable section
variable {A : Type*}

lemma firstAccepted_none_iff (E : Finset A) {n : ℕ} (x : Fin n→A) :
    firstAccepted E x=none ↔ ∀ i,x i∉E := by
  induction n with
  | zero=>simp [firstAccepted]
  | succ n ih=>
    rw [firstAccepted]
    split_ifs with h
    · simp only [false_iff,not_forall]
      exact ⟨0,by simpa using h⟩
    · rw [ih]
      constructor
      · intro hh i
        refine Fin.cases ?_ (fun j=>hh j) i
        exact h
      · intro hh i
        exact hh i.succ

variable [Fintype A]

lemma iid_avoidance (p : Law A) (E : Finset A) (n : ℕ) :
    eventWeight (iid p (Fin n)) (fun x=>∀ i,x i∉E)=(1-eventMass p E)^n := by
  rw [←first_law_none p E n]
  unfold eventWeight map
  apply Finset.sum_congr rfl
  intro x _
  rw [firstAccepted_none_iff]

lemma eventWeight_mono (p : Law A) (P Q : A→Prop) (h : ∀ a,P a→Q a) :
    eventWeight p P≤eventWeight p Q := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a
  · simp only [hp,h a hp,ite_true,le_refl]
  · simp only [hp,ite_false]
    split_ifs <;> first | exact p.nonneg a | exact le_rfl

lemma eventWeight_union (p : Law A) (P Q : A→Prop) :
    eventWeight p (fun a=>P a ∨ Q a)≤eventWeight p P+eventWeight p Q := by
  unfold eventWeight
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;>
    simp only [hp,hq,true_or,false_or,or_false,ite_true,ite_false,zero_add,add_zero,le_refl]
  exact le_add_of_nonneg_right (p.nonneg a)
end
end SharpRamseyFive.FiniteEntropy

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighPairVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma le_growSpan {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) : W≤growSpan y W x := le_sup_left

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma hit_le_growSpan {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) (i : Fin n) (hi : Incident (x i).1 y) :
    (x i).2.submodule≤growSpan y W x := by
  apply le_trans _ le_sup_right
  unfold Marking.state
  exact le_iSup_of_le i (le_iSup_of_le (Finset.mem_univ i) (by rw [ite_eq_left hi]))

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma rank_growSpan_mono {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) : finrank K W≤finrank K (growSpan y W x) :=
  Submodule.finrank_mono (le_growSpan y W x)

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma growSpan_eq_of_rank_le {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) (hr : finrank K (growSpan y W x)≤finrank K W) :
    growSpan y W x=W := by
  exact (Submodule.eq_of_le_of_finrank_eq (le_growSpan y W x)
    (Nat.le_antisymm (rank_growSpan_mono y W x) hr)).symm

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma small_subspace_card (W : Submodule K (Dual K V)) (hr : finrank K W<4) :
    ((Finset.univ.filter fun b : ℙ K (Dual K V)=>b.submodule≤W).card:ℝ)≤
      2*(Nat.card K:ℝ)^2 := by
  rw [Marking.subspace_finset_card,Nat.cast_sum]
  simp only [Nat.cast_pow]
  have hle : (∑ i∈Finset.range (finrank K W),(Nat.card K:ℝ)^i)≤
      ∑ i∈Finset.range 3,(Nat.card K:ℝ)^i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro i _ _
    positivity
  apply hle.trans
  have hq : 2≤(Nat.card K:ℝ) := by exact_mod_cast Finite.one_lt_card (α:=K)
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,zero_add]
  nlinarith

omit [Finite K] [FiniteDimensional K V] in
lemma first_incident_mass (p : Law (SampleFlag (K:=K) (V:=V))) (y : ℙ K (Dual K V)) :
    eventMass p (Finset.univ.filter fun z=>Incident z.1 y)=weightOnHyperplane (first p) y := by
  simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,
    weightOnHyperplane,incidenceEntry,first]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · simp only [one_mul]
  · simp only [Finset.sum_const_zero,zero_mul]

omit [FiniteDimensional K V] in
lemma second_subspace_mass (p : Law (SampleFlag (K:=K) (V:=V)))
    (W : Submodule K (Dual K V)) (B : ℝ) (hr : finrank K W<4) (hB : 0≤B)
    (hp : ∀ b,second p b≤B) :
    eventMass p (Finset.univ.filter fun z=>z.2.submodule≤W)≤2*(Nat.card K:ℝ)^2*B := by
  have he : eventMass p (Finset.univ.filter fun z=>z.2.submodule≤W)=
      ∑ b∈Finset.univ.filter (fun b=>b.submodule≤W),second p b := by
    simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,second]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp only [Finset.sum_const_zero]
  rw [he]
  calc
    _ ≤ ∑ _b∈Finset.univ.filter (fun b : ℙ K (Dual K V)=>b.submodule≤W),B :=
      Finset.sum_le_sum fun b _=>hp b
    _ = ((Finset.univ.filter fun b : ℙ K (Dual K V)=>b.submodule≤W).card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (small_subspace_card W hr) hB

omit [FiniteDimensional K V] in
theorem newHits_mass (p : Law (SampleFlag (K:=K) (V:=V)))
    (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V)) (B : ℝ)
    (hr : finrank K W<4) (hB : 0≤B) (hp : ∀ b,second p b≤B)
    (hy : y∉lowHits (first p)) (hsmall : 2*(Nat.card K:ℝ)^2*B≤1/(20*(Nat.card K:ℝ))) :
    1/(5*(Nat.card K:ℝ))≤eventMass p (newHits y W) := by
  have hhit : 1/(4*(Nat.card K:ℝ))≤weightOnHyperplane (first p) y := by
    exact le_of_not_gt fun h=>hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hsub := second_subspace_mass p W B hr hB hp
  have hpart : eventMass p (Finset.univ.filter fun z=>Incident z.1 y)≤
      eventMass p (newHits y W)+eventMass p (Finset.univ.filter fun z=>z.2.submodule≤W) := by
    simp only [eventMass,newHits,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    by_cases hh : Incident z.1 y <;> by_cases hw : z.2.submodule≤W <;>
      simp only [hh,hw,not_true_eq_false,not_false_eq_true,and_self,and_false,
        and_true,ite_true,ite_false,zero_add,add_zero,le_refl]
    exact p.nonneg z
  rw [first_incident_mass] at hpart
  have he : 1/(4*(Nat.card K:ℝ))-1/(20*(Nat.card K:ℝ))=1/(5*(Nat.card K:ℝ)) := by ring
  linarith
end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighSampleGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] in
lemma nongrowth_avoids {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) (hr : finrank K (growSpan y W x)≤finrank K W) :
    ∀ i,x i∉newHits y W := by
  intro i hi
  obtain ⟨hi,hn⟩:=(Finset.mem_filter.mp hi).2
  apply hn
  rw [←growSpan_eq_of_rank_le y W x hr]
  exact hit_le_growSpan y W x i hi

lemma block_growth_failure (p : Law (SampleFlag (K:=K) (V:=V)))
    (y : ℙ K (Dual K V)) (B : ℝ) (hB : 0≤B) (hp : ∀ b,second p b≤B)
    (hy : y∉lowHits (first p)) (hsmall : 2*(Nat.card K:ℝ)^2*B≤1/(20*(Nat.card K:ℝ)))
    (n : ℕ) (W : Submodule K (Dual K V)) :
    eventWeight (iid p (Fin n)) (failedGrowth (growSpan (n:=n) y) (fun W : Submodule K (Dual K V)=>finrank K W) 4 W)≤
      (1-1/(5*(Nat.card K:ℝ)))^n := by
  have hq : 2≤(Nat.card K:ℝ) := by exact_mod_cast Finite.one_lt_card (α:=K)
  have hc : 0≤1-1/(5*(Nat.card K:ℝ)) := by
    have hh : 1/(5*(Nat.card K:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  by_cases hr : finrank K W<4
  · calc
      _ ≤ eventWeight (iid p (Fin n)) (fun x=>∀ i,x i∉newHits y W) :=
        eventWeight_mono _ _ _ (fun x hx=>nongrowth_avoids y W x hx.2)
      _ = (1-eventMass p (newHits y W))^n := iid_avoidance p _ n
      _ ≤ _ := pow_le_pow_left₀ (sub_nonneg.mpr (eventMass_le_one p _))
        (by linarith [newHits_mass p y W B hr hB hp hy hsmall]) n
  · have he : eventWeight (iid p (Fin n))
        (failedGrowth (growSpan (n:=n) y) (fun W : Submodule K (Dual K V)=>finrank K W) 4 W)=0 := by
      simp only [eventWeight,failedGrowth,hr,false_and,ite_false,Finset.sum_const_zero]
    rw [he]
    exact pow_nonneg hc _

theorem sampled_span_rank_failure (p : Law (SampleFlag (K:=K) (V:=V)))
    (y : ℙ K (Dual K V)) (B : ℝ) (hB : 0≤B) (hp : ∀ b,second p b≤B)
    (hy : y∉lowHits (first p)) (hsmall : 2*(Nat.card K:ℝ)^2*B≤1/(20*(Nat.card K:ℝ)))
    (n : ℕ) :
    eventWeight (iid (iid p (Fin n)) (Fin 3))
      (fun x=>finrank K (sampleSpan x y)<4)≤3*(1-1/(5*(Nat.card K:ℝ)))^n := by
  exact iid_growth_failure (iid p (Fin n)) (growSpan y) (fun W : Submodule K (Dual K V)=>finrank K W) 4
    (fun W x=>rank_growSpan_mono y W x) _
    (fun W=>block_growth_failure p y B hB hp hy hsmall n W) y.submodule 3
    (by rw [y.finrank_submodule])
end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_HighSampleDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma growSpan_le {n : ℕ} (y : ℙ K (Dual K V))
    (W U : Submodule K (Dual K V)) (x : Fin n→SampleFlag (K:=K) (V:=V))
    (hW : W≤U) (hx : ∀ i,Incident (x i).1 y → (x i).2.submodule≤U) :
    growSpan y W x≤U := by
  apply sup_le hW
  unfold Marking.state
  apply iSup₂_le
  intro i _
  split_ifs with hi
  · exact hx i hi
  · exact bot_le

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma runSpan_le {n t : ℕ} (y : ℙ K (Dual K V))
    (W U : Submodule K (Dual K V)) (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V))
    (hW : W≤U) (hx : ∀ j i,Incident (x j i).1 y → (x j i).2.submodule≤U) :
    runSamples (growSpan y) W x≤U := by
  induction t generalizing W with
  | zero=>exact hW
  | succ t ih=>
    exact ih (growSpan y W (x 0)) (fun j=>x j.succ)
      (growSpan_le y W U (x 0) hW (hx 0)) (fun j=>hx j.succ)

omit [Finite K] [FiniteDimensional K V] in
theorem mem_highDomain {n t : ℕ} (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V))
    (z : SampleFlag (K:=K) (V:=V)) (hz : Incident z.1 z.2)
    (hr : 4≤finrank K (sampleSpan x z.2))
    (hc : ∀ j i,Incident (x j i).1 z.2 → Incident z.1 (x j i).2) :
    z∈highDomain x := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr,?_⟩
  rw [←Submodule.le_dualAnnihilator_iff_le_dualCoannihilator]
  apply runSpan_le z.2 z.2.submodule z.1.submodule.dualAnnihilator x
    ((incident_iff_dualAnnihilator _ _).mp hz)
  intro j i hi
  exact (incident_iff_dualAnnihilator _ _).mp (hc j i hi)
end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FinitePiLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι→Type*} [∀i,Fintype (β i)]

lemma piLaw_prod (p : ∀i,Law (β i)) (f : ∀i,β i→ℝ) :
    (∑x,piLaw p x*(∏i,f i (x i)))=∏i,∑a,p i a*f i a := by
  simp only [piLaw,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a=>p i a*f i a)).symm

lemma piLaw_eval_expectation (p : ∀i,Law (β i)) (i : ι) (f : β i→ℝ) :
    (∑x,piLaw p x*f (x i))=∑a,p i a*f a := by
  let g : ∀j,β j→ℝ := fun j a=>if h : j=i then f (h ▸ a) else 1
  have hx (x : ∀j,β j) : (∏j,g j (x j))=f (x i) := by
    have he : (fun j=>g j (x j))=Function.update (fun _=>1) i (f (x i)) := by
      funext j
      by_cases hj : j=i
      · subst j;simp [g]
      · simp [g,hj]
    rw [he,Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hs : (fun j=>∑a,p j a*g j a)=Function.update (fun _=>1) i (∑a,p i a*f a) := by
    funext j
    by_cases hj : j=i
    · subst j;simp [g]
    · simp [g,hj,(p j).sum_one]
  have hh := piLaw_prod p g
  simp_rw [hx] at hh
  rw [hs,Finset.prod_update_of_mem (Finset.mem_univ i)] at hh
  simpa using hh

end

open scoped BigOperators Classical

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LogSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

theorem log_sum (f g : α → ℝ) (hf : ∀ a,0≤f a) (hg : ∀ a,0≤g a)
    (hac : ∀ a,0<f a → 0<g a) :
    (∑ a,f a)*Real.log ((∑ a,f a)/(∑ a,g a)) ≤ ∑ a,f a*Real.log (f a/g a) := by
  let F := ∑ a,f a
  let G := ∑ a,g a
  have hF0 : 0≤F := Finset.sum_nonneg fun a _ => hf a
  by_cases hFz : F=0
  · have hzero (a : α) : f a=0 := by
      have hle : f a≤F := Finset.single_le_sum (fun b _ => hf b) (Finset.mem_univ a)
      exact le_antisymm (hle.trans_eq hFz) (hf a)
    simp only [hzero,Finset.sum_const_zero,zero_mul]
    exact le_rfl
  have hF : 0<F := lt_of_le_of_ne hF0 (Ne.symm hFz)
  have hG : 0<G := by
    have hex : ∃ a,0<f a := by
      by_contra! hn
      have hnon : F≤0 := Finset.sum_nonpos fun a _ => hn a
      exact (not_le_of_gt hF) hnon
    obtain ⟨a,ha⟩ := hex
    exact (hac a ha).trans_le (Finset.single_le_sum (fun b _ => hg b) (Finset.mem_univ a))
  let p : Law α :=
    { mass := fun a => f a/F
      nonneg := fun a => div_nonneg (hf a) hF.le
      sum_one := by rw [←Finset.sum_div]; exact div_self hFz }
  let q : Law α :=
    { mass := fun a => g a/G
      nonneg := fun a => div_nonneg (hg a) hG.le
      sum_one := by rw [←Finset.sum_div]; exact div_self (ne_of_gt hG) }
  have hD : 0≤divergence p q := by
    apply divergence_nonneg p q
    intro a ha
    exact div_pos (hac a ((div_pos_iff_of_pos_right hF).mp ha)) hG
  have he (a : α) : f a*Real.log (f a/g a) =
      f a*Real.log (F/G)+F*(p a*Real.log (p a/q a)) := by
    by_cases hz : f a=0
    · simp [p,hz]
    · have hfp : 0<f a := lt_of_le_of_ne (hf a) (Ne.symm hz)
      have hgp := hac a hfp
      dsimp [p,q]
      rw [Real.log_div hz (ne_of_gt hgp),Real.log_div hFz (ne_of_gt hG),
        Real.log_div (ne_of_gt (div_pos hfp hF)) (ne_of_gt (div_pos hgp hG)),
        Real.log_div hz hFz,Real.log_div (ne_of_gt hgp) (ne_of_gt hG)]
      field_simp
      ring
  calc
    _ ≤ F*Real.log (F/G)+F*divergence p q := le_add_of_nonneg_right (mul_nonneg hF.le hD)
    _ = _ := by
      simp only [he,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,divergence,F]

theorem divergence_map_le (p q : Law α) (hac : ∀ a,0<p a → 0<q a) (f : α → β) :
    divergence (map p f) (map q f) ≤ divergence p q := by
  have hpoint (b : β) := log_sum
    (fun a => if f a=b then p a else 0)
    (fun a => if f a=b then q a else 0)
    (fun a => by split_ifs; exact p.nonneg a; exact le_rfl)
    (fun a => by split_ifs; exact q.nonneg a; exact le_rfl)
    (fun a ha => by
      split_ifs at ha ⊢ with h
      · exact hac a ha
      · exact (lt_irrefl _ ha).elim)
  have hs := Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => hpoint b)
  change divergence (map p f) (map q f) ≤ _ at hs
  apply hs.trans_eq
  rw [Finset.sum_comm]
  unfold divergence
  apply Finset.sum_congr rfl
  intro a _
  have hterm (b : β) : (if f a=b then p a else 0)*Real.log
      ((if f a=b then p a else 0)/(if f a=b then q a else 0)) =
      if f a=b then p a*Real.log (p a/q a) else 0 := by
    split_ifs <;> simp
  simp only [hterm]
  classical
  simp

lemma map_product {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law α) (q : Law β) (f : α → γ) (g : β → δ) :
    map (product p q) (fun z => (f z.1,g z.2)) = product (map p f) (map q g) := by
  apply Law.ext
  funext z
  simp only [map,product,Fintype.sum_prod_type]
  have he (a : α) (b : β) :
      (if (f a,g b)=z then p a*q b else 0) =
        (if f a=z.1 then p a else 0)*(if g b=z.2 then q b else 0) := by
    rcases z with ⟨c,d⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [he,←Finset.mul_sum,←Finset.sum_mul]

theorem mutual_information_map_le {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    entropy (map (first p) f)+entropy (map (second p) g)-
      entropy (map p (fun z => (f z.1,g z.2))) ≤
    entropy (first p)+entropy (second p)-entropy p := by
  have h := divergence_map_le p (product (first p) (second p)) (ac_product p)
    (fun z => (f z.1,g z.2))
  rw [map_product] at h
  have h1 : first (map p (fun z => (f z.1,g z.2)))=map (first p) f := by
    change first (pair p (f ∘ Prod.fst) (g ∘ Prod.snd))=_
    rw [first_pair,←map_comp,map_first]
  have h2 : second (map p (fun z => (f z.1,g z.2)))=map (second p) g := by
    change second (pair p (f ∘ Prod.fst) (g ∘ Prod.snd))=_
    rw [second_pair,←map_comp,map_second]
  rw [←h1,←h2,mutual_information,mutual_information] at h
  rw [h1,h2] at h
  exact h

end

open scoped BigOperators Classical
variable {α β γ ι : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

lemma information_conditional (p : Law (α × β)) :
    information p = entropy (second p)-∑ a,first p a*entropy (fiber p a) := by
  dsimp [information]
  rw [entropy_chain]
  ring

theorem total_correlation_drop (p : Law (α × (ι → β))) :
    (entropy (first p)+(∑ i,entropy (map (second p) (fun x => x i)))-entropy p)-
      (∑ a,first p a*totalCorrelation (fiber p a)) =
      ∑ i,information (mapSnd p (fun x => x i)) := by
  have hI (i : ι) : information (mapSnd p (fun x => x i)) =
      entropy (map (second p) (fun x => x i))-
      ∑ a,first p a*entropy (map (fiber p a) (fun x => x i)) := by
    rw [information_conditional,second_mapSnd,first_mapSnd]
    simp only [fiber_mapSnd]
  simp only [hI,totalCorrelation,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a i => first p a*entropy (map (fiber p a) (fun x => x i)))]
  rw [entropy_chain]
  ring

lemma information_observation_le (p : Law (α × β)) (f : α → γ) :
    information (map p (fun z => (f z.1,z.2))) ≤ information p := by
  have hh := mutual_information_map_le p f id
  have h1 : first (map p (fun z => (f z.1,z.2)))=map (first p) f := by
    change first (pair p (f ∘ Prod.fst) (id ∘ Prod.snd))=_
    rw [first_pair]
    rw [←map_comp,map_first]
  have h2 : second (map p (fun z => (f z.1,z.2)))=second p := by
    change second (pair p (f ∘ Prod.fst) Prod.snd)=_
    rw [second_pair,map_second]
  simpa only [information,h1,h2,map_id,id_eq] using hh

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SplitLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {ι β : Type*} [Fintype ι] [Fintype β]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSubtypeMemFinset_solutions
lemma first_reveal (p : Law (ι → β)) (E : Finset ι) :
    first (reveal p E) = map p (fun x (i : E) => x i.val) := first_pair _ _ _

lemma entropy_reveal (p : Law (ι → β)) (E : Finset ι) :
    entropy (reveal p E) = entropy p := by
  apply entropy_map_injective
  intro x y he
  exact congrArg Prod.snd he

lemma information_reveal_selected (p : Law (ι → β)) (E : Finset ι) (i : ι) (hi : i∈E) :
    information (mapSnd (reveal p E) (fun x => x i)) = entropy (map p (fun x => x i)) := by
  let e : E := ⟨i,hi⟩
  have he : mapSnd (reveal p E) (fun x => x i)=
      map (first (reveal p E)) (fun y => (y,y e)) := by
    rw [first_reveal]
    simp only [reveal,mapSnd,pair,map_comp,Function.comp_def,id_eq]
    rfl
  have hH : entropy (mapSnd (reveal p E) (fun x => x i))=
      entropy (first (reveal p E)) := by
    rw [he]
    apply entropy_map_injective
    intro x y h
    exact congrArg Prod.fst h
  simp only [information,first_mapSnd,second_mapSnd,second_reveal,hH]
  ring

lemma entropy_reveal_le_coordinate_sum (p : Law (ι → β)) (E : Finset ι) :
    entropy (first (reveal p E)) ≤ ∑ i∈E,entropy (map p (fun x => x i)) := by
  have hh := totalCorrelation_nonneg (first (reveal p E))
  simp only [totalCorrelation,first_reveal,map_comp,Function.comp_def] at hh
  rw [Finset.sum_coe_sort E (fun i : ι => entropy (map p (fun x => x i)))] at hh
  simpa only [first_reveal] using (sub_nonneg.mp hh)

theorem reveal_information_budget (p : Law (ι → β)) (E : Finset ι) :
    (∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i)))+
      (∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a)) ≤
        totalCorrelation p := by
  have hh := total_correlation_drop (reveal p E)
  simp only [second_reveal,entropy_reveal] at hh
  have hb := entropy_reveal_le_coordinate_sum p E
  have hs := Finset.sum_add_sum_compl E
    (fun i => information (mapSnd (reveal p E) (fun x => x i)))
  have hsel : (∑ i∈E,information (mapSnd (reveal p E) (fun x => x i)))=
      ∑ i∈E,entropy (map p (fun x => x i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact information_reveal_selected p E i hi
  rw [hsel] at hs
  change (∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i)))+
      (∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a)) ≤
        (∑ i,entropy (map p (fun x => x i)))-entropy p
  linarith

theorem reveal_coordinate_information_le (p : Law (ι → β)) (E : Finset ι)
    (j : E) (i : ι) :
    information (pair p (fun x => x j.val) (fun x => x i)) ≤
      information (mapSnd (reveal p E) (fun x => x i)) := by
  have hh := information_observation_le (mapSnd (reveal p E) (fun x => x i))
    (fun y => y j)
  simpa only [reveal,mapSnd,pair,map_comp,Function.comp_def,id_eq] using hh

end

open scoped BigOperators Classical

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
noncomputable local instance instDecidableEqSubtypeSumProdMemFinset_solutions_r3e54ef_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
omit [Fintype A] [Fintype T] in
lemma mem_representativeSet_left (s : B → A) (b : B) (a : A) :
    Sum.inl (b,a) ∈ representativeSet (T := T) s ↔ a=s b := by
  simp [representativeSet,eq_comm]

omit [Fintype A] [Fintype T] in
lemma not_mem_representativeSet_right (s : B → A) (t : T) :
    Sum.inr t ∉ representativeSet s := by simp [representativeSet]

lemma blockInformation_own_independent (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a i : A) :
    blockInformation p (Function.update s b a) b i=blockInformation p s b i := by
  apply Finset.sup_congr rfl
  intro c hc
  rw [Function.update_of_ne (Finset.mem_erase.mp hc).1]

lemma blockInformation_le_reveal (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a : A) :
    (blockInformation p s b a:ℝ) ≤ information
      (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inl (b,a)))) := by
  let z : ℝ≥0 := ⟨information (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inl (b,a)))),information_nonneg _⟩
  change (blockInformation p s b a:ℝ) ≤ (z:ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro c _
  exact reveal_coordinate_information_le p (representativeSet s)
    ⟨Sum.inl (c,s c),(mem_representativeSet_left s c (s c)).mpr rfl⟩ (Sum.inl (b,a))

lemma middleInformation_le_reveal (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (t : T) :
    (middleInformation p s t:ℝ) ≤ information
      (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inr t))) := by
  let z : ℝ≥0 := ⟨information (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inr t))),information_nonneg _⟩
  change (middleInformation p s t:ℝ) ≤ (z:ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro c _
  exact reveal_coordinate_information_le p (representativeSet s)
    ⟨Sum.inl (c,s c),(mem_representativeSet_left s c (s c)).mpr rfl⟩ (Sum.inr t)

theorem representative_unselected_le_cost (p : Law (((B × A) ⊕ T) → β)) (s : B → A) :
    (∑ b,∑ a∈Finset.univ.erase (s b),(blockInformation p s b a:ℝ))+
      (∑ t,(middleInformation p s t:ℝ)) ≤ revealCost p (representativeSet s) := by
  classical
  let f : ((B × A) ⊕ T) → ℝ := fun i =>
    information (mapSnd (reveal p (representativeSet s)) (fun x => x i))
  have he : revealCost p (representativeSet s)=
      (∑ b,∑ a∈Finset.univ.erase (s b),f (Sum.inl (b,a)))+∑ t,f (Sum.inr t) := by
    unfold revealCost
    change (∑ i∈(representativeSet s)ᶜ,f i)=_
    have hfilt : (representativeSet (T := T) s)ᶜ=Finset.univ.filter (fun i => i∉representativeSet s) := by ext i; simp
    rw [hfilt,Finset.sum_filter,Fintype.sum_sum_type]
    simp only [mem_representativeSet_left,not_mem_representativeSet_right,
      not_false_eq_true,ite_true,Fintype.sum_prod_type]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [←Finset.sum_filter]
    rw [Finset.filter_ne']
  rw [he]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    exact blockInformation_le_reveal p s b a
  · exact Finset.sum_le_sum fun t _ => middleInformation_le_reveal p s t

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
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_1_r3e54ef_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
lemma uniformOn_expectation (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    (∑ a, uniformOn S hS a * f a) = (S.card : ℝ)⁻¹ * ∑ a ∈ S, f a := by
  simp only [uniformOn]
  calc
    _ = ∑ a, if a ∈ S then (S.card : ℝ)⁻¹ * f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by rw [←Finset.sum_filter, Finset.filter_univ_mem, Finset.mul_sum]

lemma piLaw_uniformOn_zero (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (s : B → A) {b : B} (h : s b ∉ S b) :
    piLaw (fun b => uniformOn (S b) (hS b)) s = 0 := by
  classical
  change (∏ b, uniformOn (S b) (hS b) (s b)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [uniformOn,h])

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

theorem unused_all_le_twice_unselected (S : B → Finset A)
    (hS : ∀ b, (S b).Nonempty) (hsize : ∀ b, 2 ≤ (S b).card)
    (f : (B → A) → B → A → ℝ) (hf : ∀ s b a, 0 ≤ f s b a)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * (∑ a ∈ S b, f s b a)) ≤
      2*(∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s *
        (∑ a ∈ (S b).erase (s b), f s b a)) := by
  classical
  let w := piLaw (fun b => uniformOn (S b) (hS b))
  have hi := unused_selected_identity S hS f hown b
  have hs : (∑ s, w s * (∑ a ∈ S b, f s b a)) =
      (∑ s, w s * f s b (s b)) +
      (∑ s, w s * (∑ a ∈ (S b).erase (s b), f s b a)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : s b ∈ S b
    · rw [←mul_add, Finset.add_sum_erase _ _ h]
    · have hz : w s = 0 := piLaw_uniformOn_zero S hS s h
      simp [hz]
  have hn : 0 ≤ ∑ s, w s * f s b (s b) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (w.nonneg s) (hf s b (s b))
  have hc : (2 : ℝ) ≤ (S b).card := by exact_mod_cast hsize b
  change (S b).card * (∑ s, w s * f s b (s b)) = _ at hi
  change (∑ s, w s * (∑ a ∈ S b, f s b a)) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hc hn]

theorem unused_information_le_twice_cost
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (hS : ∀ b, (S b).Nonempty) (hsize : ∀ b, 2 ≤ (S b).card) :
    (∑ s : B → A, piLaw (fun b => uniformOn (S b) (hS b)) s *
      ((∑ b : B, ∑ a ∈ S b, (blockInformation p s b a : ℝ)) +
        ∑ t : T, (middleInformation p s t : ℝ))) ≤
      2 * (∑ s : B → A, piLaw (fun b => uniformOn (S b) (hS b)) s *
        revealCost p (representativeSet s)) := by
  classical
  let w := piLaw (fun b => uniformOn (S b) (hS b))
  have hb := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset B)) =>
    unused_all_le_twice_unselected S hS hsize
      (fun s b a => (blockInformation p s b a : ℝ))
      (fun _ _ _ => NNReal.coe_nonneg _) (fun s b a i =>
        congrArg NNReal.toReal (blockInformation_own_independent p s b a i)) b)
  have hc (s : B → A) :
      (∑ b : B, ∑ a ∈ (S b).erase (s b), (blockInformation p s b a : ℝ)) +
      (∑ t : T, (middleInformation p s t : ℝ)) ≤ revealCost p (representativeSet s) := by
    apply le_trans _ (representative_unselected_le_cost p s)
    apply add_le_add _ le_rfl
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.erase_subset_erase (s b) (Finset.subset_univ _)
    · intro a _ _
      exact NNReal.coe_nonneg _
  have hh := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (B → A))) =>
    mul_le_mul_of_nonneg_left (hc s) (w.nonneg s))
  have hm : 0 ≤ ∑ s : B → A, w s * ∑ t : T, (middleInformation p s t : ℝ) := by
    exact Finset.sum_nonneg fun s _ => mul_nonneg (w.nonneg s)
      (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)
  have hb' :
      (∑ s : B → A, w s * (∑ b : B, ∑ a ∈ S b, (blockInformation p s b a : ℝ))) ≤
      2 * (∑ s : B → A, w s * (∑ b : B, ∑ a ∈ (S b).erase (s b),
        (blockInformation p s b a : ℝ))) := by
    calc
      _ = ∑ b : B, ∑ s : B → A, w s * (∑ a ∈ S b, (blockInformation p s b a : ℝ)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ b : B, 2 * (∑ s : B → A, w s * (∑ a ∈ (S b).erase (s b),
        (blockInformation p s b a : ℝ))) := hb
      _ = _ := by
        rw [←Finset.mul_sum]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
  change (∑ s : B → A, w s * _) ≤ 2 * (∑ s : B → A, w s * _)
  simp only [mul_add, Finset.sum_add_distrib] at hh ⊢
  linarith only [hb',hh,hm]

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
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_2_r3e54ef_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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

lemma blockAllInformation_mean_le (p : Law (((B × A) ⊕ T) → β))
    (S : B → Finset A) (hS : ∀ b, 2 ≤ (S b).card) :
    mean (freshBlockLaw S) (blockAllInformation p S) ≤
      2 * mean (freshBlockLaw S) (fun s => revealCost p (representativeSet s)) := by
  have hn : ∀ b, (S b).Nonempty := fun b => Finset.card_pos.mp (by have := hS b; omega)
  rw [freshBlockLaw_eq S hn]
  exact unused_information_le_twice_cost p S hn hS

omit [Nonempty A] in
lemma mean_reveal_budget (p : Law (((B × A) ⊕ T) → β)) (μ : Law (B → A)) :
    mean μ (fun s => revealCost p (representativeSet s)) +
      mean μ (fun s => mean (first (reveal p (representativeSet s)))
        (fun a => totalCorrelation (fiber (reveal p (representativeSet s)) a))) ≤
          totalCorrelation p := by
  rw [←mean_add]
  apply le_trans (mean_mono μ (fun s => reveal_information_budget p (representativeSet s)))
  exact (mean_const μ (totalCorrelation p)).le

theorem block_information_telescope
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (n : ℕ) (hS : ∀ b, n+1 ≤ (S b).card) :
    (∑ i : Fin n, blockRoundMean blockAllInformation p S n i) ≤ 2 * totalCorrelation p := by
  induction n generalizing p S with
  | zero => simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (totalCorrelation_nonneg p)
  | succ n ih =>
    have hsize : ∀ b, 2 ≤ (S b).card := fun b => by have := hS b; omega
    have hn (s : B → A) : ∀ b, n+1 ≤ (eraseBlock S s b).card :=
      eraseBlock_card S s (n+1) hS
    have hcost := blockAllInformation_mean_le p S hsize
    have hbudget := mean_reveal_budget p (freshBlockLaw S)
    simp only [blockRoundMean, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    have htail :
        (∑ i : Fin n, mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => blockRoundMean blockAllInformation (fiber (reveal p (representativeSet s)) a)
            (eraseBlock S s) n i))) ≤
        2 * mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => totalCorrelation (fiber (reveal p (representativeSet s)) a))) := by
      rw [←mean_sum]
      simp_rw [←mean_sum]
      calc
        _ ≤ mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => 2 * totalCorrelation (fiber (reveal p (representativeSet s)) a))) := by
            apply mean_mono
            intro s
            apply mean_mono
            intro a
            exact ih _ _ (hn s)
        _ = _ := by simp_rw [mean_smul]
    linarith only [htail,hcost,hbudget]

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
lemma fiber_reveal_agrees (p : Law (ι → β)) (E : Finset ι) (a : E → β)
    (ha : 0 < first (reveal p E) a) (x : ι → β)
    (hx : 0 < fiber (reveal p E) a x) : (fun i : E => x i.val) = a := by
  apply (reveal_positive p E a x _).2
  rw [mass_eq_first_mul_fiber]
  exact mul_pos ha hx

lemma InDomains.fiber {p : Law (ι → β)} {D : ι → Finset β} (h : InDomains p D)
    (E : Finset ι) (a : E → β) : InDomains (fiber (reveal p E) a) D := by
  intro x hx i
  exact h x (fiber_reveal_support p E a x hx) i

lemma FixedOutside.fiber {p : Law (ι → β)} {U : Finset ι} (h : FixedOutside p U)
    (E : Finset ι) (a : E → β) (ha : 0 < first (reveal p E) a) :
    FixedOutside (fiber (reveal p E) a) (U \ E) := by
  intro i hi
  by_cases he : i ∈ E
  · refine ⟨a ⟨i,he⟩,fun x hx => ?_⟩
    exact congrFun (fiber_reveal_agrees p E a ha x hx) ⟨i,he⟩
  · have hu : i ∉ U := fun hu => hi (Finset.mem_sdiff.mpr ⟨hu,he⟩)
    obtain ⟨b,hb⟩ := h i hu
    exact ⟨b,fun x hx => hb x (fiber_reveal_support p E a x hx)⟩

lemma marginalDeficit_le_active {p : Law (ι → β)} {U : Finset ι}
    (h : FixedOutside p U) (J : ℝ) : marginalDeficit p U J ≤ activeDeficit p U J := by
  have hh := h.entropy_le_sum
  simp only [marginalDeficit, activeDeficit, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

lemma activeDeficit_reveal (p : Law (ι → β)) (U E : Finset ι) (hEU : E ⊆ U)
    (J : ℝ) (hc : ∀ i ∈ E, entropy (map p (fun x => x i)) ≤ J) :
    mean (first (reveal p E)) (fun a => activeDeficit (fiber (reveal p E) a) (U \ E) J) ≤
      activeDeficit p U J := by
  have hcap : entropy (first (reveal p E)) ≤ (E.card : ℝ) * J := by
    apply (entropy_reveal_le_coordinate_sum p E).trans
    calc
      _ ≤ ∑ _i ∈ E,J := Finset.sum_le_sum hc
      _ = _ := by simp
  have hh := conditional_deficit_le (reveal p E) ((E.card : ℝ)*J) (((U \ E).card : ℝ)*J) hcap
  rw [entropy_reveal] at hh
  have hcard : ((E.card : ℝ) + (U \ E).card) = U.card := by
    simpa only [add_comm] using (show ((U \ E).card : ℝ) + E.card = U.card by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hEU)
  simpa only [activeDeficit, mean, ←add_mul, hcard] using hh
end

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions_3
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_3_r3e54ef_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
omit [Nonempty A] in
lemma mem_blockActive_left (S : B → Finset A) (b : B) (a : A) :
    Sum.inl (b,a) ∈ blockActive (T := T) S ↔ a ∈ S b := by simp [blockActive]
omit [Nonempty A] in
lemma mem_blockActive_right (S : B → Finset A) (t : T) :
    Sum.inr t ∈ blockActive S := by simp [blockActive]

lemma freshBlockLaw_supported (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (s : B → A) (hs : 0 < freshBlockLaw S s) : ∀ b, s b ∈ S b := by
  intro b
  by_contra h
  rw [freshBlockLaw_eq S hS,piLaw_uniformOn_zero S hS s h] at hs
  exact lt_irrefl _ hs

omit [Nonempty A] in
lemma representativeSet_subset_active (S : B → Finset A) (s : B → A)
    (hs : ∀ b, s b ∈ S b) : representativeSet (T := T) s ⊆ blockActive S := by
  intro i hi
  simp only [representativeSet, Finset.mem_image, Finset.mem_univ, true_and] at hi
  obtain ⟨b,rfl⟩ := hi
  exact (mem_blockActive_left S b (s b)).mpr (hs b)

omit [Nonempty A] in
lemma blockActive_erase (S : B → Finset A) (s : B → A) :
    blockActive (T := T) (eraseBlock S s) = blockActive S \ representativeSet s := by
  ext i
  cases i with
  | inl x => rcases x with ⟨b,a⟩; simp [blockActive,eraseBlock,representativeSet, and_comm, eq_comm]
  | inr t => simp [blockActive,representativeSet]

theorem block_round_deficit (J : ℝ) (D : ((B × A) ⊕ T) → Finset β)
    (hJ : ∀ i, Real.log (D i).card ≤ J)
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (hp : InDomains p D) (hfix : FixedOutside p (blockActive S))
    (n : ℕ) (hS : ∀ b, n ≤ (S b).card) (i : Fin n) :
    blockRoundMean (blockAllDeficit J) p S n i ≤ activeDeficit p (blockActive S) J := by
  induction n generalizing p S with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hn : ∀ b, (S b).Nonempty := fun b => Finset.card_pos.mp (by have := hS b; omega)
    cases i using Fin.cases with
    | zero =>
      change mean (freshBlockLaw S) (fun _ => marginalDeficit p (blockActive S) J) ≤ _
      rw [mean_const]
      exact marginalDeficit_le_active hfix J
    | succ i =>
      change mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
        (fun a => blockRoundMean (blockAllDeficit J) (fiber (reveal p (representativeSet s)) a)
          (eraseBlock S s) n i)) ≤ _
      apply le_trans (mean_mono_pos (freshBlockLaw S) (fun s hs => ?_))
        (mean_const (freshBlockLaw S) (activeDeficit p (blockActive S) J)).le
      have he : representativeSet (T := T) s ⊆ blockActive S :=
        representativeSet_subset_active S s (freshBlockLaw_supported S hn s hs)
      calc
        _ ≤ mean (first (reveal p (representativeSet s)))
          (fun a => activeDeficit (fiber (reveal p (representativeSet s)) a)
            (blockActive (eraseBlock S s)) J) := by
            apply mean_mono_pos
            intro a ha
            apply ih _ _ (hp.fiber _ _)
            · rw [blockActive_erase]
              exact hfix.fiber _ _ ha
            · exact eraseBlock_card S s n hS
        _ ≤ activeDeficit p (blockActive S) J := by
          rw [blockActive_erase]
          exact activeDeficit_reveal p (blockActive S) (representativeSet s) he J
            (fun j _ => hp.entropy_cap J hJ j)

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

local instance instDecidableEqSumProd_solutions_4_r3e54ef_1 : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_4_r3e54ef_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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

lemma fresh_row_collision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (hc : ∀ i j,0 ≤ c i j) (S : B → Finset A) (r : ℕ) (hr : 0 < r)
    (hS : ∀ b,r≤(S b).card) (i : ((B × A) ⊕ T)) :
    r * mean (freshBlockLaw S) (fun s => ∑ b,c i (Sum.inl (b,s b))) ≤
      ∑ j∈blockActive S,c i j := by
  have hn : ∀ b,(S b).Nonempty := fun b => Finset.card_pos.mp (hr.trans_le (hS b))
  rw [freshBlockLaw_eq S hn,mean_sum,Finset.mul_sum]
  have hb (b : B) : (r:ℝ)*mean (piLaw fun d => uniformOn (S d) (hn d))
      (fun s => c i (Sum.inl (b,s b))) ≤ ∑ a∈S b,c i (Sum.inl (b,a)) := by
    have he : mean (piLaw fun d => uniformOn (S d) (hn d))
        (fun s => c i (Sum.inl (b,s b))) =
        ((S b).card:ℝ)⁻¹ * ∑ a∈S b,c i (Sum.inl (b,a)) := by
      change (∑ s,piLaw (fun d => uniformOn (S d) (hn d)) s *
        (fun a => c i (Sum.inl (b,a))) (s b)) = _
      rw [piLaw_eval_expectation (fun d => uniformOn (S d) (hn d)) b
        (fun a => c i (Sum.inl (b,a))),uniformOn_expectation]
    have hnn := mean_nonneg (piLaw fun d=>uniformOn (S d) (hn d))
      (fun s=>c i (Sum.inl (b,s b))) (fun s=>hc _ _)
    have hcp : ((S b).card:ℝ)≠0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hn b))
    calc
      _ ≤ (S b).card*mean (piLaw fun d=>uniformOn (S d) (hn d))
          (fun s=>c i (Sum.inl (b,s b))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hS b) hnn
      _ = _ := by rw [he]; field_simp
  apply (Finset.sum_le_sum fun b _=>hb b).trans
  have he : (∑ j∈blockActive S,c i j)=
      (∑ b,∑ a∈S b,c i (Sum.inl (b,a)))+∑ t,c i (Sum.inr t) := by
    calc
      _ = ∑ j,if j∈blockActive S then c i j else 0 := by
        rw [Finset.sum_ite_mem,Finset.univ_inter]
      _ = _ := by
        rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
        simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
          Finset.sum_ite_mem,Finset.univ_inter]
  rw [he]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun t _=>hc _ _)

theorem fresh_all_collision_bound (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (hc : ∀ i j,0 ≤ c i j) (S : B → Finset A) (r : ℕ) (hr : 0 < r)
    (hS : ∀ b,r≤(S b).card) :
    r * mean (freshBlockLaw S) (allCollision c S) ≤
      ∑ i∈blockActive S,∑ j∈blockActive S,c i j := by
  have hpoint (s : B → A) : allCollision c S s ≤
      ∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b)) := by
    have he : (∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b)))=
        (∑ b,∑ a∈S b,∑ d,c (Sum.inl (b,a)) (Sum.inl (d,s d)))+
        ∑ t,middleCollision c s t := by
      calc
        _ = ∑ i,if i∈blockActive S then ∑ b,c i (Sum.inl (b,s b)) else 0 := by
          rw [Finset.sum_ite_mem,Finset.univ_inter]
        _ = _ := by
          rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
          simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
            Finset.sum_ite_mem,Finset.univ_inter,middleCollision]
    rw [he]
    change _ + _ ≤ _ + _
    apply add_le_add _ le_rfl
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun d _ _=>hc _ _)
  calc
    _ ≤ r * mean (freshBlockLaw S)
        (fun s=>∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b))) :=
      mul_le_mul_of_nonneg_left (mean_mono _ hpoint) (Nat.cast_nonneg _)
    _ = ∑ i∈blockActive S,r * mean (freshBlockLaw S)
        (fun s=>∑ b,c i (Sum.inl (b,s b))) := by rw [mean_finset_sum,Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => fresh_row_collision c hc S r hr hS i

end

open scoped Classical BigOperators

lemma badIndexIndicator_le {δ g d e : ℝ} (hδ : 0≤δ) (hg : 0≤g)
    (hd : 0<d) (he : 0<e) : badIndexIndicator δ g d e≤δ/d+g/e := by
  unfold badIndexIndicator
  split_ifs with h
  · rcases h with h|h
    · have hh : 1≤δ/d := (le_div_iff₀ hd).mpr (by linarith)
      exact hh.trans (le_add_of_nonneg_right (div_nonneg hg he.le))
    · have hh : 1≤g/e := (le_div_iff₀ he).mpr (by linarith)
      exact hh.trans (le_add_of_nonneg_left (div_nonneg hδ hd.le))
  · positivity

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

lemma mean_div {X : Type*} [Fintype X] (p : Law X) (f : X→ℝ) (d : ℝ) :
    mean p (fun x=>f x/d)=mean p f/d := by
  simp only [mean,mul_div_assoc,Finset.sum_div]

omit [Nonempty A] in
lemma indexInformation_sum (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexInformation p s i)=blockAllInformation p S s := by
  rw [blockActive_sum]
  rfl

omit [Nonempty A] in
lemma indexCollision_sum (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexCollision c s i)=allCollision c S s := by
  rw [blockActive_sum]
  rfl

omit [Nonempty A] in
lemma indexBad_sum (J d e : ℝ) (hd : 0<d) (he : 0<e)
    (p : Law (((B×A)⊕T)→β)) (hJ : ∀ i,entropy (map p (fun x=>x i))≤J)
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0 ≤ c i j)
    (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexBad J d e p c s i)≤
      blockAllDeficit J p S s/d+(blockAllInformation p S s+allCollision c S s)/e := by
  have hscore (i : ((B×A)⊕T)) : 0 ≤ indexInformation p s i+indexCollision c s i := by
    cases i with
    | inl z => exact add_nonneg (NNReal.coe_nonneg _) (Finset.sum_nonneg fun _ _=>hc _ _)
    | inr t => exact add_nonneg (NNReal.coe_nonneg _) (Finset.sum_nonneg fun _ _=>hc _ _)
  calc
    _ ≤ ∑ i∈blockActive S,((J-entropy (map p (fun x=>x i)))/d+
        (indexInformation p s i+indexCollision c s i)/e) :=
      Finset.sum_le_sum fun i _=>badIndexIndicator_le (sub_nonneg.mpr (hJ i)) (hscore i) hd he
    _ = _ := by
      rw [Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_div,Finset.sum_add_distrib,
        indexInformation_sum,indexCollision_sum]
      rfl

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

theorem fresh_bad_bound (J d e : ℝ) (hd : 0<d) (he : 0<e)
    (p : Law (((B×A)⊕T)→β)) (hJ : ∀ i,entropy (map p (fun x=>x i))≤J)
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0 ≤ c i j)
    (S : B→Finset A) (r : ℕ) (hr : 0 < r) (hS : ∀ b,r≤(S b).card) :
    mean (freshBlockLaw S) (fun s=>∑ i∈blockActive S,indexBad J d e p c s i)≤
      mean (freshBlockLaw S) (blockAllDeficit J p S)/d+
      (mean (freshBlockLaw S) (blockAllInformation p S)+
        (∑ i∈blockActive S,∑ j∈blockActive S,c i j)/r)/e := by
  have hb:=mean_mono (freshBlockLaw S) (indexBad_sum J d e hd he p hJ c hc S)
  simp_rw [mean_add,mean_div] at hb
  apply hb.trans
  rw [mean_add]
  gcongr
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  apply (le_div_iff₀ hr').mpr
  simpa only [mul_comm] using fresh_all_collision_bound c hc S r hr hS

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IndependentSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]

lemma eventWeight_mean (p : Law A) (P : A→Prop) :
    eventWeight p P=mean p (fun a=>if P a then 1 else 0) := by
  simp only [eventWeight,mean,mul_ite,mul_one,mul_zero]

lemma eventWeight_le_one (p : Law A) (P : A→Prop) : eventWeight p P≤1 := by
  rw [eventWeight_mean]
  calc
    _ ≤ mean p (fun _=>1) := mean_mono _ (fun a=>by split_ifs <;> norm_num)
    _ = 1 := mean_const p 1

lemma eventWeight_exists_le (p : Law A) (P : I→A→Prop) :
    eventWeight p (fun a=>∃ i,P i a)≤∑ i,eventWeight p (P i) := by
  simp_rw [eventWeight_mean]
  rw [←mean_sum]
  apply mean_mono
  intro a
  by_cases h : ∃ i,P i a
  · obtain ⟨i,hi⟩:=h
    rw [ite_eq_left ⟨i,hi⟩]
    calc
      (1:ℝ) = (if P i a then 1 else 0) := by rw [ite_eq_left hi]
      _ ≤ ∑ j,if P j a then 1 else 0 := Finset.single_le_sum (f:=fun j=>if P j a then (1:ℝ) else 0)
        (fun j _=>by split_ifs <;> norm_num) (Finset.mem_univ i)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg fun j _=>by split_ifs <;> norm_num

lemma iid_eval_mean [DecidableEq I] (p : Law A) (i : I) (f : A→ℝ) :
    mean (iid p I) (fun x=>f (x i))=mean p f := by
  exact piLaw_eval_expectation (fun _ : I=>p) i f

lemma iid_eval_event [DecidableEq I] (p : Law A) (i : I) (P : A→Prop) :
    eventWeight (iid p I) (fun x=>P (x i))=eventWeight p P := by
  simp_rw [eventWeight_mean]
  exact iid_eval_mean p i (fun a=>if P a then (1:ℝ) else 0)

lemma iid_exists_event [DecidableEq I] (p : Law A) (P : A→Prop) :
    eventWeight (iid p I) (fun x=>∃ i,P (x i))≤Fintype.card I*eventWeight p P := by
  apply (eventWeight_exists_le (iid p I) (fun (i:I) (x:I→A)=>P (x i))).trans
  simp only [iid_eval_event,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,le_refl]

lemma iid_nested_exists_event [DecidableEq I] [DecidableEq J]
    (p : Law A) (P : A→Prop) :
    eventWeight (iid (iid p I) J) (fun x=>∃ j i,P (x j i))≤
      Fintype.card J*(Fintype.card I*eventWeight p P) := by
  exact (iid_exists_event (iid p I) (fun x=>∃ i,P (x i))).trans
    (mul_le_mul_of_nonneg_left (iid_exists_event p P) (Nat.cast_nonneg _))
end

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FiniteKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.blockHistIndexDecEq
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.blockHistSubtypeDecEq
theorem history_round_mean
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ)
    (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n : ℕ) :
    blockRoundMean J p S (n+1) (Fin.last n)=
      mean (historyLaw p S n) (fun h=>mean (freshBlockLaw (historyUnused S h))
        (J (historyPosterior p h) (historyUnused S h))) := by
  induction n generalizing p S with
  | zero =>
    change mean (freshBlockLaw S) (J p S)=mean (uniformType Unit) (fun _=>mean (freshBlockLaw S) (J p S))
    exact (mean_const _ _).symm
  | succ n ih =>
    change mean (freshBlockLaw S) (fun s=>mean (first (reveal p (representativeSet s)))
      (fun a=>blockRoundMean J (fiber (reveal p (representativeSet s)) a)
        (eraseBlock S s) (n+1) (Fin.last n)))=_
    simp_rw [ih]
    change _=mean (sigmaLaw (freshBlockLaw S) fun s=>
      adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n)
      (fun h => mean (freshBlockLaw (historyUnused (eraseBlock S h.1) h.2.2))
        (J (historyPosterior (fiber (reveal p (representativeSet h.1)) h.2.1) h.2.2)
          (historyUnused (eraseBlock S h.1) h.2.2)))
    rw [mean_sigma]
    apply mean_congr
    intro s
    rw [mean_adaptive]

lemma blockRoundMean_total_irrel
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ)
    (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n m : ℕ)
    (i : Fin n) (j : Fin m) (hij : i.val=j.val) :
    blockRoundMean J p S n i=blockRoundMean J p S m j := by
  induction n generalizing p S m with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases m with
    | zero => exact Fin.elim0 j
    | succ m =>
      cases i using Fin.cases with
      | zero =>
        have hj : j=0 := Fin.ext (by simpa using hij.symm)
        subst j
        rfl
      | succ i =>
        have hj : j≠0 := by intro hz;subst j;simp at hij
        obtain ⟨j,rfl⟩:=Fin.exists_succ_eq.mpr hj
        simp only [blockRoundMean,Fin.cases_succ]
        apply mean_congr
        intro s
        apply mean_congr
        intro a
        apply ih _ _ _ i j
        simpa using hij

end SharpRamseyFive.FiniteEntropy

end

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

section
open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.uniformHistoryIndexDecEq
local instance uniformHistorySubtypeDecEq_r3e54ef_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
theorem exists_uniform_pre_round (μ : Law κ)
    (p : κ→Law (((B×A)⊕T)→β)) (S : κ→B→Finset A)
    (n : ℕ) (hn : 0<n) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    ∃ i : Fin n, mean μ (fun c=>blockRoundMean blockAllInformation (p c) (S c) n i)≤
      2*mean μ (fun c=>totalCorrelation (p c))/n := by
  have hb : (∑ i : Fin n,mean μ (fun c=>blockRoundMean blockAllInformation (p c) (S c) n i))≤
      2*mean μ (fun c=>totalCorrelation (p c)) := by
    rw [←mean_sum,←mean_smul]
    exact mean_mono_pos μ (fun c hc=>block_information_telescope (p c) (S c) n (hS c hc))
  by_contra! hh
  have hs := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hn⟩⟩) (fun i _=>hh i)
  have he : (∑ _i : Fin n,2*mean μ (fun c=>totalCorrelation (p c))/n)=
      2*mean μ (fun c=>totalCorrelation (p c)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  rw [he] at hs
  exact (not_lt_of_ge hb) hs

lemma preRound_mean (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ)
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ) :
    mean (preRoundLaw μ p S n) (fun z=>J (historyPosterior (p z.1.1) z.1.2)
      (historyUnused (S z.1.1) z.1.2) z.2)=
      mean μ (fun c=>blockRoundMean J (p c) (S c) (n+1) (Fin.last n)) := by
  rw [preRoundLaw,mean_adaptive,mean_adaptive]
  apply mean_congr
  intro c
  exact (history_round_mean J (p c) (S c) n).symm

theorem exists_preRoundLaw_information (μ : Law κ)
    (p : κ→Law (((B×A)⊕T)→β)) (S : κ→B→Finset A)
    (n : ℕ) (hn : 0<n) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    ∃ i : Fin n, mean (preRoundLaw μ p S i.val)
      (fun z=>blockAllInformation (historyPosterior (p z.1.1) z.1.2)
        (historyUnused (S z.1.1) z.1.2) z.2)≤
      2*mean μ (fun c=>totalCorrelation (p c))/n := by
  obtain ⟨i,hi⟩:=exists_uniform_pre_round μ p S n hn hS
  refine ⟨i,?_⟩
  rw [preRound_mean]
  have he (c : κ) := blockRoundMean_total_irrel blockAllInformation (p c) (S c)
    (i.val+1) n (Fin.last i.val) i rfl
  simp_rw [he]
  exact hi

lemma preRoundLaw_deficit (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (J : ℝ) (D : κ→((B×A)⊕T)→Finset β)
    (hJ : ∀ c x,Real.log (D c x).card≤J) (hp : ∀ c,0<μ c→InDomains (p c) (D c))
    (hfix : ∀ c,0<μ c→FixedOutside (p c) (blockActive (S c)))
    (n : ℕ) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    mean (preRoundLaw μ p S n) (fun z=>blockAllDeficit J
      (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)≤
      mean μ (fun c=>activeDeficit (p c) (blockActive (S c)) J) := by
  rw [preRound_mean]
  exact mean_mono_pos μ (fun c hc=>block_round_deficit J (D c) (hJ c)
    (p c) (S c) (hp c hc) (hfix c hc) (n+1) (hS c hc) (Fin.last n))

end

open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.historyProducerIndexDecEq
local instance historyProducerSubtypeDecEq_r3e54ef_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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
theorem preRound_bad_budget (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n r : ℕ) (hr : 0 < r)
    (hS : ∀ c,0<μ c→∀ b,r+n≤(S c b).card)
    (J d e : ℝ) (hd : 0<d) (he : 0<e) (D : κ→((B×A)⊕T)→Finset β)
    (hJ : ∀ c i,Real.log (D c i).card≤J)
    (hp : ∀ c,0<μ c→InDomains (p c) (D c))
    (hfix : ∀ c,0<μ c→FixedOutside (p c) (blockActive (S c)))
    (c : κ→BlockHistory B A T β n→((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (hc : ∀ a h i j,0 ≤ c a h i j) (C : ℝ)
    (hC : ∀ a,0<μ a→∀ h,0<historyLaw (p a) (S a) n h→
      (∑ i∈blockActive (historyUnused (S a) h),
        ∑ j∈blockActive (historyUnused (S a) h),c a h i j)≤C) :
    mean (preRoundLaw μ p S n) (fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),
      preRoundBad μ p S n J d e c z i)≤
      mean μ (fun a=>activeDeficit (p a) (blockActive (S a)) J)/d+
      (mean (preRoundLaw μ p S n) (fun z=>blockAllInformation
        (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)+C/r)/e := by
  have hlocal (a : κ) (ha : 0<μ a) (h : BlockHistory B A T β n)
      (hh : 0<historyLaw (p a) (S a) n h) :
      mean (freshBlockLaw (historyUnused (S a) h))
        (fun s=>∑ i∈blockActive (historyUnused (S a) h),
          indexBad J d e (historyPosterior (p a) h) (c a h) s i)≤
        mean (freshBlockLaw (historyUnused (S a) h))
          (blockAllDeficit J (historyPosterior (p a) h) (historyUnused (S a) h))/d+
        (mean (freshBlockLaw (historyUnused (S a) h))
          (blockAllInformation (historyPosterior (p a) h) (historyUnused (S a) h))+C/r)/e := by
    apply (fresh_bad_bound J d e hd he _ ((history_in_domains (p a) (D a) (hp a ha) n h).entropy_cap J (hJ a))
      _ (hc a h) _ r hr (history_unused_card (S a) r n (hS a ha) h)).trans
    gcongr
    exact hC a ha h hh
  have hb := mean_mono_pos μ (fun a ha=>mean_mono_pos (historyLaw (p a) (S a) n)
    (hlocal a ha))
  simp_rw [mean_add,mean_div,mean_add,mean_const] at hb
  have hdef := preRoundLaw_deficit μ p S J D hJ hp hfix n
    (fun a ha b=>by have := hS a ha b; omega)
  unfold preRoundLaw at hdef ⊢
  simp only [mean_adaptive,preRoundBad] at hdef ⊢
  exact hb.trans (by gcongr)

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

local instance readinessBlockDE_r3e54ef_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ConditionalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
variable {α β κ τ : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype τ]

omit [Fintype β] in
lemma omitted_card_eq {n : ℕ} (x : Fin n→β) (D : Finset β) :
    ((coveredPositions x D)ᶜ.card:ℝ)=∑ i:Fin n,if x i∉D then 1 else 0 := by
  have he : (coveredPositions x D)ᶜ=Finset.univ.filter fun i=>x i∉D := by
    ext i
    simp [coveredPositions]
  rw [he]
  simp only [←Finset.sum_boole]

end
end

open SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section
variable {κ β τ : Type} [Fintype κ] [Fintype β] [Fintype τ] {r n rem : ℕ} [Nonempty (Fin r)]

local instance readyExtractBlockDE_r3e54ef_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.readyExtractIndexDE
theorem preRound_ready_omissions (μ : Law κ) (p : κ→Law (Slots 1 r→β))
    (S : κ→(Fin 1×Bool)→Finset (Fin r)) (hrem : 0 < rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card) (J d e L : ℝ) (hL : 0≤L)
    (c : κ→BlockHistory (Fin 1×Bool) (Fin r) (Fin 1×Fin (2*r)) β n→Slots 1 r→Slots 1 r→ℝ)
    (sampler : ((κ×BlockHistory (Fin 1×Bool) (Fin r) (Fin 1×Fin (2*r)) β n)×
      ((Fin 1×Bool)→Fin r))→Law τ) (D : τ→Finset β)
    (hb : ∀ z,0<preRoundLaw μ p S n z→∀ t,
      windowReady (preRoundBad μ p S n J d e c z) z.2 0 t→
      mean (map (historyPosterior (p z.1.1) z.1.2) (fun x=>x (Sum.inr (0,t))))
        (fun b=>eventWeight (sampler z) (fun s=>b∉D s))≤L) :
    mean (adaptiveLaw (preRoundTupleLaw μ p S n) (fun z=>sampler z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (D z.2))ᶜ.card:ℝ))≤
      5*mean (preRoundLaw μ p S n) (fun z=>
        ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S n J d e c z i)+(2*r:ℝ)*L := by
  have hpoint : ∀ z,0<preRoundLaw μ p S n z→∀ t,
      mean (map (historyPosterior (p z.1.1) z.1.2) (fun x=>x (Sum.inr (0,t))))
        (fun b=>eventWeight (sampler z) (fun s=>b∉D s))≤
          (if windowReady (preRoundBad μ p S n J d e c z) z.2 0 t then (0:ℝ) else 1)+L := by
    intro z hz t
    by_cases hh : windowReady (preRoundBad μ p S n J d e c z) z.2 0 t
    · simpa only [ite_eq_left hh,zero_add] using hb z hz t hh
    · rw [ite_eq_right hh]
      exact (mean_mono _ (fun b=>eventWeight_le_one _ _)).trans (by rw [mean_const]; linarith)
  have he : mean (adaptiveLaw (preRoundTupleLaw μ p S n) (fun z=>sampler z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (D z.2))ᶜ.card:ℝ))=
      mean (preRoundLaw μ p S n) (fun z=>∑ t,
        mean (map (historyPosterior (p z.1.1) z.1.2) (fun x=>x (Sum.inr (0,t))))
          (fun b=>eventWeight (sampler z) (fun s=>b∉D s))) := by
    simp only [mean_adaptive,preRoundTupleLaw]
    apply mean_congr
    intro z
    simp_rw [omitted_card_eq,mean_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [mean_map]
    apply mean_congr
    intro x
    rw [eventWeight_mean]
    apply mean_congr
    intro zt
    by_cases hh : x (Sum.inr (0,t))∉D zt <;> simp only [hh]
  rw [he]
  have hh:=mean_mono_pos (preRoundLaw μ p S n) (fun z hz=>
    Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin (2*r)))) (fun t _=>hpoint z hz t))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mean_add,mean_const,Nat.cast_mul,Nat.cast_ofNat] at hh
  have hrdy:=preRound_ready_loss μ p S hrem hr hS J d e c
  simp only [Fin.sum_univ_one] at hrdy
  exact hh.trans (add_le_add hrdy le_rfl)
end

end SharpRamseyFive.FiniteEntropy

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GoodRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma good_pair_mass (p : Law (α×β)) (A : Finset α) (B : Finset β) :
    1-eventMass (first p) Aᶜ-eventMass (second p) Bᶜ≤eventMass p (A×ˢB) := by
  have hs (z : α×β) : p z≤(if z∈A×ˢB then p z else 0)+
      (if z.1∈Aᶜ then p z else 0)+(if z.2∈Bᶜ then p z else 0) := by
    by_cases ha : z.1∈A <;> by_cases hb : z.2∈B <;>
      simp [ha,hb,Finset.mem_compl,Finset.mem_product]
    linarith [p.nonneg z]
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun z _=>hs z)
  have hA : (∑ z:α×β,if z.1∈Aᶜ then p z else 0)=eventMass (first p) Aᶜ := by
    simp only [Fintype.sum_prod_type,eventMass,first]
    calc
      _ = ∑ a,if a∈Aᶜ then ∑ b,p (a,b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp only [Finset.sum_const_zero]
      _ = _ := by rw [Finset.sum_ite_mem,Finset.univ_inter]
  have hB : (∑ z:α×β,if z.2∈Bᶜ then p z else 0)=eventMass (second p) Bᶜ := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp only [eventMass,second]
    calc
      _ = ∑ b,if b∈Bᶜ then ∑ a,p (a,b) else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> simp only [Finset.sum_const_zero]
      _ = _ := by rw [Finset.sum_ite_mem,Finset.univ_inter]
  simp only [Finset.sum_add_distrib,p.sum_one,hA,hB,Finset.sum_ite_mem,Finset.univ_inter] at hh
  change 1≤eventMass p (A×ˢB)+eventMass (first p) Aᶜ+eventMass (second p) Bᶜ at hh
  linarith only [hh]

lemma goodRepresentative_first_cap (p : Law (α×β)) (A : Finset α) (B : Finset β)
    (h : 0<eventMass p (A×ˢB)) (M : ℝ) (hM : 0≤M)
    (hcap : ∀ a∈A,first p a≤M) (a : α) :
    first (goodRepresentative p A B h) a≤M/eventMass p (A×ˢB) := by
  by_cases ha : a∈A
  · apply le_trans _ (div_le_div_of_nonneg_right (hcap a ha) h.le)
    change (∑ b,conditionOn p (A×ˢB) h (a,b))≤(∑ b,p (a,b))/eventMass p (A×ˢB)
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun b _=>conditionOn_le p _ h (a,b)
  · have hz : first (goodRepresentative p A B h) a=0 := by
      simp only [first,goodRepresentative,conditionOn_apply,Finset.mem_product,ha,false_and,
        ite_false,Finset.sum_const_zero]
    rw [hz]
    exact div_nonneg hM h.le

lemma goodRepresentative_second_cap (p : Law (α×β)) (A : Finset α) (B : Finset β)
    (h : 0<eventMass p (A×ˢB)) (M : ℝ) (hM : 0≤M)
    (hcap : ∀ b∈B,second p b≤M) (b : β) :
    second (goodRepresentative p A B h) b≤M/eventMass p (A×ˢB) := by
  by_cases hb : b∈B
  · apply le_trans _ (div_le_div_of_nonneg_right (hcap b hb) h.le)
    change (∑ a,conditionOn p (A×ˢB) h (a,b))≤(∑ a,p (a,b))/eventMass p (A×ˢB)
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun a _=>conditionOn_le p _ h (a,b)
  · have hz : second (goodRepresentative p A B h) b=0 := by
      simp only [second,goodRepresentative,conditionOn_apply,Finset.mem_product,hb,and_false,
        ite_false,Finset.sum_const_zero]
    rw [hz]
    exact div_nonneg hM h.le

lemma relationMass_conditionOn_left (R : α→β→Prop) (p : Law α) (q : Law β)
    (E : Finset α) (h : 0<eventMass p E) :
    relationMass R (conditionOn p E h) q ≤ relationMass R p q/eventMass p E := by
  unfold relationMass
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro z _
  simpa only [div_mul_eq_mul_div] using
    mul_le_mul_of_nonneg_right (conditionOn_le p E h z.1) (q.nonneg z.2)

lemma forbidden_product_mass (p : Law (α×β)) (R : α→β→Prop)
    (h : ∀ z,0<p z→¬R z.1 z.2) :
    relationMass R (first p) (second p)≤
      2*(entropy (first p)+entropy (second p)-entropy p) := by
  have hz : eventWeight p (fun z=>R z.1 z.2)=0 := by
    apply eventWeight_zero
    intro z hz
    exact le_antisymm (le_of_not_gt (fun hp=>h z hp hz)) (p.nonneg z)
  have hh:=eventWeight_comparison p (product (first p) (second p)) (ac_product p) (fun z=>R z.1 z.2)
  rw [hz,add_zero,mutual_information] at hh
  simpa only [relationMass,Finset.sum_filter,eventWeight,product] using hh
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

end
end SharpRamseyFive.FiniteEntropy

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
local instance wpBDE_r3e54ef_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance wpTDE_r3e54ef_1 : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PreparedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {κ B A T β : Type} [Fintype κ] [Fintype B] [Fintype A] [Fintype T]
  [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.chosenRoundDE
lemma FixedOutside.totalCorrelation_le_active {ι : Type} [Fintype ι]
    (p : Law (ι→β)) (U : Finset ι) (J : ℝ) (hfix : FixedOutside p U)
    (hc : ∀i∈U,entropy (map p (fun x=>x i))≤J) :
    totalCorrelation p≤activeDeficit p U J := by
  unfold totalCorrelation activeDeficit
  apply sub_le_sub_right
  calc
    _ = ∑i∈U,entropy (map p (fun x=>x i)) := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi=>hfix.entropy_zero i hi)
    _ ≤ ∑_i∈U,J := Finset.sum_le_sum hc
    _ = _ := by simp

theorem exists_small_deletion_round (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (rounds rem : ℕ) (hrounds : 0 < rounds) (hrem : 0 < rem)
    (hS : ∀a,0<μ a→∀b,rem+rounds≤(S a b).card)
    (J d ε budget C : ℝ) (hd : 0<d) (hε : 0<ε)
    (D : κ→((B×A)⊕T)→Finset β) (hJ : ∀a i,Real.log (D a i).card≤J)
    (hp : ∀a,0<μ a→InDomains (p a) (D a))
    (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (S a)))
    (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (S a)) J)≤budget)
    (c : (i : Fin rounds)→κ→BlockHistory B A T β i.val→((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (hc : ∀i a h x y,0 ≤ c i a h x y)
    (hC : ∀i a,0<μ a→∀h,0<historyLaw (p a) (S a) i.val h→
      (∑x∈blockActive (historyUnused (S a) h),∑y∈blockActive (historyUnused (S a) h),c i a h x y)≤C) :
    ∃i : Fin rounds,mean (preRoundLaw μ p S i.val) (fun z=>
      ∑j∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S i.val J d ε (c i) z j)≤
      budget/d+(2*budget/rounds+C/rem)/ε := by
  obtain ⟨i,hi⟩:=exists_preRoundLaw_information μ p S rounds hrounds
    (fun a ha b=>by have := hS a ha b;omega)
  refine ⟨i,?_⟩
  have htc : mean μ (fun a=>totalCorrelation (p a))≤budget := by
    apply (mean_mono_pos μ (fun a ha=>FixedOutside.totalCorrelation_le_active (p a) _ J
      (hfix a ha) (fun j _=>(hp a ha).entropy_cap J (hJ a) j))).trans hbudget
  have hi' : mean (preRoundLaw μ p S i.val) (fun z=>blockAllInformation
      (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)≤2*budget/rounds :=
    hi.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htc (by norm_num)) (by positivity))
  have h:=preRound_bad_budget μ p S i.val rem hrem
    (fun a ha b=>by have := hS a ha b;have:=i.isLt;omega) J d ε hd hε D hJ hp hfix
    (c i) (hc i) C (hC i)
  exact h.trans (add_le_add (div_le_div_of_nonneg_right hbudget hd.le)
    (div_le_div_of_nonneg_right (add_le_add hi' le_rfl) hε.le))
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighSampleRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem fixed_target_loss (p : Law (SampleFlag (K:=K) (V:=V)))
    (z : SampleFlag (K:=K) (V:=V)) (hz : Incident z.1 z.2)
    (C : ℝ) (hC : 0≤C) (hp : ∀ b,second p b≤C)
    (hy : z.2∉lowHits (first p))
    (hsmall : 2*(Nat.card K:ℝ)^2*C≤1/(20*(Nat.card K:ℝ))) (n : ℕ) :
    eventWeight (iid (iid p (Fin n)) (Fin 3)) (fun x=>z∉highDomain x)≤
      3*(1-1/(5*(Nat.card K:ℝ)))^n+3*(n*eventWeight p (fun w=>SampleConflict w z)) := by
  have hsub : ∀ x : Fin 3→Fin n→SampleFlag (K:=K) (V:=V),z∉highDomain x →
      finrank K (sampleSpan x z.2)<4 ∨ ∃ j i,SampleConflict (x j i) z := by
    intro x hx
    by_cases hr : finrank K (sampleSpan x z.2)<4
    · exact Or.inl hr
    · apply Or.inr
      by_contra! hc
      apply hx
      apply mem_highDomain x z hz (by omega)
      intro j i hi
      by_contra hn
      exact hc j i ⟨hi,hn⟩
  apply (eventWeight_mono _ _ _ hsub).trans
  apply (eventWeight_union _ _ _).trans
  exact add_le_add (sampled_span_rank_failure p z.2 C hC hp hy hsmall n)
    (by simpa using iid_nested_exists_event (I:=Fin n) (J:=Fin 3) p (fun w=>SampleConflict w z))

omit [Finite K] [FiniteDimensional K V] in
lemma mean_second (r : Law (SampleFlag (K:=K) (V:=V))) (f : ℙ K (Dual K V)→ℝ) :
    mean r (fun z=>f z.2)=mean (second r) f := by
  simp only [mean,second,Fintype.sum_prod_type,Finset.sum_mul]
  exact Finset.sum_comm

omit [Finite K] [FiniteDimensional K V] in
lemma mean_sampleConflict (p r : Law (SampleFlag (K:=K) (V:=V))) :
    mean r (fun z=>eventWeight p (fun w=>SampleConflict w z))=relationMass SampleConflict p r := by
  rw [relationMass_by_target]
  simp only [mean,eventWeight,Finset.sum_filter]

theorem sampled_target_loss (hdim : finrank K V=5)
    (p r : Law (SampleFlag (K:=K) (V:=V)))
    (hrflag : ∀ z,0 < r z→Incident z.1 z.2)
    (G : Finset (ℙ K (Dual K V))) (A B C : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (hpA : ∀ a,first p a≤A) (hrB : ∀ b∈G,second r b≤B) (hpC : ∀ b,second p b≤C)
    (hsmall : 2*(Nat.card K:ℝ)^2*C≤1/(20*(Nat.card K:ℝ))) (n : ℕ) :
    mean r (fun z=>eventWeight (iid (iid p (Fin n)) (Fin 3)) (fun x=>z∉highDomain x)) ≤
      eventMass (second r) Gᶜ+64*(Nat.card K:ℝ)^5*A*B+
      3*(1-1/(5*(Nat.card K:ℝ)))^n+3*n*relationMass SampleConflict p r := by
  let E : ℝ:=3*(1-1/(5*(Nat.card K:ℝ)))^n
  have hq : 2≤(Nat.card K:ℝ) := by exact_mod_cast Finite.one_lt_card (α:=K)
  have hc : 0≤1-1/(5*(Nat.card K:ℝ)) := by
    have hh : 1/(5*(Nat.card K:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hE : 0≤E := mul_nonneg (by norm_num) (pow_nonneg hc _)
  have hpoint : mean r (fun z=>eventWeight (iid (iid p (Fin n)) (Fin 3)) (fun x=>z∉highDomain x)) ≤
      mean r (fun z=>(if z.2∈lowHits (first p) then 1 else 0)+E+
        3*n*eventWeight p (fun w=>SampleConflict w z)) := by
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : 0 < r z
    · apply mul_le_mul_of_nonneg_left _ (r.nonneg z)
      dsimp only
      by_cases hy : z.2∈lowHits (first p)
      · rw [ite_eq_left hy]
        have hn : 0≤3*(n:ℝ)*eventWeight p (fun w=>SampleConflict w z) :=
          mul_nonneg (by positivity) (eventWeight_nonneg _ _)
        linarith [eventWeight_le_one (iid (iid p (Fin n)) (Fin 3)) (fun x=>z∉highDomain x)]
      · rw [ite_eq_right hy,zero_add]
        simpa only [mul_assoc] using fixed_target_loss p z (hrflag z hz) C hC hpC hy hsmall n
    · have hz' : r z=0 := le_antisymm (le_of_not_gt hz) (r.nonneg z)
      simp only [hz',zero_mul,le_refl]
  have he : mean r (fun z=>(if z.2∈lowHits (first p) then 1 else 0)+E+
        3*n*eventWeight p (fun w=>SampleConflict w z))=
      eventMass (second r) (lowHits (first p))+E+3*n*relationMass SampleConflict p r := by
    rw [mean_add,mean_add,mean_const,mean_smul,mean_sampleConflict]
    congr 2
    rw [mean_second r (fun b=>if b∈lowHits (first p) then (1:ℝ) else 0)]
    simp only [mean,eventMass,mul_ite,mul_one,mul_zero]
    symm
    calc
      _ = ∑ b∈lowHits (first p),if b∈lowHits (first p) then second r b else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [ite_eq_left hb]
      _ = ∑ b,if b∈lowHits (first p) then second r b else 0 := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro b _ hb
        rw [ite_eq_right hb]
  have hl : eventMass (second r) (lowHits (first p)) ≤
      eventMass (second r) Gᶜ+64*(Nat.card K:ℝ)^5*A*B := by
    have hm := lowHits_mass hdim (first p) (second r) G A B hA hB
      (fun a=>⟨(first p).nonneg a,hpA a⟩) (by rw [(first p).sum_one];norm_num)
      (by rw [(first p).sum_one]) hrB
    have hh : eventMass (second r) (lowHits (first p))≤
        eventMass (second r) Gᶜ+eventMass (second r) (G∩lowHits (first p)) := by
      have he0 (S : Finset (ℙ K (Dual K V))) : eventMass (second r) S =
          eventWeight (second r) (fun b=>b∈S) := by
        unfold eventMass eventWeight
        calc
          _ = ∑ b∈S,if b∈S then second r b else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [ite_eq_left hb]
          _ = ∑ b,if b∈S then second r b else 0 := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro b _ hb
            rw [ite_eq_right hb]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases hb : b∈S <;> simp only [hb,ite_true,ite_false]
      simp only [he0,eventWeight,←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b∈G <;> by_cases hl : b∈lowHits (first p) <;>
        simp only [Finset.mem_compl,Finset.mem_inter,hb,hl,
          and_true,and_false,not_true_eq_false,not_false_eq_true,ite_true,ite_false,
          add_zero,zero_add,le_refl]
      exact (second r).nonneg b
    exact hh.trans (add_le_add le_rfl hm)
  rw [he] at hpoint
  exact hpoint.trans (add_le_add (add_le_add hl le_rfl) le_rfl)
end
end SharpRamseyFive.HighSamples

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

attribute [local instance] OAI.SharpRamseyFive.Marking.highRepDE
attribute [local instance] OAI.SharpRamseyFive.Marking.highRepDualDE
lemma highLeft_cap (p : Law (FlagPair K V)) (r' : ℕ) (s : ℝ) (a : ℙ K V)
    (ha : a∈highLeft p r' s) : first p a≤Real.exp s/(Nat.card K:ℝ)^r' := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  exact (le_div_iff₀ (pow_pos hq r')).mpr (by
    simpa only [mul_comm] using
      (Finset.mem_filter.mp (show a∈highGoodFirst _ _ _ _ _ from ha)).2)
lemma highRight_cap (p : Law (FlagPair K V)) (r : ℕ) (s : ℝ) (b : ℙ K (Dual K V))
    (hb : b∈highRight p r s) : second p b≤Real.exp s/(Nat.card K:ℝ)^r := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hh:=(Finset.mem_filter.mp (show b∈highGoodFirst _ _ _ _ _ from hb)).2
  rw [first_swap] at hh
  exact (le_div_iff₀ (pow_pos hq r)).mpr (by simpa only [mul_comm] using hh)

omit [Finite K] in
lemma high_pair_half (p : Law (FlagPair K V)) (r r' : ℕ) (s b : ℝ)
    (ha : eventMass (first p) (highLeft p r' s)ᶜ≤b)
    (hb : eventMass (second p) (highRight p r s)ᶜ≤b) (hsmall : b≤(1:ℝ)/4) :
    (1:ℝ)/2≤eventMass p (highLeft p r' s×ˢhighRight p r s) := by
  have h:=good_pair_mass p (highLeft p r' s) (highRight p r s)
  linarith

theorem highRepresentative_bounds (p : Law (FlagPair K V)) (r r' : ℕ) (s : ℝ)
    (hhalf : (1:ℝ)/2≤eventMass p (highLeft p r' s×ˢhighRight p r s)) :
    (∀ z,highRepresentative p r r' s z≤2*p z) ∧
    (∀ a,first (highRepresentative p r r' s) a≤2*Real.exp s/(Nat.card K:ℝ)^r') ∧
    (∀ b,second (highRepresentative p r r' s) b≤2*Real.exp s/(Nat.card K:ℝ)^r) := by
  have hpos : 0<eventMass p (highLeft p r' s×ˢhighRight p r s) := by linarith
  have he : highRepresentative p r r' s=
      goodRepresentative p (highLeft p r' s) (highRight p r s) hpos := by
    simp only [highRepresentative,dite_eq_left hpos,goodRepresentative]
  rw [he]
  constructor
  · intro z
    apply (conditionOn_le p _ hpos z).trans
    apply (div_le_iff₀ hpos).mpr
    nlinarith [p.nonneg z]
  constructor
  · intro a
    apply (goodRepresentative_first_cap p _ _ hpos (Real.exp s/(Nat.card K:ℝ)^r')
      (by positivity) (highLeft_cap p r' s) a).trans
    apply (div_le_iff₀ hpos).mpr
    have hz : 0≤Real.exp s/(Nat.card K:ℝ)^r' := by positivity
    have hs := mul_le_mul_of_nonneg_left hhalf (show 0≤2*(Real.exp s/(Nat.card K:ℝ)^r') by positivity)
    rw [mul_div_assoc]
    nlinarith only [hs]
  · intro b
    apply (goodRepresentative_second_cap p _ _ hpos (Real.exp s/(Nat.card K:ℝ)^r)
      (by positivity) (highRight_cap p r s) b).trans
    apply (div_le_iff₀ hpos).mpr
    have hz : 0≤Real.exp s/(Nat.card K:ℝ)^r := by positivity
    have hs := mul_le_mul_of_nonneg_left hhalf (show 0≤2*(Real.exp s/(Nat.card K:ℝ)^r) by positivity)
    rw [mul_div_assoc]
    nlinarith only [hs]

omit [Finite K] in
theorem highRepresentative_conflict (p : Law (FlagPair K V×FlagPair K V))
    (r r' : ℕ) (s ε : ℝ)
    (hcons : ∀ z,0<p z→Incident z.1.1 z.2.2→Incident z.2.1 z.1.2)
    (hhalf : (1:ℝ)/2≤eventMass (first p) (highLeft (first p) r' s×ˢhighRight (first p) r s))
    (hI : entropy (first p)+entropy (second p)-entropy p≤ε) :
    relationMass SampleConflict (highRepresentative (first p) r r' s) (second p)≤4*ε := by
  have hpos : 0<eventMass (first p) (highLeft (first p) r' s×ˢhighRight (first p) r s) := by linarith
  have hforbid:=forbidden_product_mass p SampleConflict (by
    intro z hz hc
    exact hc.2 (hcons z hz hc.1))
  have hI0 : 0≤entropy (first p)+entropy (second p)-entropy p := by
    linarith [entropy_subadditive p]
  have he0 : 0≤ε := hI0.trans hI
  simp only [highRepresentative,dite_eq_left hpos]
  apply (relationMass_conditionOn_left SampleConflict (first p) (second p) _ hpos).trans
  apply (div_le_iff₀ hpos).mpr
  have hm:=mul_le_mul_of_nonneg_left hhalf (show 0≤4*ε by positivity)
  linarith
end
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

theorem high_domain_pair_loss (hdim : finrank K V=5)
    (D₁ D₂ : Finset (FlagPair K V)) (r' : ℕ) (hr' : r'≤4)
    (hcap₁ : HighCaps D₁ 4 r') (hcap₂ : HighCaps D₂ 4 r')
    (p : Law (FlagPair K V×FlagPair K V))
    (hD1 : support (FiniteEntropy.first p)⊆D₁) (hD2 : support (FiniteEntropy.second p)⊆D₂)
    (hcons : ∀ z,0<p z→Incident z.1.1 z.2.2→Incident z.2.1 z.1.2)
    (hflag : ∀ z,0 < second p z→Incident z.1 z.2)
    (s d ε : ℝ) (hs : 0 < s)
    (hent1 : 4*Real.log (Nat.card K)-entropy (FiniteEntropy.first p)≤d)
    (hent2 : 4*Real.log (Nat.card K)-entropy (FiniteEntropy.second p)≤d)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hI : entropy (FiniteEntropy.first p)+entropy (FiniteEntropy.second p)-entropy p≤ε)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (h : ℕ) :
    mean (FiniteEntropy.second p) (fun z=>eventWeight
      (iid (iid (highRepresentative (FiniteEntropy.first p) 4 r' s) (Fin h)) (Fin 3))
      (fun x=>z∉highDomain x))≤
      highBadMass s d 153+64*(Nat.card K:ℝ)^5*(2*Real.exp s/(Nat.card K:ℝ)^r')*
        (Real.exp s/(Nat.card K:ℝ)^4)+3*(1-1/(5*(Nat.card K:ℝ)))^h+12*h*ε := by
  have hB1:=hcap₁.endpoint_bad (FiniteEntropy.first p) hD1 (by decide) hr' s d hs hent1
  have hB2:=hcap₂.endpoint_bad (FiniteEntropy.second p) hD2 (by decide) hr' s d hs hent2
  have half:=high_pair_half (FiniteEntropy.first p) 4 r' s _ hB1.1 hB1.2 hbad
  have hrep:=highRepresentative_bounds (FiniteEntropy.first p) 4 r' s half
  have hconf:=highRepresentative_conflict p 4 r' s ε hcons half hI
  apply (sampled_target_loss hdim (highRepresentative (FiniteEntropy.first p) 4 r' s) (FiniteEntropy.second p) hflag
    (highRight (FiniteEntropy.second p) 4 s) (2*Real.exp s/(Nat.card K:ℝ)^r')
    (Real.exp s/(Nat.card K:ℝ)^4) (2*Real.exp s/(Nat.card K:ℝ)^4)
    (by positivity) (by positivity) (by positivity) hrep.2.1
    (highRight_cap (FiniteEntropy.second p) 4 s) hrep.2.2 hsmall h).trans
  have hmul:=mul_le_mul_of_nonneg_left hconf (show 0≤3*(h:ℝ) by positivity)
  linarith [hB2.2]
end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N w r : ℕ} [Nonempty (Fin r)]

local instance highDomainStageBlockDE_r3e54ef_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.highDomainStageIndexDE
omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
  [Nonempty (Fin r)] in
theorem high_domain_good_pair_loss (hdim : finrank K V=5)
    (D : Slots w r→Finset (FlagPair K V))
    (p : Law (Slots w r→FlagPair K V))
    (hD : ∀ i,support (map p (fun x=>x i))⊆D i)
    (r' : ℕ) (hr' : r'≤4) (hcap : ∀i,HighCaps (D i) 4 r')
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i < slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hflag : ∀ x,0<p x→∀ i,Incident (x i).1 (x i).2)
    (J d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hs : 0 < s)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (c : Slots w r→Slots w r→ℝ) (hc : ∀ i j,0 ≤ c i j) (hcs : ∀ i j,c i j=c j i)
    (sel : (Fin w×Bool)→Fin r) (v : Fin w) (t : Fin (2*r))
    (hready : windowReady (indexBad J d ε p c sel) sel v t) (h : ℕ) :
    mean (map p (fun x=>x (Sum.inr (v,t)))) (fun z=>eventWeight
      (iid (iid (highRepresentative (map p (fun x=>x (Sum.inl ((v,false),sel (v,false))))) 4 r' s)
        (Fin h)) (Fin 3)) (fun x=>z∉highDomain x))≤
      highBadMass s d 153+64*(Nat.card K:ℝ)^5*(2*Real.exp s/(Nat.card K:ℝ)^r')*
        (Real.exp s/(Nat.card K:ℝ)^4)+3*(1-1/(5*(Nat.card K:ℝ)))^h+12*h*ε := by
  let i : Slots w r:=Sum.inl ((v,false),sel (v,false))
  let j : Slots w r:=Sum.inr (v,t)
  let q:=pair p (fun x=>x i) (fun x=>x j)
  have hqi : first q=map p (fun x=>x i) := first_pair p _ _
  have hqj : second q=map p (fun x=>x j) := second_pair p _ _
  have hi:=good_index_scores J d ε p c hc sel i (hready.2 false)
  have hj:=good_index_scores J d ε p c hc sel j hready.1
  have hI:=good_index_scores_reverse J d ε p c hc hcs sel j hready.1 (v,false) trivial
  have hIc : entropy (first q)+entropy (second q)-entropy q≤ε := by
    rw [hqi,hqj]
    exact le_trans (le_add_of_nonneg_right (hc i j)) hI
  have hpc : ∀ z,0<q z→Incident z.1.1 z.2.2→Incident z.2.1 z.1.2 := by
    intro z hz
    obtain ⟨x,hx,he⟩:=map_positive p (fun x=>(x i,x j)) z hz
    cases he
    exact hcons x hx i j (representative_early v (sel (v,false)) t)
  have hpf : ∀ z,0 < second q z→Incident z.1 z.2 := by
    intro z hz
    rw [hqj] at hz
    obtain ⟨x,hx,he⟩:=map_positive p (fun x=>x j) z hz
    cases he
    exact hflag x hx j
  have H:=high_domain_pair_loss hdim (D i) (D j) r' hr' (hcap i) (hcap j) q
    (hqi ▸ hD i) (hqj ▸ hD j)
    hpc hpf s d ε hs (by rw [hqi]; linarith [hi.1])
    (by rw [hqj]; linarith [hj.1]) hbad hIc hsmall h
  simpa only [hqi,hqj,i,j] using H
end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighFourPreRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N r : ℕ} [Nonempty (Fin r)]

local instance highFourPreBlockDE_r3e54ef_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.highFourPreIndexDE
lemma highFourLoss_nonneg (q : ℕ) (hq : 1≤q) (r' h : ℕ) (s d ε : ℝ)
    (hs : 0 < s) (hd : 0≤d) (he : 0≤ε) : 0≤highFourLoss q r' h s d ε := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hb : 0≤1-1/(5*(q:ℝ)) := by
    have hh : 0<5*(q:ℝ) := by linarith
    have hh' : 1/(5*(q:ℝ))≤1 := (div_le_one hh).mpr (by linarith)
    linarith
  unfold highFourLoss highBadMass
  positivity

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighDomainPreRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N r : ℕ} [Nonempty (Fin r)]

local instance highDomainPreBlockDE_r3e54ef_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.highDomainPreIndexDE
omit [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_domain_preRound_omissions {κ : Type} [Fintype κ] {n rem : ℕ}
    (hdim : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots 1 r→FlagPair K V))
    (D : κ→Slots 1 r→Finset (FlagPair K V))
    (hD : ∀a,0<μ a→InDomains (p a) (D a))
    (r' : ℕ) (hr' : r'≤4) (hcap : ∀a,0<μ a→∀i,HighCaps (D a i) 4 r')
    (hcons : ∀ a,0<μ a→∀ x,0<p a x→∀ i j,slotEmbedding i < slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hflag : ∀ a,0<μ a→∀ x,0<p a x→∀ i,Incident (x i).1 (x i).2)
    (S : κ→(Fin 1×Bool)→Finset (Fin r)) (hrem : 0 < rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card)
    (J d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hs : 0 < s) (hd : 0≤d) (he : 0≤ε)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (c : κ→BlockHistory (Fin 1×Bool) (Fin r) (Fin 1×Fin (2*r)) (FlagPair K V) n→
      Slots 1 r→Slots 1 r→ℝ)
    (hc : ∀ a z i j,0 ≤ c a z i j) (hcs : ∀ a z i j,c a z i j=c a z j i)
    (h : ℕ) :
    mean (adaptiveLaw (preRoundTupleLaw μ p S n) (fun z=>highFourSampler p r' s h z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
      5*mean (preRoundLaw μ p S n) (fun z=>
        ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S n J d ε c z i)+
        (2*r:ℝ)*highFourLoss (Nat.card K) r' h s d ε := by
  refine preRound_ready_omissions μ p S hrem hr hS J d ε
    (highFourLoss (Nat.card K) r' h s d ε)
    (highFourLoss_nonneg _ (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
      (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))))) r' h s d ε hs hd he) c
    (highFourSampler p r' s h) highDomain ?_
  intro z hz t hrdy
  have ha:=(preRound_positive μ p S n z hz).1
  change _ ≤ highFourLoss (Nat.card K) r' h s d ε
  unfold highFourSampler highFourLoss
  apply high_domain_good_pair_loss hdim (D z.1.1)
    (historyPosterior (p z.1.1) z.1.2) _ r' hr' (hcap _ ha) _ _
    J d s ε hJ hs hbad hsmall (c z.1.1 z.1.2) (hc _ _) (hcs _ _)
    z.2 0 t hrdy h
  · intro i
    exact marginal_support_subset _ _ (history_in_domains _ _ (hD _ ha) n z.1.2) i
  · intro x hx i j hij hi
    exact hcons _ ha x (history_support (p z.1.1) n z.1.2 x hx) i j hij hi
  · intro x hx i
    exact hflag _ ha x (history_support (p z.1.1) n z.1.2 x hx) i
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_HighSampleContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}

local instance hprBDE_r3e54ef_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance hprTDE_r3e54ef_1 : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hprIDE
omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_prepared_round_oai (hd : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
    (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
    (r' : ℕ) (hr' : r'≤4)
    (hcap : ∀c,0 < map S.law ctx c→∀i,HighCaps (P.domain c i) 4 r')
    (rounds rem : ℕ) (hrounds : 0 < rounds) (hrem : 0 < rem)
    (hn : n≤2*rem) (hroom : rem+rounds≤n)
    (d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hdp : 0<d) (hs : 0 < s) (he : 0<ε)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (h : ℕ) :
    ∃i : Fin rounds,
      mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
        (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val)
        (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
        (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
          5*(B/d+(2*B/rounds)/(ε))+(2*n:ℝ)*highFourLoss (Nat.card K) r' h s d ε := by
  let μ:=first (pair S.law ctx (windowTuple S))
  let p:=fiber (pair S.law ctx (windowTuple S))
  let elig:=fun _ : κ=>fun _ : Fin 1×Bool=>(Finset.univ : Finset (Fin n))
  have hS : ∀c,0<μ c→∀b,rem+rounds≤(elig c b).card := by
    intro c hc b
    simpa only [elig,Finset.card_univ,Fintype.card_fin] using hroom
  have hD:=window_posterior_domains S ctx P.domain P.contains
  have hbudget : mean μ (fun c=>activeDeficit (p c) (blockActive (elig c)) J)≤B := by
    dsimp only [μ,p,elig]
    rw [window_posterior_deficit]
    have h:=P.deficit
    simp only [Nat.cast_mul,Nat.cast_ofNat] at h
    have he : psFinDE (1*(4*n)) = (inferInstance : DecidableEq (Fin (1*(4*n)))) := Subsingleton.elim _ _
    rw [he] at h
    exact h
  obtain ⟨i,hi⟩:=exists_small_deletion_round μ p elig rounds rem hrounds hrem hS
    J d ε B 0 hdp he (fun c i=>P.domain c (slotEmbedding i))
    (fun c i=>P.cap c (slotEmbedding i)) hD
    (fun c _=>by simpa only [elig,blockActive_univ] using fixedOutside_univ (p c)) hbudget
    (fun _ _ _ _ _=>0) (by intros;exact le_rfl)
    (by intros;simp)
  refine ⟨i,?_⟩
  have hp:=high_domain_preRound_omissions (n:=i.val) (rem:=rem) hd μ p (fun c i=>P.domain c (slotEmbedding i))
    hD r' hr' (fun c hc i=>hcap c (by simpa only [μ,first_pair] using hc) (slotEmbedding i))
    (window_posterior_consistent S ctx P.consistent) (window_posterior_incident S ctx P.incident)
    elig hrem hn (fun c hc b=>by have:=hS c hc b;have:=i.isLt;omega)
    J d s ε hJ hs hdp.le he.le hbad hsmall
    (fun _ _ _ _=>0) (by intros;exact le_rfl) (by intros;rfl) h
  apply hp.trans
  exact add_le_add (mul_le_mul_of_nonneg_left
    (by simpa only [zero_div,add_zero] using hi) (by norm_num)) le_rfl
end

end SharpRamseyFive.SelectedTuple

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.SelectedTuple.high_prepared_round_oai := @OAI.SharpRamseyFive.SelectedTuple.high_prepared_round_oai
