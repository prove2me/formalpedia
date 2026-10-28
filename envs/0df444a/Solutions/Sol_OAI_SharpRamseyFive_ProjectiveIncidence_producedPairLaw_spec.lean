-- Prove2me | solution 1 for OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:15:41.175509+00:00
-- url     : https://prove2.me/submissions/61d10fff-7e10-4d57-873f-d325efa9c6af

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003

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

lemma eventMass_nonneg (p : Law α) (E : Finset α) : 0≤eventMass p E :=
  Finset.sum_nonneg fun a _ => p.nonneg a

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Hits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma hits_cons (H : Finset α) {n : ℕ} (a : α) (x : Fin n → α) :
    hits H (Fin.cons a x)=(if a∈H then 1 else 0)+hits H x := by
  simp only [hits,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma expected_hits (p : Law α) (H : Finset α) (n : ℕ) :
    (∑ x,iid p (Fin n) x*hits H x)=(n:ℝ)*eventMass p H := by
  induction n with
  | zero => simp [hits]
  | succ n hn =>
    rw [sum_iid_succ]
    simp only [hits_cons,mul_add,Finset.sum_add_distrib]
    have h1 : (∑ a,∑ x,p a*iid p (Fin n) x*(if a∈H then 1 else 0))=eventMass p H := by
      calc
        _ = ∑ a,p a*(if a∈H then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [←Finset.sum_mul,←Finset.mul_sum,(iid p (Fin n)).sum_one,mul_one]
        _ = _ := by simp [mul_ite,eventMass]
    have h2 : (∑ a,∑ x,p a*iid p (Fin n) x*hits H x)=(n:ℝ)*eventMass p H := by
      simp only [mul_assoc,←Finset.mul_sum,hn,←Finset.sum_mul,p.sum_one,one_mul]
    rw [h1,h2,Nat.cast_add,Nat.cast_one]
    ring

lemma event_markov (p : Law α) (w : α → ℝ) (hw : ∀ a,0≤w a) (t : ℝ)
    (E : Finset α) (hE : ∀ a∈E,t≤w a) :
    t*eventMass p E≤∑ a,p a*w a := by
  rw [eventMass,Finset.mul_sum]
  calc
    _ ≤ ∑ a∈E,p a*w a := Finset.sum_le_sum fun a ha => by
      simpa only [mul_comm t] using mul_le_mul_of_nonneg_left (hE a ha) (p.nonneg a)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
      mul_nonneg (p.nonneg a) (hw a))

theorem iid_test_rejection (p : Law α) (H : Finset α) (n : ℕ) (hn : 0<n)
    (c : ℝ) (hc : 0 < c) :
    eventMass (iid p (Fin n)) (Finset.univ.filter fun x => c*n≤hits H x)≤eventMass p H/c := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hh := event_markov (iid p (Fin n)) (hits H) (by
      intro x
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num)
    (c*n) (Finset.univ.filter fun x => c*n≤hits H x) (by
      intro x hx
      exact (Finset.mem_filter.mp hx).2)
  rw [expected_hits] at hh
  apply (le_div_iff₀ hc).mpr
  nlinarith

end
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma uniformOn_mass (A : Finset α) (hA : A.Nonempty) (H : Finset α) :
    eventMass (uniformOn A hA) H = ((H∩A).card:ℝ)/A.card := by
  simp only [eventMass,uniformOn,←Finset.sum_filter,Finset.filter_mem_eq_inter,
    Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]

lemma iid_uniformOn {n : ℕ} (A : Finset α) (hA : A.Nonempty) (x : Fin n → α) :
    iid (uniformOn A hA) (Fin n) x =
      if (∀ i,x i∈A) then ((A.card:ℝ)⁻¹)^n else 0 := by
  by_cases h : ∀ i,x i∈A
  · simp [iid,uniformOn,h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    simp only [iid]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [uniformOn,hi])]
    simp only [h,ite_false]

lemma uniformOn_row_scaling {n : ℕ} (A W : Finset α) (hA : A.Nonempty)
    (hW : W.Nonempty) (hAW : A⊆W) (x : Fin n → α) (hx : ∀ i,x i∈A) :
    iid (uniformOn W hW) (Fin n) x = ((A.card:ℝ)/W.card)^n*
      iid (uniformOn A hA) (Fin n) x := by
  rw [iid_uniformOn,iid_uniformOn,ite_eq_left hx,ite_eq_left (fun i => hAW (hx i))]
  have hc : (A.card:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hA)
  rw [←mul_pow]
  congr 1
  field_simp

lemma eventMass_scaling (p r : Law α) (E : Finset α) (s : ℝ)
    (h : ∀ a∈E,p a=s*r a) : eventMass p E=s*eventMass r E := by
  simp only [eventMass,Finset.mul_sum]
  exact Finset.sum_congr rfl h

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IIDLowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A : Type*} [Fintype A]

lemma exp_neg_one_le_half : Real.exp (-1) ≤ (1/2:ℝ) := by
  have h := Real.add_one_le_exp (1:ℝ)
  rw [Real.exp_neg]
  rw [←one_div]
  exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith)

lemma expected_exp_neg_hit (p : Law A) (H : Finset A) :
    (∑a,p a*Real.exp (-(if a∈H then (1:ℝ) else 0)))=
      1-(1-Real.exp (-1))*eventMass p H := by
  have hh (a : A) : p a*Real.exp (-(if a∈H then (1:ℝ) else 0))=
      p a-(1-Real.exp (-1))*(if a∈H then p a else 0) := by
    split_ifs
    · ring
    · norm_num
  simp_rw [hh]
  rw [Finset.sum_sub_distrib,p.sum_one,←Finset.mul_sum]
  simp only [eventMass,←Finset.sum_filter,Finset.filter_univ_mem]

lemma expected_exp_neg_hits (p : Law A) (H : Finset A) (n : ℕ) :
    (∑x,iid p (Fin n) x*Real.exp (-hits H x))=
      (1-(1-Real.exp (-1))*eventMass p H)^n := by
  have hh (x : Fin n→A) : Real.exp (-hits H x)=
      ∏i,Real.exp (-(if x i∈H then (1:ℝ) else 0)) := by
    rw [hits,←Finset.sum_neg_distrib,Real.exp_sum]
  change (∑x,(∏i,p (x i))*Real.exp (-hits H x))=_
  simp_rw [hh,←Finset.prod_mul_distrib]
  rw [←Fintype.sum_pow (fun a=>p a*Real.exp (-(if a∈H then (1:ℝ) else 0))) n,
    expected_exp_neg_hit]

lemma expected_exp_neg_hits_le (p : Law A) (H : Finset A) (n : ℕ) :
    (∑x,iid p (Fin n) x*Real.exp (-hits H x)) ≤
      Real.exp (-eventMass p H*n/2) := by
  have hbase : 0 ≤ 1-(1-Real.exp (-1))*eventMass p H := by
    rw [←expected_exp_neg_hit]
    exact Finset.sum_nonneg fun a _=>mul_nonneg (p.nonneg a) (Real.exp_pos _).le
  have hp := eventMass_nonneg p H
  have hsmall : 1-(1-Real.exp (-1))*eventMass p H ≤ Real.exp (-eventMass p H/2) := by
    have he := Real.add_one_le_exp (-eventMass p H/2)
    have hh := mul_le_mul_of_nonneg_right exp_neg_one_le_half hp
    nlinarith
  rw [expected_exp_neg_hits]
  calc
    _ ≤ (Real.exp (-eventMass p H/2))^n := pow_le_pow_left₀ hbase hsmall n
    _ = _ := by rw [←Real.exp_nat_mul];congr 1;ring

theorem iid_low_hit_event (p : Law A) (H : Finset A) (n : ℕ) (t : ℝ)
    (E : Finset (Fin n→A)) (hE : ∀x∈E,hits H x ≤ t) :
    eventMass (iid p (Fin n)) E ≤ Real.exp (t-eventMass p H*n/2) := by
  have hx := event_markov (iid p (Fin n)) (fun x=>Real.exp (-hits H x))
    (fun x=>(Real.exp_pos _).le) (Real.exp (-t)) E (fun x hx=>
      Real.exp_le_exp.mpr (neg_le_neg (hE x hx)))
  have hh := hx.trans (expected_exp_neg_hits_le p H n)
  calc
    _ ≤ Real.exp (-eventMass p H*n/2)/Real.exp (-t) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hh)
    _ = _ := by rw [←Real.exp_sub];congr 1;ring

theorem iid_cap_tail (p : Law A) (H : Finset A) (n : ℕ) (q : ℝ) (hq : 0 < q)
    (hH : 1/(2*q) ≤ eventMass p H) :
    eventMass (iid p (Fin n)) (Finset.univ.filter fun x=>hits H x < (n:ℝ)/(5*q)) ≤
      Real.exp (-(n:ℝ)/(20*q)) := by
  have hh := iid_low_hit_event p H n ((n:ℝ)/(5*q))
    (Finset.univ.filter fun x=>hits H x < (n:ℝ)/(5*q)) (fun x hx=>(Finset.mem_filter.mp hx).2.le)
  refine hh.trans (Real.exp_le_exp.mpr ?_)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hH hn
  have he : (n:ℝ)/(5*q)-(1/(2*q))*n/2= -(n:ℝ)/(20*q) := by field_simp;ring
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ReverseCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

lemma expected_filter_card {X : Type*} [Fintype X] (p : Law X)
    (U : Finset A) (F : A→X→Prop) :
    (∑x,p x*((U.filter fun a=>F a x).card:ℝ))=
      ∑a∈U,eventMass p (Finset.univ.filter (F a)) := by
  simp only [←Finset.sum_boole,Finset.mul_sum,eventMass,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

lemma uniform_neighbor_mass (R : A→B→Prop) (C : Finset B) (hC : C.Nonempty) (a : A) :
    eventMass (uniformOn C hC) (neighbors R a)=((C.filter (R a)).card:ℝ)/C.card := by
  rw [uniformOn_mass]
  have he : neighbors R a∩C=C.filter (R a) := by
    ext b
    simp [neighbors,and_comm]
  rw [he]

theorem expected_cap_card (R : A→B→Prop) (U Bad : Finset A)
    (C : Finset B) (hC : C.Nonempty) (n : ℕ) (q : ℝ) (hq : 0 < q)
    (hgood : ∀a∈U,a∉Bad → 1/(2*q) ≤ ((C.filter (R a)).card:ℝ)/C.card) :
    (∑row,iid (uniformOn C hC) (Fin n) row*((cap R U q row).card:ℝ)) ≤
      (Bad.card:ℝ)+(U.card:ℝ)*Real.exp (-(n:ℝ)/(20*q)) := by
  simp only [cap]
  rw [expected_filter_card]
  let z := Real.exp (-(n:ℝ)/(20*q))
  have hz : 0 ≤ z := (Real.exp_pos _).le
  calc
    _ ≤ ∑a∈U,((if a∈Bad then (1:ℝ) else 0)+z) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hb : a∈Bad
      · simp only [hb,ite_true]
        exact (eventMass_le_one _ _).trans (by linarith)
      · simp only [hb,ite_false,zero_add]
        apply iid_cap_tail _ _ n q hq
        rw [uniform_neighbor_mass]
        exact hgood a ha hb
    _ = ((U.filter fun a=>a∈Bad).card:ℝ)+U.card*z := by
      rw [Finset.sum_add_distrib,Finset.sum_boole]
      simp
    _ ≤ _ := by
      have hh : (U.filter fun a=>a∈Bad).card ≤ Bad.card :=
        Finset.card_le_card (by intro a ha;exact (Finset.mem_filter.mp ha).2)
      have hh' : ((U.filter fun a=>a∈Bad).card:ℝ) ≤ Bad.card := by exact_mod_cast hh
      exact add_le_add hh' le_rfl

end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A : Type*} [Fintype A]

lemma uniform_row_source (C : Finset A) (hC : C.Nonempty) {n : ℕ}
    (P : (Fin n→A)→Prop) :
    eventMass (iid (uniformOn C hC) (Fin n))
      (Finset.univ.filter fun row=>(∀i,row i∈C)∧P row)=
    eventMass (iid (uniformOn C hC) (Fin n)) (Finset.univ.filter P) := by
  simp only [eventMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hs : ∀i,row i∈C
  · simp [hs]
  · rw [iid_uniformOn]
    simp [hs]

lemma finite_table_failure (p : Law A) (E : Finset A) (N : ℕ) :
    map (iid p (Fin N)) (firstAccepted E (n := N)) none ≤
      Real.exp (-eventMass p E*N) := by
  rw [first_law_none]
  have hh : 1-eventMass p E ≤ Real.exp (-eventMass p E) := by
    linarith [Real.add_one_le_exp (-eventMass p E)]
  calc
    _ ≤ (Real.exp (-eventMass p E))^N :=
      pow_le_pow_left₀ (sub_nonneg.mpr (eventMass_le_one p E)) hh N
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1;ring

theorem uniform_table_failure (C W : Finset A) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCW : C⊆W) (n N : ℕ) (E : Finset (Fin n→A))
    (hsource : ∀row∈E,∀i,row i∈C)
    (hE : (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n)) E)
    (q : ℝ) (hN : q ≤ (9:ℝ)/10*((C.card:ℝ)/W.card)^n*N) :
    map (iid (iid (uniformOn W hW) (Fin n)) (Fin N))
      (firstAccepted E (n := N)) none ≤ Real.exp (-q) := by
  have he := eventMass_scaling (iid (uniformOn W hW) (Fin n))
    (iid (uniformOn C hC) (Fin n)) E (((C.card:ℝ)/W.card)^n)
    (fun row hr=>uniformOn_row_scaling C W hC hW hCW row (hsource row hr))
  have hm : (9:ℝ)/10*((C.card:ℝ)/W.card)^n ≤
      eventMass (iid (uniformOn W hW) (Fin n)) E := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hE
      (by positivity : (0:ℝ) ≤ ((C.card:ℝ)/W.card)^n)
    simpa [mul_comm] using hh
  apply (finite_table_failure _ E N).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg N)
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_FreshValidation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A : Type*} [Fintype A]

lemma pair_success_mass (p : Law A) (P Q : A→Prop)
    (hP : eventMass p (Finset.univ.filter fun a=>¬P a) ≤ 1/20)
    (hQ : eventMass p (Finset.univ.filter fun a=>¬Q a) ≤ 1/20) :
    (9:ℝ)/10 ≤ eventMass p (Finset.univ.filter fun a=>P a∧Q a) := by
  have hb : (1:ℝ) ≤ eventMass p (Finset.univ.filter fun a=>P a∧Q a)+
      eventMass p (Finset.univ.filter fun a=>¬P a)+
      eventMass p (Finset.univ.filter fun a=>¬Q a) := by
    calc
      1 = ∑a,p a := p.sum_one.symm
      _ ≤ ∑a,((if P a∧Q a then p a else 0)+(if ¬P a then p a else 0)+
          (if ¬Q a then p a else 0)) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq,p.nonneg a]
      _ = _ := by simp only [Finset.sum_add_distrib,eventMass,Finset.sum_filter]
  linarith

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] in
lemma expected_rejected_card (R : A→B→Prop) (S : Finset A) (C : Finset B)
    (hC : C.Nonempty) (n : ℕ) (hn : 0 < n) (q : ℝ) (hq : 0 < q) :
    (∑row,iid (uniformOn C hC) (Fin n) row*((rejected R S q row).card:ℝ)) ≤
      (5*q/C.card)*(∑a∈S,((C.filter (R a)).card:ℝ)) := by
  simp only [rejected]
  rw [expected_filter_card,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have he : (1/(5*q))*(n:ℝ)=(n:ℝ)/(5*q) := by ring
  have hh := iid_test_rejection (uniformOn C hC) (neighbors R a) n hn (1/(5*q)) (by positivity)
  rw [he,uniform_neighbor_mass] at hh
  convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv,one_mul,inv_inv]; ring)

omit [Fintype A] in
lemma capture_partition (R : A→B→Prop) (S U : Finset A) (hSU : S⊆U)
    {n : ℕ} (q : ℝ) (row : Fin n→B) :
    (S∩cap R U q row).card+(rejected R S q row).card=S.card := by
  have he : S∩cap R U q row=S.filter fun a=>hits (neighbors R a) row < (n:ℝ)/(5*q) := by
    ext a
    simp only [Finset.mem_inter,cap,Finset.mem_filter]
    constructor
    · rintro ⟨ha,_,hw⟩;exact ⟨ha,hw⟩
    · rintro ⟨ha,hw⟩;exact ⟨ha,hSU ha,hw⟩
  rw [he,rejected]
  simpa only [not_lt] using (Finset.card_filter_add_card_filter_not (s := S) (fun a=>hits (neighbors R a) row < (n:ℝ)/(5*q)))

omit [Fintype A] in
theorem validationRows_mass (R : A→B→Prop) (S U : Finset A) (hS : S.Nonempty) (hSU : S⊆U)
    (C : Finset B) (hC : C.Nonempty) (n : ℕ) (hn : 0 < n) (q M : ℝ) (hq : 0 < q) (hM : 0 < M)
    (hmean : ∑row,iid (uniformOn C hC) (Fin n) row*((cap R U q row).card:ℝ) ≤ M/20)
    (hsparse : (5*q/C.card)*(∑a∈S,((C.filter (R a)).card:ℝ)) ≤ (S.card:ℝ)/200) :
    (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n)) (validationRows R S U C n q M) := by
  have he := uniform_row_source C hC (fun row : Fin n→B=>
    ((cap R U q row).card:ℝ) ≤ M ∧ (9:ℝ)/10*S.card ≤ (S∩cap R U q row).card)
  have he' : eventMass (iid (uniformOn C hC) (Fin n)) (validationRows R S U C n q M)=
      eventMass (iid (uniformOn C hC) (Fin n)) (Finset.univ.filter fun row=>
      ((cap R U q row).card:ℝ) ≤ M ∧ (9:ℝ)/10*S.card ≤ (S∩cap R U q row).card) := by
    convert he using 1 <;> congr 1 <;> ext row <;> simp only [validationRows,Finset.mem_filter]
  rw [he']
  apply pair_success_mass
  · have hh := event_markov (iid (uniformOn C hC) (Fin n))
      (fun row=>((cap R U q row).card:ℝ)) (fun _=>Nat.cast_nonneg _) M
      (Finset.univ.filter fun row=>¬((cap R U q row).card:ℝ) ≤ M)
      (fun row hr=>(lt_of_not_ge (Finset.mem_filter.mp hr).2).le)
    apply (mul_le_mul_iff_of_pos_left hM).mp
    exact hh.trans (by simpa [div_eq_mul_inv] using hmean)
  · have hs : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hh := event_markov (iid (uniformOn C hC) (Fin n))
      (fun row=>((rejected R S q row).card:ℝ)) (fun _=>Nat.cast_nonneg _) (S.card/10)
      (Finset.univ.filter fun row=>¬(9:ℝ)/10*S.card ≤ (S∩cap R U q row).card)
      (by
        intro row hr
        have hg := (Finset.mem_filter.mp hr).2
        have hp : ((S∩cap R U q row).card:ℝ)+(rejected R S q row).card=S.card := by
          exact_mod_cast capture_partition R S U hSU q row
        linarith)
    have hb := hh.trans ((expected_rejected_card R S C hC n hn q hq).trans hsparse)
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0:ℝ)<S.card/10)).mp
    nlinarith

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CapDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

lemma cap_subset (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    cap R U q row⊆U := Finset.filter_subset _ _

end SharpRamseyFive.ReverseCap

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SequentialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma adaptiveLaw_first (p : Law α) (next : α→Law β) :
    first (adaptiveLaw p next)=p := by
  apply Law.ext
  funext a
  change (∑b,p a*next a b)=p a
  rw [←Finset.mul_sum,(next a).sum_one,mul_one]

theorem adaptive_option_failure (p : Law (Option α))
    (next : Option α→Law (Option β)) (ε₁ ε₂ : ℝ) (hε₂ : 0≤ε₂)
    (hfirst : p none≤ε₁) (hnext : ∀a,0 < p (some a) → next (some a) none≤ε₂) :
    eventMass (adaptiveLaw p next)
      (Finset.univ.filter fun ab=>ab.1=none ∨ ab.2=none) ≤ ε₁+ε₂ := by
  have hinner (a : Option α) (ha : 0 < p a) :
      (∑b : Option β,if a=none ∨ b=none then next a b else 0) ≤
        (if a=none then 1 else 0)+ε₂ := by
    cases a with
    | none => simpa only [true_or,ite_true] using
        (show (∑b,next none b)≤1+ε₂ by rw [(next none).sum_one];linarith)
    | some a => simpa using hnext a ha
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a (_ : a∈Finset.univ)=>
    show p a*(∑b : Option β,if a=none ∨ b=none then next a b else 0) ≤
      p a*((if a=none then 1 else 0)+ε₂) from by
      by_cases hz : p a=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hinner a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz))) (p.nonneg a))
  have hl : eventMass (adaptiveLaw p next)
      (Finset.univ.filter fun ab=>ab.1=none ∨ ab.2=none)=
      ∑a : Option α,p a*(∑b : Option β,if a=none ∨ b=none then next a b else 0) := by
    simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw,
      Finset.mul_sum,mul_ite,mul_zero]
  rw [hl]
  calc
    _ ≤ ∑a : Option α,p a*((if a=none then 1 else 0)+ε₂) := hsum
    _ = p none+ε₂ := by
      simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero]
      rw [←Finset.sum_mul,p.sum_one,one_mul]
      simp
    _ ≤ ε₁+ε₂ := by linarith

end

open MeasureTheory
open scoped Classical BigOperators

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A]

omit [Fintype A] in
lemma uniformCutoff_bound (q : ℝ) (C W : Finset A)
    (hC : C.Nonempty) (hW : W.Nonempty) (n : ℕ) :
    q ≤ (9:ℝ)/10*((C.card:ℝ)/W.card)^n*uniformCutoff q C W n := by
  have hc : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hw : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hp : (0:ℝ) < (9:ℝ)/10*((C.card:ℝ)/W.card)^n := by positivity
  have hh := (div_le_iff₀ hp).mp (Nat.le_ceil (q/((9:ℝ)/10*((C.card:ℝ)/W.card)^n)))
  simpa only [mul_comm,uniformCutoff] using hh

theorem uniform_cutoff_failure (q : ℝ) (C W : Finset A)
    (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W) (n : ℕ)
    (E : Finset (Fin n→A)) (hsource : ∀row∈E,∀i,row i∈C)
    (hE : (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n)) E) :
    map (iid (iid (uniformOn W hW) (Fin n)) (Fin (uniformCutoff q C W n)))
      (firstAccepted E (n := uniformCutoff q C W n)) none ≤ Real.exp (-q) :=
  uniform_table_failure C W hC hW hCW n _ E hsource hE q (uniformCutoff_bound q C W hC hW n)

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionTwoPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Field K] [Finite K] in
lemma density_three_quarters {d : ℕ} (hd : 1 ≤ d) (hq : 3 ≤ Nat.card K) :
    3 / (4 * (Nat.card K : ℝ)) ≤
      (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d := by
  have hm : 0 < Q (Nat.card K) (d-1) := Q_pos _ _
  have hn : 0 < Q (Nat.card K) d := Q_pos _ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [Q_recurrence hd]
  push_cast
  have hq' : (3 : ℝ) ≤ Nat.card K := by exact_mod_cast hq
  have hm' : (1 : ℝ) ≤ Q (Nat.card K) (d-1) := by exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left hm' (by positivity : (0:ℝ) ≤ Nat.card K)
  nlinarith

theorem sparse_half_rectangle_size {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d) (hq3 : 3 ≤ Nat.card K)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V)))
    (hsparse : (incidences A B : ℝ) ≤ (A.card : ℝ) * B.card / (2 * Nat.card K)) :
    (A.card : ℝ) * B.card ≤ 16 * (Nat.card K : ℝ) ^ (d+1) := by
  classical
  let q : ℝ := Nat.card K
  let v : ℝ := (A.card : ℝ) * B.card
  let p : ℝ := (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 3 / (4*q) ≤ p := density_three_quarters hd hq3
  have hpv := mul_le_mul_of_nonneg_right hp hv
  have hlow : v / (4*q) ≤ p*v - incidences A B := by
    change (incidences A B : ℝ) ≤ v / (2*q) at hsparse
    have he : (3 / (4*q)) * v = 3 * (v / (4*q)) := by field_simp
    have he2 : v / (2*q) = 2 * (v / (4*q)) := by field_simp; ring
    rw [he] at hpv
    rw [he2] at hsparse
    linarith
  have hm : |(incidences A B : ℝ) - p*v| ≤ Real.sqrt (q^(d-1)*v) := by
    simpa only [p, q, v, mul_assoc] using incidence_mixing hdim hd A B
  have habs : |(incidences A B : ℝ) - p*v| = p*v - incidences A B := by
    rw [abs_of_nonpos (show (incidences A B : ℝ) - p*v ≤ 0 by
      have hnonneg : 0 ≤ v / (4*q) := by positivity
      linarith)]
    ring
  rw [habs] at hm
  have hs : v / (4*q) ≤ Real.sqrt (q^(d-1)*v) := hlow.trans hm
  have hs2 := (Real.le_sqrt (by positivity) (by positivity)).mp hs
  have he : (v / (4*q))^2 * (16*q^2) = v^2 := by field_simp; ring
  have hm2 := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ 16*q^2 by positivity)
  rw [he] at hm2
  have hexp : q^(d-1)*v*(16*q^2) = (16*q^(d+1))*v := by
    have hd' : d-1 + 2 = d+1 := by omega
    rw [← hd', pow_add]
    ring
  rw [hexp, pow_two] at hm2
  by_cases hv0 : v = 0
  · change v ≤ _
    rw [hv0]
    positivity
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hv (Ne.symm hv0))).mp hm2

end SharpRamseyFive.ProjectiveIncidence

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PublicCapLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma publicCapLaw_none (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    publicCapLaw R S U C W hW n q M none=
      map (iid (iid (uniformOn W hW) (Fin n)) (Fin (uniformCutoff q C W n)))
        (firstAccepted (validationRows R S U C n q M)) none := by
  classical
  simp [publicCapLaw,map,Fintype.sum_option]

lemma publicCapLaw_failure (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W)
    (n : ℕ) (q M : ℝ)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows R S U C n q M)) :
    publicCapLaw R S U C W hW n q M none≤Real.exp (-q) := by
  rw [publicCapLaw_none]
  exact uniform_cutoff_failure q C W hC hW hCW n _
    (fun row hr=>(Finset.mem_filter.mp hr).2.1) hE

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AmbientPublicTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma cap_inter (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    U∩cap R Finset.univ q row=cap R U q row := by
  ext a
  simp [cap]

lemma ambientCapLaw_none (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    ambientCapLaw R S U C W hW n q M none=publicCapLaw R S U C W hW n q M none := by
  simp [ambientCapLaw,publicCapLaw,map,Fintype.sum_option]

lemma ambientCapLaw_positive (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ)
    (Y : Finset A) (hY : 0<ambientCapLaw R S U C W hW n q M (some Y)) :
    ValidCap S U M (U∩Y) := by
  obtain ⟨row,hr,he⟩ := map_positive _ _ _ hY
  cases row with
  | none => simp at he
  | some row =>
    have he' : cap R Finset.univ q row=Y := Option.some.inj he
    subst Y
    rw [cap_inter]
    obtain ⟨t,_,ht⟩ := map_positive _ _ _ hr
    obtain ⟨i,hi,hm⟩ := firstAccepted_index _ _ ht
    exact ⟨cap_subset _ _ _ _,(Finset.mem_filter.mp hm).2.2⟩

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_CapNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
lemma ambient_tail (u s q h : ℝ) (hu : 0 < u) (hs : 0 < s) (hq : 0 < q)
    (hh : 20*q*Real.log (u/s) ≤ h) :
    u*Real.exp (-h/(20*q)) ≤ s := by
  have hp : 0 < 20*q := by positivity
  have he : -h/(20*q) ≤ -Real.log (u/s) := by
    have hh' : Real.log (u/s) ≤ h/(20*q) := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
    simpa only [neg_div] using neg_le_neg hh'
  calc
    _ ≤ u*Real.exp (-Real.log (u/s)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hu.le
    _ = s := by rw [Real.exp_neg,Real.exp_log (div_pos hu hs)]; field_simp

lemma captured_cap_budget (G x c a s u q h : ℝ)
    (hG : 0 ≤ G) (hx : 0 < x) (hc : 0 < c) (ha : 0 < a)
    (hs : 0 < s) (hu : 0 < u) (hq : 0 < q)
    (hcapture : c*x ≤ a) (hproduct : s*x ≤ 16*G)
    (hh : 20*q*Real.log (u/s) ≤ h) :
    16*G/a+u*Real.exp (-h/(20*q)) ≤ ((320/c+320)*G/x)/20 := by
  have ht := ambient_tail u s q h hu hs hq hh
  have hs' : s ≤ 16*G/x := (le_div_iff₀ hx).mpr hproduct
  have ha' : 16*G/a ≤ 16*G/(c*x) :=
    (div_le_div_iff₀ ha (mul_pos hc hx)).mpr
      (mul_le_mul_of_nonneg_left hcapture (by positivity))
  calc
    _ ≤ 16*G/(c*x)+16*G/x := add_le_add ha' (ht.trans hs')
    _ = _ := by field_simp; ring

lemma rejection_from_capture (e x c a s q : ℝ) (ha : 0 < a) (hs : 0 ≤ s)
    (hcapture : c*x ≤ a) (hsparse : 1000*q*e ≤ c*s*x) :
    (5*q/a)*e ≤ s/200 := by
  have hc := mul_le_mul_of_nonneg_left hcapture hs
  have hh : 1000*q*e ≤ s*a := hsparse.trans (by nlinarith)
  calc
    _ = (5*q*e)/a := by ring
    _ ≤ s/200 := (div_le_iff₀ ha).mpr (by nlinarith)

lemma density_half (e s x c q : ℝ) (he : 0 ≤ e) (hs : 0 ≤ s) (hx : 0 ≤ x)
    (hq : 0 < q) (hc : c ≤ 1) (hsparse : 1000*q*e ≤ c*s*x) :
    e ≤ s*x/(2*q) := by
  have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hs hx)
  have hg : 0 ≤ q*e := mul_nonneg hq.le he
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*q)).mpr
  nlinarith

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PredictorReverseCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma incidences_eq_sum_card (S : Finset (ℙ K V)) (C : Finset (ℙ K (Dual K V))) :
    (incidences S C:ℝ)=∑x∈S,((C.filter (Incident x)).card:ℝ) := by
  rw [incidences_eq_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [incidenceEntry,Finset.sum_boole]

theorem lowIncidence_mass {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (C : Finset (ℙ K (Dual K V))) :
    ((lowIncidence C).card:ℝ)*C.card ≤ 16*(Nat.card K:ℝ)^(d+1) := by
  apply sparse_half_rectangle_size hdim hd hq
  rw [incidences_eq_sum_card]
  calc
    _ ≤ ∑x∈lowIncidence C,(C.card:ℝ)/(2*Nat.card K) :=
      Finset.sum_le_sum fun x hx=>(Finset.mem_filter.mp hx).2
    _ = _ := by simp;ring

theorem expected_projective_cap {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (C : Finset (ℙ K (Dual K V))) (hC : C.Nonempty)
    (U : Finset (ℙ K V)) (n : ℕ) :
    (∑row,iid (uniformOn C hC) (Fin n) row*
      ((cap Incident U (Nat.card K) row).card:ℝ)) ≤
      16*(Nat.card K:ℝ)^(d+1)/C.card +
        U.card*Real.exp (-(n:ℝ)/(20*Nat.card K)) := by
  have hqpos : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hc : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hh := expected_cap_card Incident U (lowIncidence C) C hC n (Nat.card K) hqpos
    (by
      intro x hx hlow
      have hdg : (C.card:ℝ)/(2*Nat.card K) < (C.filter (Incident x)).card := by
        simpa only [lowIncidence,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hlow
      apply (le_div_iff₀ hc).mpr
      calc
        _ = (C.card:ℝ)/(2*Nat.card K) := by ring
        _ ≤ _ := hdg.le)
  have hb := (le_div_iff₀ hc).mpr (lowIncidence_mass hdim hd hq C)
  linarith

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma incidences_eq_sum_card_right (C : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) :
    (incidences C T:ℝ)=∑y∈T,((C.filter fun x=>Incident x y).card:ℝ) := by
  rw [incidences_eq_sum]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [incidenceEntry,Finset.sum_boole]

theorem lowPencil_mass {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (C : Finset (ℙ K V)) :
    ((lowPencil C).card:ℝ)*C.card ≤ 16*(Nat.card K:ℝ)^(d+1) := by
  have hh : (C.card:ℝ)*(lowPencil C).card ≤ 16*(Nat.card K:ℝ)^(d+1) := by
    apply sparse_half_rectangle_size hdim hd hq
    rw [incidences_eq_sum_card_right]
    calc
      _ ≤ ∑y∈lowPencil C,(C.card:ℝ)/(2*Nat.card K) :=
        Finset.sum_le_sum fun y hy=>(Finset.mem_filter.mp hy).2
      _ = _ := by simp; ring
  simpa only [mul_comm] using hh

theorem expected_dual_cap {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (C : Finset (ℙ K V)) (hC : C.Nonempty)
    (U : Finset (ℙ K (Dual K V))) (n : ℕ) :
    (∑row,iid (uniformOn C hC) (Fin n) row*
      ((cap (fun y x=>Incident x y) U (Nat.card K) row).card:ℝ)) ≤
      16*(Nat.card K:ℝ)^(d+1)/C.card +
        U.card*Real.exp (-(n:ℝ)/(20*Nat.card K)) := by
  have hqpos : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hc : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hh := expected_cap_card (fun y x=>Incident x y) U (lowPencil C) C hC n (Nat.card K) hqpos
    (by
      intro y hy hlow
      have hdeg : (C.card:ℝ)/(2*Nat.card K) < (C.filter fun x=>Incident x y).card := by
        simpa only [lowPencil,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hlow
      apply (le_div_iff₀ hc).mpr
      calc
        _ = (C.card:ℝ)/(2*Nat.card K) := by ring
        _ ≤ _ := hdeg.le)
  have hb := (le_div_iff₀ hc).mpr (lowPencil_mass hdim hd hq C)
  linarith

end
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem geometric_validation_mass {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (X C : Finset (ℙ K (Dual K V))) (hC : C.Nonempty) (hCX : C⊆X)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hcapture : c*X.card ≤ C.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences S X ≤ c*S.card*X.card)
    (n : ℕ) (hn : 0 < n)
    (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card) ≤ n) :
    (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows Incident S U C n (Nat.card K)
        ((320/c+320)*(Nat.card K:ℝ)^(d+1)/X.card)) := by
  have hqpos : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hCpos : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hXpos : (0:ℝ) < X.card := by exact_mod_cast Finset.card_pos.mpr (hC.mono hCX)
  have hSpos : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hUpos : (0:ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr (hS.mono hSU)
  have hprod := sparse_half_rectangle_size hdim hd hq S X
    (density_half (incidences S X) S.card X.card c (Nat.card K)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hqpos hc1 hsparse)
  have hm := (expected_projective_cap hdim hd hq C hC U n).trans
    (captured_cap_budget ((Nat.card K:ℝ)^(d+1)) X.card c C.card S.card U.card (Nat.card K) n
      (by positivity) hXpos hc hCpos hSpos hUpos hqpos hcapture hprod hlen)
  apply validationRows_mass Incident S U hS hSU C hC n hn (Nat.card K) _ hqpos (by positivity) hm
  have hsum : (∑a∈S,((C.filter (Incident a)).card:ℝ)) ≤ (incidences S X:ℝ) := by
    rw [incidences_eq_sum_card]
    apply Finset.sum_le_sum
    intro a ha
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hCX)
  apply rejection_from_capture _ _ c _ _ _ hCpos (Nat.cast_nonneg _) hcapture
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hsparse

theorem geometric_dual_validation_mass {d : ℕ} (hdim : finrank K V=d+1) (hd : 1 ≤ d)
    (hq : 3 ≤ Nat.card K) (S U : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hSU : S⊆U)
    (X C : Finset (ℙ K V)) (hC : C.Nonempty) (hCX : C⊆X)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hcapture : c*X.card ≤ C.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences X S ≤ c*S.card*X.card)
    (n : ℕ) (hn : 0 < n)
    (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card) ≤ n) :
    (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows (fun y x=>Incident x y) S U C n (Nat.card K)
        ((320/c+320)*(Nat.card K:ℝ)^(d+1)/X.card)) := by
  have hqpos : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hCpos : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hXpos : (0:ℝ) < X.card := by exact_mod_cast Finset.card_pos.mpr (hC.mono hCX)
  have hSpos : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hUpos : (0:ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr (hS.mono hSU)
  have hdensity : (incidences X S:ℝ) ≤ X.card*S.card/(2*(Nat.card K)) := by
    have hh := density_half (incidences X S) S.card X.card c (Nat.card K)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hqpos hc1 hsparse
    simpa only [mul_comm] using hh
  have hprod : (S.card:ℝ)*X.card ≤ 16*(Nat.card K:ℝ)^(d+1) := by
    simpa only [mul_comm] using sparse_half_rectangle_size hdim hd hq X S hdensity
  have hm := (expected_dual_cap hdim hd hq C hC U n).trans
    (captured_cap_budget ((Nat.card K:ℝ)^(d+1)) X.card c C.card S.card U.card (Nat.card K) n
      (by positivity) hXpos hc hCpos hSpos hUpos hqpos hcapture hprod hlen)
  apply validationRows_mass (fun y x=>Incident x y) S U hS hSU C hC n hn (Nat.card K) _ hqpos (by positivity) hm
  have hsum : (∑y∈S,((C.filter fun x=>Incident x y).card:ℝ)) ≤ (incidences X S:ℝ) := by
    rw [incidences_eq_sum_card_right]
    apply Finset.sum_le_sum
    intro y hy
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hCX)
  apply rejection_from_capture _ _ c _ _ _ hCpos (Nat.cast_nonneg _) hcapture
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hsparse

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoAmbientCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem geometric_two_ambient_caps {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (A UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAU : A⊆UA)
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBU : B⊆UB)
    (W : Finset (ℙ K V)) (hW : W.Nonempty) (c : ℝ) (hc : 0 < c) (hc9 : c≤9/10)
    (hcapture : c*A.card≤(A∩W).card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B ≤ c*A.card*B.card)
    (nA nB : ℕ) (hnA : 0<nA) (hnB : 0<nB)
    (hlenA : 20*(Nat.card K:ℝ)*Real.log ((UA.card:ℝ)/A.card)≤nA)
    (hlenB : 20*(Nat.card K:ℝ)*Real.log ((UB.card:ℝ)/B.card)≤nB) :
    let q : ℝ := Nat.card K
    let MA := (320/((9:ℝ)/10)+320)*q^(d+1)/B.card
    let MB := (320/c+320)*q^(d+1)/A.card
    let firstCap := ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB
    let p := adaptiveLaw firstCap (nextAmbientCapLaw A UA B UB hB nA q MA MB)
    eventMass p (Finset.univ.filter fun caps=>caps.1=none ∨ caps.2=none)≤2*Real.exp (-q) ∧
    first p=firstCap ∧
    (∀Y,0 < firstCap (some Y) → ValidCap B UB MB (UB∩Y)) ∧
    (∀Y Z,0 < p (some Y,some Z) → ValidCap B UB MB (UB∩Y) ∧ ValidCap A UA MA (UA∩Z)) := by
  dsimp only
  let q : ℝ := Nat.card K
  let MA := (320/((9:ℝ)/10)+320)*q^(d+1)/B.card
  let MB := (320/c+320)*q^(d+1)/A.card
  let firstCap := ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB
  let next := nextAmbientCapLaw A UA B UB hB nA q MA MB
  have hC : (A∩W).Nonempty := by
    apply Finset.card_pos.mp
    have ha : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
    have : (0:ℝ)<(A∩W).card := lt_of_lt_of_le (mul_pos hc ha) hcapture
    exact_mod_cast this
  have hc1 : c≤1 := by linarith
  have hfirst : firstCap none≤Real.exp (-q) := by
    rw [ambientCapLaw_none]
    apply publicCapLaw_failure _ _ _ _ _ hC hW Finset.inter_subset_right
    apply geometric_dual_validation_mass hdim hd hq B UB hB hBU A (A∩W) hC
      Finset.inter_subset_left c hc hc1 hcapture _ nB hnB hlenB
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hsparse
  have hgood (Y) (hY : 0 < firstCap (some Y)) : ValidCap B UB MB (UB∩Y) :=
    ambientCapLaw_positive _ _ _ _ _ _ _ _ _ _ hY
  have hsparse' : 1000*q*incidences A B≤(9:ℝ)/10*A.card*B.card := by
    have hh := mul_le_mul_of_nonneg_right hc9
      (show (0:ℝ)≤(A.card:ℝ)*B.card by positivity)
    dsimp [q]
    nlinarith
  have hnext (Y) (hY : 0 < firstCap (some Y)) : next (some Y) none≤Real.exp (-q) := by
    have hvalid := hgood Y hY
    dsimp only [next,nextAmbientCapLaw]
    rw [dite_eq_left hvalid]
    rw [ambientCapLaw_none]
    apply publicCapLaw_failure _ _ _ _ _ (hvalid.source_nonempty hB) _ Finset.inter_subset_right
    exact geometric_validation_mass hdim hd hq A UA hA hAU B (B∩(UB∩Y))
      (hvalid.source_nonempty hB) Finset.inter_subset_left ((9:ℝ)/10)
      (by norm_num) (by norm_num) hvalid.2.2 hsparse' nA hnA hlenA
  refine ⟨?_,adaptiveLaw_first _ _,hgood,?_⟩
  · have hh := adaptive_option_failure firstCap next (Real.exp (-q)) (Real.exp (-q))
      (Real.exp_pos _).le hfirst hnext
    simpa only [two_mul] using hh
  · intro Y Z hYZ
    change 0<firstCap (some Y)*next (some Y) (some Z) at hYZ
    have hypos : 0 < firstCap (some Y) := by
      by_contra hh
      have hz : firstCap (some Y)=0 := le_antisymm (le_of_not_gt hh) (firstCap.nonneg _)
      rw [hz,zero_mul] at hYZ
      exact lt_irrefl _ hYZ
    have hzpos : 0 < next (some Y) (some Z) := by
      by_contra hh
      have hz : next (some Y) (some Z)=0 := le_antisymm (le_of_not_gt hh) ((next _).nonneg _)
      rw [hz,mul_zero] at hYZ
      exact lt_irrefl _ hYZ
    have hvalid := hgood Y hypos
    refine ⟨hvalid,?_⟩
    dsimp only [next,nextAmbientCapLaw] at hzpos
    rw [dite_eq_left hvalid] at hzpos
    exact ambientCapLaw_positive _ _ _ _ _ _ _ _ _ _ hzpos


end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LocalNodeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

lemma pairOptions_none (p : Law (Option α×Option β)) :
    map p pairOptions none=eventMass p (Finset.univ.filter fun z=>z.1=none ∨ z.2=none) := by
  simp only [map,eventMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ _
  cases a <;> cases b <;> simp [pairOptions]

lemma pairOptions_positive (p : Law (Option α×Option β)) (a : α) (b : β)
    (h : 0 < map p pairOptions (some (a,b))) : 0<p (some a,some b) := by
  obtain ⟨⟨a',b'⟩,hh,he⟩ := map_positive p pairOptions _ h
  cases a' <;> cases b' <;> simp [pairOptions] at he
  obtain ⟨rfl,rfl⟩ := he
  exact hh
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma producedPairLaw_spec_oai (hd : finrank K V=5) (hq : 3≤Nat.card K)
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hAU : A⊆UA) (hBU : B⊆UB)
    (c M : ℝ) (hc : 0 < c) (hc9 : c≤9/10)
    (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B ≤ c*A.card*B.card) :
    producedPairLaw A UA B UB hB c (some W) none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
    ∀Y Z,0<producedPairLaw A UA B UB hB c (some W) (some (Y,Z))→
      ValidCap B UB ((320/c+320)*(Nat.card K:ℝ)^5/A.card) (UB∩Y) ∧
      ValidCap A UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card) (UA∩Z) := by
  have hW : W.Nonempty := (hcap.nonempty hA hc).mono Finset.inter_subset_right
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
  have hlenA := reverseLength_spec (Nat.card K) (Real.log ((UA.card:ℝ)/A.card)) hq1
    (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hA.card_pos)).mpr
      (by simpa only [one_mul] using (show (A.card:ℝ)≤UA.card from by exact_mod_cast Finset.card_le_card hAU))))
  have hlenB := reverseLength_spec (Nat.card K) (Real.log ((UB.card:ℝ)/B.card)) hq1
    (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hB.card_pos)).mpr
      (by simpa only [one_mul] using (show (B.card:ℝ)≤UB.card from by exact_mod_cast Finset.card_le_card hBU))))
  have hh := geometric_two_ambient_caps (d:=4) hd (by norm_num) hq A UA hA hAU B UB hB hBU
    W hW c hc hc9 (by simpa only [Finset.inter_comm] using hcap.2.2) hsparse
    (reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card)))
    (reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card)))
    hlenA.1 hlenB.1 hlenA.2.1 hlenB.2.1
  dsimp only [producedPairLaw]
  rw [dite_eq_left hW]
  exact ⟨by rw [pairOptions_none];exact hh.1,fun Y Z hp=>hh.2.2.2 Y Z (pairOptions_positive _ Y Z hp)⟩

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec_oai.{u_1, u_2} := @OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec_oai.{u_1, u_2}
