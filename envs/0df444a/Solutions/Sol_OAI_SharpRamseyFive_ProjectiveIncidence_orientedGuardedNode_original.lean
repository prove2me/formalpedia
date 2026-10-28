-- Prove2me | solution 1 for OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:33:49.809136+00:00
-- url     : https://prove2.me/submissions/318d3c9c-e368-461d-98ff-59d629d71a6e

import Mathlib
import Definitions.Def_OAIQ060R004

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

lemma first_law_zero_some (p : Law α) (E : Finset α) (a : α) :
    map (iid p (Fin 0)) (firstAccepted E (n := 0)) (some a)=0 := by
  simp [map,firstAccepted]

lemma first_law_none (p : Law α) (E : Finset α) (n : ℕ) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) none=(1-eventMass p E)^n := by
  induction n with
  | zero => simpa using first_law_zero_none p E
  | succ n hn =>
    rw [first_law_succ,hn,pow_succ]
    simp only [Option.some_ne_none,and_false,ite_false,Finset.sum_const_zero,zero_add]
    ring

lemma first_law_some (p : Law α) (E : Finset α) (n : ℕ) (a : α) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) (some a)=
      (if a∈E then p a else 0)*(∑ i∈Finset.range n,(1-eventMass p E)^i) := by
  induction n with
  | zero => simpa using first_law_zero_some p E a
  | succ n hn =>
    rw [first_law_succ,hn]
    have he : (∑ b,if b∈E ∧ some b=some a then p b else 0)=if a∈E then p a else 0 := by
      classical
      simp only [Option.some.injEq]
      simp only [and_comm,ite_and]
      simp
    rw [he,Finset.sum_range_succ']
    simp only [pow_succ',←Finset.mul_sum,pow_zero]
    ring

lemma acceptance_geom_sum (p : Law α) (E : Finset α) (n : ℕ) :
    eventMass p E*(∑ i∈Finset.range n,(1-eventMass p E)^i)=1-(1-eventMass p E)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ,mul_add,hn,pow_succ]
    ring

theorem first_success_law (p : Law α) (E : Finset α) (n : ℕ) (hn : 0<n)
    (hE : 0<eventMass p E) (a : α) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) (some a) /
      (1-map (iid p (Fin n)) (firstAccepted E (n := n)) none)=
      (if a∈E then p a/eventMass p E else 0) := by
  have hq : 0≤1-eventMass p E := sub_nonneg.mpr (eventMass_le_one p E)
  have hq1 : 1-eventMass p E<1 := by linarith
  have hp : (1-eventMass p E)^n<1 := pow_lt_one₀ hq hq1 (Nat.ne_of_gt hn)
  have hd : 1-(1-eventMass p E)^n≠0 := by linarith
  rw [first_law_some,first_law_none]
  by_cases ha : a∈E
  · rw [ite_eq_left ha,ite_eq_left ha]
    have hg := acceptance_geom_sum p E n
    apply (div_eq_div_iff hd (ne_of_gt hE)).mpr
    nlinarith [congrArg (fun z : ℝ => p a*z) hg]
  · simp [ha]

theorem first_success_density (p : Law α) (E : Finset α) (n : ℕ) (hn : 0<n)
    (hE : 0<eventMass p E) (a : α) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) (some a) /
      (1-map (iid p (Fin n)) (firstAccepted E (n := n)) none)≤p a/eventMass p E := by
  rw [first_success_law p E n hn hE]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (p.nonneg a) hE.le

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

lemma first_success_atom_le (p : Law α) (E : Finset α) (n : ℕ) (hn : 0<n)
    (hE : 0<eventMass p E) (a : α) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) (some a)≤p a/eventMass p E := by
  let r := map (iid p (Fin n)) (firstAccepted E (n := n))
  have hd := first_success_density p E n hn hE a
  have hs : 0<1-r none := by
    dsimp [r]
    rw [first_law_none]
    have hq : 0≤1-eventMass p E := sub_nonneg.mpr (eventMass_le_one p E)
    have hq1 : 1-eventMass p E<1 := by linarith
    have hp := pow_lt_one₀ hq hq1 (Nat.ne_of_gt hn)
    linarith
  change r (some a)/(1-r none)≤p a/eventMass p E at hd
  have hd' := (div_le_iff₀ hs).mp hd
  have hn0 := r.nonneg none
  have hpa : 0≤p a/eventMass p E := div_nonneg (p.nonneg a) hE.le
  change r (some a)≤_
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

theorem first_success_scaled (p r : Law α) (E : Finset α) (s : ℝ) (hs : 0 < s)
    (hscale : ∀ a∈E,p a=s*r a) (N : ℕ) (hN : 0<N)
    (hE : 0<eventMass r E) (a : α) :
    map (iid p (Fin N)) (firstAccepted E (n := N)) (some a) ≤ r a/eventMass r E := by
  by_cases ha : a∈E
  · have he := eventMass_scaling p r E s hscale
    have hpE : 0<eventMass p E := by rw [he]; exact mul_pos hs hE
    have hh := first_success_atom_le p E N hN hpE a
    rw [he,hscale a ha] at hh
    have heq : s*r a/(s*eventMass r E)=r a/eventMass r E := by field_simp
    rwa [heq] at hh
  · rw [first_law_some]
    simp only [ha,ite_false,zero_mul]
    exact div_nonneg (r.nonneg a) hE.le

lemma first_success_scaled_bad (p r : Law α) (E Bad : Finset α) (s : ℝ) (hs : 0 < s)
    (hscale : ∀ a∈E,p a=s*r a) (N : ℕ) (hN : 0<N) (hE : 0<eventMass r E) :
    eventMass (map (iid p (Fin N)) (firstAccepted E (n := N))) (Bad.image some) ≤
      eventMass r Bad/eventMass r E := by
  rw [eventMass,Finset.sum_image (by intro a _ b _ h; exact Option.some.inj h)]
  calc
    _ ≤ ∑ a∈Bad,r a/eventMass r E := Finset.sum_le_sum fun a _ =>
      first_success_scaled p r E s hs hscale N hN hE a
    _ = _ := by rw [←Finset.sum_div]; rfl

theorem uniform_proposal_bad (A W : Finset α) (hA : A.Nonempty) (hW : W.Nonempty)
    (hAW : A⊆W) (h N : ℕ) (hN : 0<N) (E Bad : Finset (Fin h → α))
    (hsource : ∀ x∈E,∀ i,x i∈A) (hE : 0<eventMass (iid (uniformOn A hA) (Fin h)) E) :
    eventMass (map (iid (iid (uniformOn W hW) (Fin h)) (Fin N))
      (firstAccepted E (n := N))) (Bad.image some) ≤
      eventMass (iid (uniformOn A hA) (Fin h)) Bad /
        eventMass (iid (uniformOn A hA) (Fin h)) E := by
  have hcA : (0:ℝ)<A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hcW : (0:ℝ)<W.card := by exact_mod_cast Finset.card_pos.mpr hW
  have hh := first_success_scaled_bad _ _ E Bad (((A.card:ℝ)/W.card)^h) (by positivity)
    (fun x hx => uniformOn_row_scaling A W hA hW hAW x (hsource x hx)) N hN hE
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp only [Finset.mem_image]

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

lemma eventMass_filter_mono (p : Law A) (P Q : A→Prop) (h : ∀a,P a → Q a) :
    eventMass p (Finset.univ.filter P) ≤ eventMass p (Finset.univ.filter Q) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ a,h a (Finset.mem_filter.mp ha).2⟩)
    (fun a _ _=>p.nonneg a)

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

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma uniform_source_fraction (A X H : Finset α) (hA : A.Nonempty) (hAX : A⊆X)
    (c : ℝ) (hc : 0 < c) (hsize : c*X.card≤A.card) :
    eventMass (uniformOn A hA) H≤((H∩X).card:ℝ)/(c*X.card) := by
  have hX : X.Nonempty := hA.mono hAX
  have hnA : (0:ℝ)<A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hnX : (0:ℝ)<X.card := by exact_mod_cast Finset.card_pos.mpr hX
  have hcard : ((H∩A).card:ℝ)≤(H∩X).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl H) hAX)
  rw [uniformOn_mass]
  exact div_le_div₀ (by positivity) hcard (by positivity) hsize

theorem fresh_test_domination (A X W H : Finset α) (hA : A.Nonempty) (hW : W.Nonempty)
    (hAW : A⊆W) (hAX : A⊆X) (q c : ℝ) (hq : 0<q) (hc : 0 < c)
    (hsize : c*X.card≤A.card) (h N : ℕ) (hh : 0<h) (hN : 0<N)
    (E : Finset (Fin h → α)) (hsource : ∀ x∈E,∀ i,x i∈A)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn A hA) (Fin h)) E) :
    eventMass (map (iid (iid (uniformOn W hW) (Fin h)) (Fin N))
      (firstAccepted E (n := N)))
      ((Finset.univ.filter fun x => (1/(5*q))*h≤hits H x).image some) ≤
      (50*q/(9*c))*(((H∩X).card:ℝ)/X.card) := by
  let b : ℝ := 1/(5*q)
  have hb : 0<b := by dsimp [b]; positivity
  have hepos : 0<eventMass (iid (uniformOn A hA) (Fin h)) E := by linarith
  have hp := uniform_proposal_bad A W hA hW hAW h N hN E
    (Finset.univ.filter fun x => b*h≤hits H x) hsource hepos
  have hi := iid_test_rejection (uniformOn A hA) H h hh b hb
  have hs := uniform_source_fraction A X H hA hAX c hc hsize
  have hnum : eventMass (iid (uniformOn A hA) (Fin h))
        (Finset.univ.filter fun x => b*h≤hits H x) ≤
      (((H∩X).card:ℝ)/(c*X.card))/b :=
    hi.trans (div_le_div_of_nonneg_right hs hb.le)
  have hd := div_le_div₀ (by positivity) hnum (by norm_num : (0:ℝ)<9/10) hE
  have hnX : (0:ℝ)<X.card := by exact_mod_cast Finset.card_pos.mpr (hA.mono hAX)
  have heq : ((((H∩X).card:ℝ)/(c*X.card))/b)/(9/10)=
      (50*q/(9*c))*(((H∩X).card:ℝ)/X.card) := by
    dsimp [b]
    field_simp
    ring
  have hfin := hp.trans (hd.trans_eq heq)
  convert hfin using 1
  all_goals try with_reducible_and_instances rfl

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
lemma uniformCutoff_pos (q : ℝ) (hq : 0 < q) (C W : Finset A)
    (hC : C.Nonempty) (hW : W.Nonempty) (n : ℕ) :
    0 < uniformCutoff q C W n := by
  have hc : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hw : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
  apply Nat.ceil_pos.mpr
  positivity

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ProducedCapExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma eventMass_map_filter (p : Law α) (f : α→β) (P : β→Prop) :
    eventMass (map p f) (Finset.univ.filter P)=
    eventMass p (Finset.univ.filter fun a=>P (f a)) := by
  simpa only [eventMass,Finset.sum_filter,mul_ite,mul_one,mul_zero] using
    sum_map p f (fun b=>if P b then (1:ℝ) else 0)
end SharpRamseyFive.FiniteEntropy

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

lemma piLaw_eval (p : ∀i,Law (β i)) (i : ι) : map (piLaw p) (fun x=>x i)=p i := by
  apply Law.ext
  funext a
  have hm := piLaw_eval_expectation p i (fun b=>if b=a then 1 else 0)
  simpa only [map,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hm
end

open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

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

theorem ambientCapLaw_domination (R : A→B→Prop) (S U : Finset A)
    (C X W : Finset B) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCW : C⊆W) (hCX : C⊆X) (n : ℕ) (hn : 0<n)
    (q c M : ℝ) (hq : 0<q) (hc : 0 < c) (hsize : c*X.card≤C.card)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows R S U C n q M)) (a : A) :
    eventMass (ambientCapLaw R S U C W hW n q M) (Finset.univ.filter (Excludes a))≤
      (50*q/(9*c))*(((X.filter (R a)).card:ℝ)/X.card) := by
  have heq : eventMass (ambientCapLaw R S U C W hW n q M)
      (Finset.univ.filter (Excludes a))=
      freshRejection (fun b a=>R a b) q W hW n (uniformCutoff q C W n)
        (validationRows R S U C n q M) a := by
    unfold ambientCapLaw freshRejection
    rw [eventMass_map_filter]
    apply congrArg (eventMass _)
    apply Finset.ext
    intro row
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,Finset.mem_image]
    cases row with
    | none => simp only [Option.map_none,Excludes,Option.some_ne_none,and_false,exists_false]
    | some row =>
      simp only [Option.map_some,Excludes,Finset.mem_filter,cap,Finset.mem_univ,true_and,
        not_lt,Option.some.injEq,exists_eq_right]
      change hits (neighbors R a) row ≥ (n:ℝ)/(5*q) ↔ _
      rw [show (n:ℝ)/(5*q)=(1/(5*q))*n by ring]
      rfl
  rw [heq]
  have h := fresh_test_domination C X W (Finset.univ.filter (R a)) hC hW hCW hCX
    q c hq hc hsize n (uniformCutoff q C W n) hn (uniformCutoff_pos q hq C W hC hW n)
    (validationRows R S U C n q M) (fun row hr=>(Finset.mem_filter.mp hr).2.1) hE
  have he : (Finset.univ.filter (R a))∩X=X.filter (R a) := by ext b;simp [and_comm]
  simpa only [freshRejection,he] using h

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FreshPublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*}
lemma acceptedIndex_decode {n : ℕ} (E : Finset A) (t : Fin n→A) :
    Option.map t (acceptedIndex E t)=firstAccepted E t :=
  Classical.choose_spec (exists_accepted_index E t)
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma freshEncoded_decoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q) :
    Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t)=
      Option.map (cap R Finset.univ q)
        (firstAccepted (validationRows R S U C n q M)
          (t ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩)) := by
  unfold freshEncoded freshDecoded
  rw [←acceptedIndex_decode]
  simp only [Option.map_map]
  rfl

theorem fresh_public_law (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    map (freshTapeLaw W hW n q)
      (fun t=>Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t))=
    ambientCapLaw R S U C W hW n q M := by
  let m : Fin (W.card+1) := ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩
  have hm := piLaw_eval (fun m : Fin (W.card+1)=>
    iid (iid (uniformOn W hW) (Fin n)) (Fin (cardCutoff q m W.card n))) m
  have ht := congrArg (fun p=>map (map p (firstAccepted (validationRows R S U C n q M)))
    (Option.map (cap R Finset.univ q))) hm
  simp only [map_comp] at ht
  unfold ambientCapLaw
  rw [map_comp]
  calc
    _ = map (freshTapeLaw W hW n q) (fun t=>Option.map (cap R Finset.univ q)
        (firstAccepted (validationRows R S U C n q M) (t m))) := by
      congr 1
      funext t
      exact freshEncoded_decoded R S U C W hCW n q M t
    _ = _ := ht

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_UniversalFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma universalFresh_marginal (H : ℕ) (q : ℝ) (i : FreshIndex B H) :
    map (universalFreshLaw B H q) (fun t=>t i)=freshTapeLaw i.1.1 i.1.2 i.2 q :=
  piLaw_eval _ i

lemma universalFresh_output (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (hCW : C⊆W) (H n : ℕ) (hn : n≤H)
    (q M : ℝ) :
    let i : FreshIndex B H := (⟨W,hW⟩,⟨n,Nat.lt_succ_of_le hn⟩)
    map (universalFreshLaw B H q)
      (fun t=>Option.map (freshDecoded R W n q (t i)) (freshEncoded R S U C W hCW n q M (t i)))=
      ambientCapLaw R S U C W hW n q M := by
  dsimp only
  rw [←fresh_public_law R S U C W hCW hW n q M]
  have hm := universalFresh_marginal (B:=B) H q
    ((⟨W,hW⟩,⟨n,Nat.lt_succ_of_le hn⟩) : FreshIndex B H)
  rw [←hm,map_comp]
  rfl

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PublicComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma map_const (p : Law α) (b : β) : map p (fun _=>b)=pureLaw b := by
  apply Law.ext
  funext x
  by_cases hx : b=x
  · subst x
    simp [map,pureLaw,p.sum_one]
  · simp [map,pureLaw,hx,Ne.symm hx]

lemma adaptive_output_mass (p : Law α) (next : α→Law β) (out : α→β→γ) (c : γ) :
    map (adaptiveLaw p next) (fun z=>out z.1 z.2) c=
      ∑a,p a*map (next a) (out a) c := by
  simp only [map,adaptiveLaw,Fintype.sum_prod_type,Finset.mul_sum,mul_ite,mul_zero]

lemma public_composition (p : Law α) (tape : Law β) (firstOut : α→γ)
    (out : γ→β→δ) (next : γ→Law δ)
    (hm : ∀c,map tape (out c)=next c) :
    map (adaptiveLaw p (fun _=>tape)) (fun z=>out (firstOut z.1) z.2)=
      map (adaptiveLaw (map p firstOut) next) Prod.snd := by
  apply Law.ext
  funext d
  rw [adaptive_output_mass (out:=fun a b=>out (firstOut a) b)]
  have hr := adaptive_output_mass (map p firstOut) next (fun _ x=>x) d
  change map (adaptiveLaw (map p firstOut) next) Prod.snd d = ∑ a, map p firstOut a * map (next a) id d at hr
  simp only [map_id] at hr
  rw [hr,sum_map]
  apply Finset.sum_congr rfl
  intro a _
  rw [hm]

lemma optionCompose_eq_second (p : Law (Option α))
    (next : Option α→Law (Option β)) (hn : next none=pureLaw none) :
    optionCompose p next=map (adaptiveLaw p next) Prod.snd := by
  apply Law.ext
  funext b
  have h₁ := adaptive_output_mass p next (fun a b=>a.bind fun _=>b) b
  have h₂ := adaptive_output_mass p next (fun _ b=>b) b
  rw [optionCompose,h₁,h₂]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  cases a with
  | none =>
    change map (next none) (fun _ : Option β => (none : Option β)) b = map (next none) id b
    rw [map_const,map_id,hn]
  | some a => rfl
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
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_UniversalReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma universalFreshEncoded_exact (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) :
    (universalFreshEncoded R S U C W hCW H n q M t).map (universalFreshDecoded R W H q t)=
      (freshEncoded R S U C W hCW n q M (t (⟨W,hW⟩,n))).map
        (freshDecoded R W n q (t (⟨W,hW⟩,n))) := by
  simp only [universalFreshEncoded,dite_eq_left hW,Option.map_map]
  congr 1
  funext m
  exact dite_eq_left hW

lemma universalFreshEncoded_law (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (hW : W.Nonempty) (H : ℕ) (n : Fin (H+1)) (q M : ℝ) :
    map (universalFreshLaw B H q) (fun t=>
      (universalFreshEncoded R S U C W hCW H n q M t).map (universalFreshDecoded R W H q t))=
      ambientCapLaw R S U C W hW n q M := by
  simp only [universalFreshEncoded_exact R S U C W hCW hW]
  exact universalFresh_output R S U C W hW hCW H n (Nat.le_of_lt_succ n.isLt) q M
end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ChronologicalCapDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma adaptive_event_first (p : Law α) (next : α→Law β) (P : α→Prop) :
    eventMass (adaptiveLaw p next) (Finset.univ.filter fun ab=>P ab.1)=
    eventMass p (Finset.univ.filter P) := by
  simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a
  · simp only [h,ite_true,←Finset.mul_sum,(next a).sum_one,mul_one]
  · simp [h]

lemma adaptive_event_second (p : Law α) (next : α→Law β) (P : β→Prop) :
    eventMass (adaptiveLaw p next) (Finset.univ.filter fun ab=>P ab.2)=
    ∑a,p a*eventMass (next a) (Finset.univ.filter P) := by
  simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw,
    Finset.mul_sum,mul_ite,mul_zero]

lemma adaptive_event_second_le (p : Law α) (next : α→Law β) (P : β→Prop)
    (B : ℝ) (h : ∀a,eventMass (next a) (Finset.univ.filter P)≤B) :
    eventMass (adaptiveLaw p next) (Finset.univ.filter fun ab=>P ab.2)≤B := by
  rw [adaptive_event_second]
  calc
    _ ≤ ∑a,p a*B := Finset.sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (h a) (p.nonneg a)
    _ = B := by rw [←Finset.sum_mul,p.sum_one,one_mul]
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical
lemma excludes_pure_none {A : Type*} [Fintype A] (a : A) :
    eventMass (pureLaw (none : Option (Finset A))) (Finset.univ.filter (Excludes a))=0 := by
  unfold eventMass
  apply Finset.sum_eq_zero
  intro Y hY
  have h := (Finset.mem_filter.mp hY).2
  cases Y <;> simp_all [Excludes,pureLaw]
end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AmbientPairPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma public_joint_composition (p : Law α) (tape : Law β) (firstOut : α→γ)
    (out : γ→β→δ) (next : γ→Law δ)
    (hm : ∀c,map tape (out c)=next c) :
    map (adaptiveLaw p (fun _=>tape)) (fun z=>(firstOut z.1,out (firstOut z.1) z.2))=
      adaptiveLaw (map p firstOut) next := by
  apply Law.ext
  funext cd
  rcases cd with ⟨c,d⟩
  rw [adaptive_output_mass (out:=fun a b=>(firstOut a,out (firstOut a) b))]
  change _=(∑a,if firstOut a=c then p a else 0)*next c d
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : firstOut a=c
  · simp only [hc,ite_true]
    have hs : map tape (fun b=>(c,out c b)) (c,d)=map tape (out c) d := by
      simp only [map,Prod.mk.injEq,true_and]
    rw [hs,hm]
  · simp only [map,Prod.mk.injEq,hc,false_and,ite_false,Finset.sum_const_zero,mul_zero,zero_mul]
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma publicAmbientSecond_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) :
    map (universalFreshLaw (ℙ K (Dual K V)) H q) (publicAmbientSecond A UA B UB H n q MA MB Y)=
      nextAmbientCapLaw A UA B UB hB n q MA MB Y := by
  cases Y with
  | none => exact map_const _ none
  | some W =>
    change map (universalFreshLaw (ℙ K (Dual K V)) H q)
      (fun t=>if _hW : ValidCap B UB MB (UB∩W) then
        (universalFreshEncoded Incident A UA (B∩(UB∩W)) (UB∩W) Finset.inter_subset_right H n q MA t).map
          (universalFreshDecoded Incident (UB∩W) H q t) else none)=_
    dsimp only [nextAmbientCapLaw]
    split_ifs with hv
    · exact universalFreshEncoded_law Incident A UA (B∩(UB∩W)) (UB∩W) Finset.inter_subset_right
        ((hv.source_nonempty hB).mono Finset.inter_subset_right) H n q MA
    · exact map_const _ none

omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_exact (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q) :
    (ambientPairEncoded A UA B UB W H nA nB q MA MB t).map (ambientPairDecoded UB W H q t)=
      let Y := (universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1).map
        (universalFreshDecoded (fun b a=>Incident a b) W H q t.1)
      pairOptions (Y,publicAmbientSecond A UA B UB H nA q MA MB Y t.2) := by
  cases hf : universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1 with
  | none => simp [ambientPairEncoded,hf,pairOptions]
  | some f =>
    simp only [ambientPairEncoded,hf,Option.bind_some,Option.map_some,publicAmbientSecond,pairOptions]
    split_ifs <;> simp only [Option.map_none,Option.map_map,ambientPairDecoded,Function.comp_def]

omit [Finite K] [FiniteDimensional K V] in
theorem ambientPair_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (W : Finset (ℙ K V)) (hW : W.Nonempty)
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) :
    map (ambientPairTapeLaw (K:=K) (V:=V) H q)
      (fun t=>(ambientPairEncoded A UA B UB W H nA nB q MA MB t).map (ambientPairDecoded UB W H q t))=
    map (adaptiveLaw (ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB)
      (nextAmbientCapLaw A UA B UB hB nA q MA MB)) pairOptions := by
  simp only [ambientPair_exact]
  have hh := public_joint_composition (universalFreshLaw (ℙ K V) H q)
    (universalFreshLaw (ℙ K (Dual K V)) H q)
    (fun t=>(universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t).map
      (universalFreshDecoded (fun b a=>Incident a b) W H q t))
    (publicAmbientSecond A UA B UB H nA q MA MB)
    (nextAmbientCapLaw A UA B UB hB nA q MA MB)
    (publicAmbientSecond_law A UA B UB hB H nA q MA MB)
  rw [universalFreshEncoded_law _ _ _ _ _ _ hW] at hh
  have hm := congrArg (fun p=>map p pairOptions) hh
  simpa only [map_comp,Function.comp_def,ambientPairTapeLaw] using hm

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IndependentLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
lemma independent_second (p : Law α) (q : Law β) :
    map (adaptiveLaw p (fun _=>q)) Prod.snd=q := by
  apply Law.ext
  funext b
  change (∑z : α×β,if z.2=b then p z.1*q z.2 else 0)=q b
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [←Finset.sum_mul,p.sum_one,one_mul]
lemma independent_first (p : Law α) (q : Law β) :
    map (adaptiveLaw p (fun _=>q)) Prod.fst=p := by
  apply Law.ext
  funext a
  simp [map,adaptiveLaw,Fintype.sum_prod_type,←Finset.mul_sum,q.sum_one]
lemma map_independent_left (p : Law α) (q : Law β) (f : α→γ) :
    map (adaptiveLaw p (fun _=>q)) (fun z=>f z.1)=map p f := by
  have h := congrArg (fun r=>map r f) (independent_first p q)
  simpa only [map_comp,Function.comp_def] using h
lemma map_independent_right (p : Law α) (q : Law β) (f : β→γ) :
    map (adaptiveLaw p (fun _=>q)) (fun z=>f z.2)=map q f := by
  have h := congrArg (fun r=>map r f) (independent_second p q)
  simpa only [map_comp,Function.comp_def] using h
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FourFinitePredictor
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_exact (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q) :
    (finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t).map (finiteNodeDecoded pred UB H q t)=
      finiteNodeNextOut A UA B UB H nA nB q MA MB c M ((pred.encoded A B t.1).map (pred.decoded t.1)) t.2 := by
  cases hm : pred.encoded A B t.1 with
  | none => simp [finiteNodeEncoded,hm,finiteNodeNextOut]
  | some m =>
    simp only [finiteNodeEncoded,hm,Option.bind_some,Option.map_some,finiteNodeNextOut]
    split_ifs <;> simp only [Option.map_none,Option.map_map,Function.comp_def,finiteNodeDecoded]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_law (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) :
    finiteNodeOutput pred A UA B UB H nA nB q MA MB c M=
      optionCompose (pred.output A B) (finiteNodeNextLaw A UA B UB H nA nB q MA MB c M) := by
  rw [optionCompose_eq_second _ _ (by exact map_const _ none)]
  unfold finiteNodeOutput
  simp only [finiteNode_exact]
  exact public_composition pred.tapeLaw (ambientPairTapeLaw H q)
    (fun t=>(pred.encoded A B t).map (pred.decoded t))
    (finiteNodeNextOut A UA B UB H nA nB q MA MB c M)
    (finiteNodeNextLaw A UA B UB H nA nB q MA MB c M) (fun _=>rfl)

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FiniteNodeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNodeNextLaw_produced (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (c M : ℝ) (hc : 0 < c)
    (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
    (H : ℕ)
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))<H+1)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))<H+1) :
    finiteNodeNextLaw A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M (some W)=
        producedPairLaw A UA B UB hB c (some W) := by
  have hW : W.Nonempty := (hcap.nonempty hA hc).mono Finset.inter_subset_right
  unfold finiteNodeNextLaw finiteNodeNextOut
  simp only [Option.bind_some,dite_eq_left hcap]
  rw [ambientPair_law _ _ _ _ hB _ hW]
  simp only [producedPairLaw,dite_eq_left hW]

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FiniteNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma original_ready_sparse (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (c δ τ : ℝ) (hc : 0 ≤ c) (hδ : 0≤δ) (hτ : 1000*τ ≤ c*δ^2)
    (hr : OriginalNodeReady A₀ UA B₀ UB δ τ) :
    1000*(Nat.card K:ℝ)*incidences (A₀∩UA) (B₀∩UB) ≤ c*(A₀∩UA).card*(B₀∩UB).card := by
  have hi : incidences (A₀∩UA) (B₀∩UB)≤ incidences A₀ B₀ := by
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    exact Finset.product_subset_product Finset.inter_subset_left Finset.inter_subset_left
  have hp := mul_le_mul hr.1 hr.2.1 (mul_nonneg hδ (Nat.cast_nonneg B₀.card))
    (Nat.cast_nonneg (A₀∩UA).card)
  have hp' : δ^2*(A₀.card:ℝ)*B₀.card≤(A₀∩UA).card*(B₀∩UB).card := by nlinarith only [hp]
  have h₁ := mul_le_mul_of_nonneg_left (show (incidences (A₀∩UA) (B₀∩UB):ℝ)≤ incidences A₀ B₀ by exact_mod_cast hi)
    (show (0:ℝ)≤1000*(Nat.card K:ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hr.2.2 (by norm_num : (0:ℝ)≤1000)
  have h₃ := mul_le_mul_of_nonneg_right hτ (show (0:ℝ)≤(A₀.card:ℝ)*B₀.card by positivity)
  have h₄ := mul_le_mul_of_nonneg_left hp' hc
  nlinarith only [h₁,h₂,h₃,h₄]

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OptionEventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma pairOptions_event_left (p : Law (Option α×Option β)) (P : Option α→Prop) (hn : ¬P none) :
    eventMass (map p pairOptions) (Finset.univ.filter fun z=>P (z.map Prod.fst))≤
      eventMass p (Finset.univ.filter fun z=>P z.1) := by
  rw [eventMass_map_filter]
  apply eventMass_filter_mono
  rintro ⟨a,b⟩ hp
  cases a <;> cases b <;> simp_all [pairOptions]

lemma pairOptions_event_right (p : Law (Option α×Option β)) (P : Option β→Prop) (hn : ¬P none) :
    eventMass (map p pairOptions) (Finset.univ.filter fun z=>P (z.map Prod.snd))≤
      eventMass p (Finset.univ.filter fun z=>P z.2) := by
  rw [eventMass_map_filter]
  apply eventMass_filter_mono
  rintro ⟨a,b⟩ hp
  cases a <;> cases b <;> simp_all [pairOptions]

lemma optionCompose_event_le (p : Law (Option α)) (next : Option α→Law (Option β))
    (P : Option β→Prop) (hn : ¬P none) (B : ℝ) (hB : 0≤B)
    (h : ∀a,0<p (some a)→eventMass (next (some a)) (Finset.univ.filter P)≤B) :
    eventMass (optionCompose p next) (Finset.univ.filter P)≤B := by
  have he : eventMass (optionCompose p next) (Finset.univ.filter P)=
      ∑a,p a*eventMass (next a) (Finset.univ.filter fun b=>P (a.bind fun _=>b)) := by
    rw [optionCompose,eventMass_map_filter]
    simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw,
      Finset.mul_sum,mul_ite,mul_zero]
  rw [he]
  calc
    _≤∑a,p a*B := by
      apply Finset.sum_le_sum
      intro a _
      by_cases hz : p a=0
      · simp only [hz,zero_mul,le_refl]
      apply mul_le_mul_of_nonneg_left _ (p.nonneg a)
      cases a with
      | none => simpa [eventMass,hn] using hB
      | some a => exact h a (lt_of_le_of_ne (p.nonneg _) (Ne.symm hz))
    _=B := by rw [←Finset.sum_mul,p.sum_one,one_mul]
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AmbientOriginalDomination
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

theorem firstAmbient_original {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K)
    (A A₀ : Finset (ℙ K V)) (hA : A.Nonempty) (hAA₀ : A⊆A₀)
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBU : B⊆UB)
    (W : Finset (ℙ K V)) (hW : W.Nonempty)
    (c δ : ℝ) (hc : 0 < c) (hc1 : c≤1) (hδ : 0<δ)
    (htrim : δ*A₀.card≤A.card) (hcapture : c*A.card≤(A∩W).card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B ≤ c*A.card*B.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((UB.card:ℝ)/B.card)≤n)
    (b : ℙ K (Dual K V)) :
    eventMass (ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW n (Nat.card K)
      ((320/c+320)*(Nat.card K:ℝ)^(d+1)/A.card)) (Finset.univ.filter (Excludes b))≤
      (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card) := by
  have hC : (A∩W).Nonempty := by
    apply Finset.card_pos.mp
    have ha : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
    exact_mod_cast lt_of_lt_of_le (mul_pos hc ha) hcapture
  have hq0 : (0:ℝ)<Nat.card K := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (by exact_mod_cast hq)
  have hs : (c*δ)*A₀.card≤(A∩W).card := by
    have hh := mul_le_mul_of_nonneg_left htrim hc.le
    nlinarith only [hh,hcapture]
  apply ambientCapLaw_domination (fun b a=>Incident a b) B UB (A∩W) A₀ W hC hW
    Finset.inter_subset_right (Finset.inter_subset_left.trans hAA₀) n hn (Nat.card K) (c*δ) _ hq0 (mul_pos hc hδ) hs
  exact geometric_dual_validation_mass hdim hd hq B UB hB hBU A (A∩W) hC
    Finset.inter_subset_left c hc hc1 hcapture
    (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hsparse) n hn hlen

theorem secondAmbient_original {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (A UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAU : A⊆UA)
    (B B₀ UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBB₀ : B⊆B₀)
    (δ : ℝ) (hδ : 0<δ) (htrim : δ*B₀.card≤B.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/10*A.card*B.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((UA.card:ℝ)/A.card)≤n)
    (MB : ℝ) (Y : Option (Finset (ℙ K (Dual K V)))) (a : ℙ K V) :
    eventMass (nextAmbientCapLaw A UA B UB hB n (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^(d+1)/B.card) MB Y)
      (Finset.univ.filter (Excludes a))≤
      (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card) := by
  have hq0 : (0:ℝ)<Nat.card K := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (by exact_mod_cast hq)
  cases Y with
  | none =>
    change eventMass (pureLaw (none : Option (Finset (ℙ K V)))) (Finset.univ.filter (Excludes a))≤_
    rw [excludes_pure_none]
    positivity
  | some Y =>
    dsimp only [nextAmbientCapLaw]
    split_ifs with hY
    · have hC := hY.source_nonempty hB
      have hs : ((9:ℝ)/10*δ)*B₀.card≤(B∩(UB∩Y)).card := by
        have hh := mul_le_mul_of_nonneg_left htrim (by norm_num : (0:ℝ)≤9/10)
        nlinarith only [hh,hY.2.2]
      apply ambientCapLaw_domination Incident A UA (B∩(UB∩Y)) B₀ (UB∩Y) hC
        (hC.mono Finset.inter_subset_right) Finset.inter_subset_right (Finset.inter_subset_left.trans hBB₀)
        n hn (Nat.card K) ((9:ℝ)/10*δ) _ hq0 (by positivity) hs
      exact geometric_validation_mass hdim hd hq A UA hA hAU B (B∩(UB∩Y)) hC
        Finset.inter_subset_left (9/10) (by norm_num) (by norm_num) hY.2.2 hsparse n hn hlen
    · rw [excludes_pure_none]
      positivity
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProducedPairOriginal
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem producedPair_original (hd : finrank K V=5) (hq : 3≤Nat.card K)
    (A A₀ UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAA₀ : A⊆A₀) (hAU : A⊆UA)
    (B B₀ UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBB₀ : B⊆B₀) (hBU : B⊆UB)
    (c δ M : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ)
    (htrimA : δ*A₀.card≤A.card) (htrimB : δ*B₀.card≤B.card)
    (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B ≤ c*A.card*B.card) :
    (∀b,eventMass (producedPairLaw A UA B UB hB c (some W))
      (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass (producedPairLaw A UA B UB hB c (some W))
      (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  have hW : W.Nonempty := (hcap.nonempty hA hc).mono Finset.inter_subset_right
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
  have hlenA := reverseLength_spec (Nat.card K) (Real.log ((UA.card:ℝ)/A.card)) hq1
    (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hA.card_pos)).mpr
      (by simpa only [one_mul] using (show (A.card:ℝ)≤UA.card from by exact_mod_cast Finset.card_le_card hAU))))
  have hlenB := reverseLength_spec (Nat.card K) (Real.log ((UB.card:ℝ)/B.card)) hq1
    (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hB.card_pos)).mpr
      (by simpa only [one_mul] using (show (B.card:ℝ)≤UB.card from by exact_mod_cast Finset.card_le_card hBU))))
  have hsparse' : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/10*A.card*B.card := by
    have hh := mul_le_mul_of_nonneg_right hc9 (mul_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card))
    nlinarith only [hh,hsparse]
  let nA := reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))
  let nB := reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))
  let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card
  let MB := (320/c+320)*(Nat.card K:ℝ)^5/A.card
  let firstCap := ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB (Nat.card K) MB
  let next := nextAmbientCapLaw A UA B UB hB nA (Nat.card K) MA MB
  have he : producedPairLaw A UA B UB hB c (some W)=map (adaptiveLaw firstCap next) pairOptions := by
    simp only [producedPairLaw,dite_eq_left hW]
    rfl
  rw [he]
  constructor
  · intro b
    have hm := pairOptions_event_left (adaptiveLaw firstCap next) (Excludes b) (by simp [Excludes])
    rw [adaptive_event_first] at hm
    exact hm.trans (firstAmbient_original hd (by norm_num) hq A A₀ hA hAA₀ B UB hB hBU W hW
      c δ hc (by linarith only [hc9]) hδ htrimA hcap.2.2 hsparse nB hlenB.1 hlenB.2.1 b)
  · intro a
    have hm := pairOptions_event_right (adaptiveLaw firstCap next) (Excludes a) (by simp [Excludes])
    apply hm.trans
    apply adaptive_event_second_le
    intro Y
    exact secondAmbient_original hd (by norm_num) hq A UA hA hAU B B₀ UB hB hBB₀ δ hδ htrimB hsparse'
      nA hlenA.1 hlenA.2.1 MB Y a
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem finiteNode_original (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (hd : finrank K V=5) (hq : 3≤Nat.card K)
    (A A₀ UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAA₀ : A⊆A₀) (hAU : A⊆UA)
    (B B₀ UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBB₀ : B⊆B₀) (hBU : B⊆UB)
    (c δ M : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ)
    (htrimA : δ*A₀.card≤A.card) (htrimB : δ*B₀.card≤B.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B ≤ c*A.card*B.card)
    (H : ℕ)
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))<H+1)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))<H+1) :
    (∀b,eventMass (finiteNodeOutput pred A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M)
      (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass (finiteNodeOutput pred A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M)
      (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  rw [finiteNode_law]
  have hn (W : Finset (ℙ K V)) (hW : ¬CaptureBound A UA c M W) :
      finiteNodeNextLaw A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
        ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
        ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M (some W)=pureLaw none := by
    unfold finiteNodeNextLaw finiteNodeNextOut
    simp only [Option.bind_some,dite_eq_right hW]
    exact map_const _ none
  constructor
  · intro b
    have hnon : 0≤(50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card) := by positivity
    apply optionCompose_event_le _ _ _ (by simp [Excludes]) _ hnon
    intro W _
    by_cases hW : CaptureBound A UA c M W
    · rw [finiteNodeNextLaw_produced A UA B UB hA hB c M hc W hW H hnA hnB]
      exact (producedPair_original hd hq A A₀ UA hA hAA₀ hAU B B₀ UB hB hBB₀ hBU
        c δ M hc hc9 hδ htrimA htrimB W hW hsparse).1 b
    · rw [hn W hW]
      have he : eventMass (pureLaw (none : Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))))
          (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))=0 := by
        unfold eventMass
        apply Finset.sum_eq_zero
        intro out hout
        have hp := (Finset.mem_filter.mp hout).2
        cases out <;> simp_all [pureLaw,Excludes]
      rw [he]
      exact hnon
  · intro a
    have hnon : 0≤(50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card) := by positivity
    apply optionCompose_event_le _ _ _ (by simp [Excludes]) _ hnon
    intro W _
    by_cases hW : CaptureBound A UA c M W
    · rw [finiteNodeNextLaw_produced A UA B UB hA hB c M hc W hW H hnA hnB]
      exact (producedPair_original hd hq A A₀ UA hA hAA₀ hAU B B₀ UB hB hBB₀ hBU
        c δ M hc hc9 hδ htrimA htrimB W hW hsparse).2 a
    · rw [hn W hW]
      have he : eventMass (pureLaw (none : Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))))
          (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))=0 := by
        unfold eventMass
        apply Finset.sum_eq_zero
        intro out hout
        have hp := (Finset.mem_filter.mp hout).2
        cases out <;> simp_all [pureLaw,Excludes]
      rw [he]
      exact hnon

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GuardedNodeOriginal
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
lemma eventMass_pure_filter_of_not {Ω : Type*} [Fintype Ω] (x : Ω) (P : Ω→Prop) (h : ¬P x) :
    eventMass (pureLaw x) (Finset.univ.filter P)=0 := by
  unfold eventMass
  apply Finset.sum_eq_zero
  intro y hy
  have hp := (Finset.mem_filter.mp hy).2
  have hne : y≠x := fun he=>h (he ▸ hp)
  simp [pureLaw,hne]
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem guardedNode_original (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ)
    (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2) :
    (∀b,eventMass (guardedNodeLaw pred σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ)
      (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass (guardedNodeLaw pred σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ)
      (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  unfold guardedNodeLaw
  split_ifs with hr
  · have hA := nonempty_of_positive_trim (A₀∩UA) A₀ hA₀ δ hδ hr.1
    have hB := nonempty_of_positive_trim (B₀∩UB) B₀ hB₀ δ hδ hr.2.1
    exact finiteNode_original pred hd hq3 (A₀∩UA) A₀ UA hA Finset.inter_subset_left Finset.inter_subset_right
      (B₀∩UB) B₀ UB hB Finset.inter_subset_left Finset.inter_subset_right c δ M hc hc9 hδ hr.1 hr.2.1
      (original_ready_sparse A₀ UA B₀ UB c δ τ hc.le hδ.le hτ hr) _ _ _
  · constructor <;> intro z <;>
      rw [eventMass_pure_filter_of_not _ _ (by simp [Excludes])] <;> positivity
end SharpRamseyFive.ProjectiveIncidence
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeEncoder
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma guardedNode_encoder_law (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ) :
    map (finiteNodeTapeLaw pred (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t).map
        (finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t))=
      guardedNodeLaw pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ := by
  unfold guardedNodeEncoded guardedNodeLaw
  split_ifs
  · rfl
  · simp only [Option.map_none]
    exact map_const _ none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeSent
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

lemma orientedGuardedNode_law
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ) :
    map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t))=
    if (A₀∩UA).card≤(B₀∩UB).card then
      guardedNodeLaw f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ
    else map
      (guardedNodeLaw r σ hσ hq (by simpa using hd) B₀ UB
        (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀
        hA₀.map c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ)
      (Option.map reverseNodePair) := by
  unfold orientedGuardedNodeEncoded
  split_ifs with h
  · simp only [Option.map_map,Function.comp_def,orientedNodeDecoded]
    exact (map_independent_left
      (finiteNodeTapeLaw f (1000*(Nat.card K)^2) (Nat.card K))
      (finiteNodeTapeLaw r (1000*(Nat.card K)^2) (Nat.card K)) _).trans
      (guardedNode_encoder_law f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
        (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ)
  · simp only [Option.map_map,Function.comp_def,orientedNodeDecoded]
    have hh := congrArg (fun p=>map p (Option.map reverseNodePair))
      (guardedNode_encoder_law r σ hσ hq (by simpa using hd) B₀ UB
        (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀
        hA₀.map c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ)
    rw [map_comp] at hh
    simp only [Option.map_map,Function.comp_def] at hh
    exact (map_independent_right
      (finiteNodeTapeLaw f (1000*(Nat.card K)^2) (Nat.card K))
      (finiteNodeTapeLaw r (1000*(Nat.card K)^2) (Nat.card K)) _).trans hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNode
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma reverseNodePair_excludes_first
    (out : Option (Finset (ℙ K (Dual K (Dual K V)))×Finset (ℙ K (Dual K V))))
    (b : ℙ K (Dual K V)) :
    Excludes b ((out.map reverseNodePair).map Prod.fst) ↔ Excludes b (out.map Prod.snd) := by
  cases out <;> simp [reverseNodePair,Excludes]
omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma reverseNodePair_excludes_second
    (out : Option (Finset (ℙ K (Dual K (Dual K V)))×Finset (ℙ K (Dual K V))))
    (a : ℙ K V) :
    Excludes a ((out.map reverseNodePair).map Prod.snd) ↔
      Excludes (bidualPoint a) (out.map Prod.fst) := by
  cases out <;> simp [reverseNodePair,Excludes]

theorem orientedGuardedNode_original_oai
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ)
    (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2) :
    let p := map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t))
    (∀b,eventMass p (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass p (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  have hconst : 50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ))≤50*(Nat.card K:ℝ)/(9*(c*δ)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hc9 hδ.le]
  dsimp only
  rw [orientedGuardedNode_law]
  split_ifs with hAB
  · obtain ⟨h1,h2⟩ := guardedNode_original f σ hσ hq hd hq3 A₀ UA B₀ UB
      hA₀ hB₀ c δ τ (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hc hc9 hδ hτ
    refine ⟨h1,fun a=>(h2 a).trans ?_⟩
    exact mul_le_mul_of_nonneg_right hconst (by positivity)
  · obtain ⟨h1,h2⟩ := guardedNode_original r σ hσ hq (by simpa using hd) hq3 B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map
      c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hc hc9 hδ hτ
    constructor
    · intro b
      rw [eventMass_map_filter]
      simp only [reverseNodePair_excludes_first]
      have hh := h2 b
      simp only [Finset.filter_map,Finset.card_map,Function.comp_def,Equiv.toEmbedding_apply,
        incident_bidual] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hconst (by positivity))
    · intro a
      rw [eventMass_map_filter]
      simp only [reverseNodePair_excludes_second]
      simpa only [incident_bidual] using h1 (bidualPoint a)

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original_oai := @OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original_oai
