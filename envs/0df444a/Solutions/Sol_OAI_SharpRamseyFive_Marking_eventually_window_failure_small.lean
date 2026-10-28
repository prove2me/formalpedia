-- Prove2me | solution 1 for OAI.SharpRamseyFive.Marking.eventually_window_failure_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:28:06.424557+00:00
-- url     : https://prove2.me/submissions/74bb16af-137d-4afc-a984-ee1c3d07f112

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_eventually_ordered_target_retention

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

lemma relationMass_nonneg (R : α→β→Prop) (f : α→ℝ) (g : β→ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀b,0 ≤ g b) : 0 ≤ relationMass R f g :=
  Finset.sum_nonneg (fun entry _=>mul_nonneg (hf entry.1) (hg entry.2))

end

open scoped BigOperators Classical

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
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_PivotTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open BinaryTree

lemma balanced_height (H lo n : ℕ) (hn : n<2^H) :
    (balanced lo n).height≤H := by
  induction H generalizing lo n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simp [balanced]
  | succ H ih =>
    cases n with
    | zero => simp [balanced]
    | succ n =>
      rw [pow_succ] at hn
      have hl : n/2<2^H := by omega
      have hr : n-n/2<2^H := by omega
      simp only [balanced,BinaryTree.height]
      exact Nat.succ_le_succ (max_le (ih lo (n/2) hl) (ih _ _ hr))

end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OriginalLevelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α : Type*} [Fintype α]

lemma positiveLaw_mean (p : Law α) (f : α → ℝ) :
    (∑ a, positiveLaw p a * f a) = ∑ a, p a * f a := by
  change (∑ a : {a // 0 < p a}, p a * f a) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => 0 < p a)) (by simp) (fun a => p a * f a), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : 0 < p a
  · simp [h]
  · have hz : p a = 0 := le_antisymm (le_of_not_gt h) (p.nonneg a)
    simp [hz]

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
variable {α β : Type*} [Fintype α] [Fintype β]

lemma conditionOn_ge_on (p : Law α) (E : Finset α) (hE : 0<eventMass p E)
    (a : α) (ha : a∈E) : p a ≤ conditionOn p E hE a := by
  rw [conditionOn_apply,ite_eq_left ha]
  exact (le_div_iff₀ hE).mpr (mul_le_of_le_one_right (p.nonneg a) (eventMass_le_one p E))

omit [Fintype α] in
lemma uniformWeight_eq_zero_of_not_mem (A : Finset α) (a : α) (h : a∉A) :
    uniformWeight A a=0 := by simp only [uniformWeight,ite_eq_right h]

lemma supported_levels_conditioned_domination (μ : Law (Finset α)) (p : Law α)
    (E : Finset α) (hE : 0<eventMass p E) (C : ℝ) (hC : 0≤C)
    (hsub : ∀ A,0<μ A→A⊆E)
    (hdom : ∀ a,(∑ A,μ A*uniformWeight A a)≤C*p a) :
    ∀ a,(∑ A,positiveLaw μ A*uniformWeight A.val a)≤C*conditionOn p E hE a := by
  intro a
  rw [positiveLaw_mean μ (fun A=>uniformWeight A a)]
  by_cases ha : a∈E
  · exact (hdom a).trans (mul_le_mul_of_nonneg_left (conditionOn_ge_on p E hE a ha) hC)
  · have hz : (∑ A,μ A*uniformWeight A a)=0 := by
      apply Finset.sum_eq_zero
      intro A _
      by_cases hm : 0<μ A
      · rw [uniformWeight_eq_zero_of_not_mem A a (fun hx=>ha (hsub A hm hx)),mul_zero]
      · rw [le_antisymm (le_of_not_gt hm) (μ.nonneg A),zero_mul]
    rw [hz]
    exact mul_nonneg hC ((conditionOn p E hE).nonneg a)

lemma relationMass_conditioned_good (R : α→β→Prop) (p : Law α) (q : Law β)
    (A : Finset α) (B : Finset β) (hA : 0<eventMass p A) (hB : 0<eventMass q B) :
    relationMass R (conditionOn p A hA) (conditionOn q B hB)=
      relationMass (fun a b=>a∈A ∧ b∈B ∧ R a b) p q/(eventMass p A*eventMass q B) := by
  simp only [relationMass,Finset.sum_filter,conditionOn_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : z.1∈A <;> by_cases hb : z.2∈B <;> by_cases hr : R z.1 z.2 <;>
    simp only [ha,hb,hr,ite_true,ite_false,true_and,false_and,and_false,
      zero_mul,mul_zero,zero_div,div_mul_div_comm]
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
variable {I J : Type*} [Preorder I] [Preorder J]

lemma ordered_map (g : I→J) (hg : Monotone g) (b : BinaryTree I) (hb : Ordered b) :
    Ordered (b.map g) := by
  induction b with
  | nil=>trivial
  | node a l r ihl ihr=>
    refine ⟨?_,?_,ihl hb.2.2.1,ihr hb.2.2.2⟩
    · intro j
      obtain ⟨k,hk⟩:=label_map_mem g l j
      rw [hk]
      exact hg (hb.1 k)
    · intro j
      obtain ⟨k,hk⟩:=label_map_mem g r j
      rw [hk]
      exact hg (hb.2.1 k)

omit [Preorder I] [Preorder J] in
lemma map_height (g : I→J) (b : BinaryTree I) : (b.map g).height=b.height := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>simp only [BinaryTree.map,BinaryTree.height,ihl,ihr]

end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.PivotTree
open BinaryTree TreeCodec

lemma balanced_ordered (lo n : ℕ) : Ordered (balanced lo n) := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih=>
    cases n with
    | zero=>simp [balanced,Ordered]
    | succ n=>
      rw [balanced,Ordered]
      refine ⟨?_,?_,ih _ (by omega) _,ih _ (by omega) _⟩
      · intro j
        have h:=(balanced_label_bounds lo (n/2) j).2
        omega
      · intro j
        have h:=(balanced_label_bounds (lo+n/2+1) (n-n/2) j).1
        omega

lemma finiteBalanced_ordered (n : ℕ) : Ordered (finiteBalanced n) := by
  apply ordered_map _ _ _ (balanced_ordered _ _)
  intro i j h
  exact min_le_min_right _ h

lemma finiteBalanced_height (H n : ℕ) (hn : n<2^H) : (finiteBalanced n).height≤H := by
  rw [finiteBalanced,map_height]
  exact balanced_height H 0 n hn

end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TreeShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open TreeCodec
open scoped Classical
noncomputable section

lemma finiteRankEquiv_label (n : ℕ) (j : Fin n) :
    (label (finiteBalanced n) ((finiteRankEquiv n).symm j)).val=j.val := by
  exact congrArg Fin.val ((finiteRankEquiv n).apply_symm_apply j)
end
end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedTreeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
  [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma mem_flagRectangle (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V)))
    (z : (ℙ K V)×(ℙ K (Dual K V))) :
    z∈flagRectangle A B ↔ z.1∈A ∧ z.2∈B ∧ Incident z.1 z.2 := by
  simp only [flagRectangle,Finset.mem_filter,Finset.mem_product,and_assoc]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
  [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma targetCovered_some (C : PivotContext K V)
    (D : Finset (ℙ K (Dual K V))×Finset (ℙ K V)) (a : ℙ K V) (b : ℙ K (Dual K V)) :
    TargetCovered (some C) (some D) a b ↔ a∈C.1 ∧ b∈C.2 ∧ a∈D.2 ∧ b∈D.1 := by
  constructor
  · rintro ⟨C',D',hC,hD,h⟩
    cases Option.some.inj hC
    cases Option.some.inj hD
    exact h
  · intro h
    exact ⟨C,D,rfl,rfl,h⟩

theorem orientedPublicDomain_coverage
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I→Finset (ℙ K V)) (B₀ : I→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ)
    (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree) (C : PivotContext K V)
    (j : Address tree) (z : (ℙ K V)×(ℙ K (Dual K V))) :
    z∈orientedPublicDomain f r tree ω C
      (orientedPivotTreeEncoded f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C) j ↔
    TargetCovered (orientedPivotContextAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j)
      (orientedPivotCapsAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j) z.1 z.2 ∧
      Incident z.1 z.2 := by
  induction tree generalizing C with
  | nil => exact nomatch j
  | node i lt rt ihl ihr =>
    rcases j with j | (j | j)
    · cases he:orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
        (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ (ω.1 C) <;>
        simp [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,
          targetCovered_some,orientedNodeDomain,mem_flagRectangle,Finset.mem_inter,and_left_comm,and_assoc]
      ; simp [TargetCovered]
    · cases he:orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
        (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ (ω.1 C) with
      | none => simp [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,TargetCovered]
      | some m =>
        simpa only [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,
          Option.map_some,Option.elim_some]
          using ihl ω.2.1 (orientedPivotLeft f r C (ω.1 C) m) j
    · cases he:orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
        (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ (ω.1 C) with
      | none => simp [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,TargetCovered]
      | some m =>
        simpa only [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,
          Option.map_some,Option.elim_some]
          using ihr ω.2.2 (orientedPivotRight f r C (ω.1 C) m) j

end
end

open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

omit [Finite K] [FiniteDimensional K V] in
lemma variableTreeLaw_eval (w : ℕ) (m : Fin (w+1)) :
    map (variableTreeLaw f r w) (fun t=>t m)=orientedPivotTreeLaw f r (finiteBalanced m.val) :=
  piLaw_eval _ _

omit [Finite K] in
lemma variableTreeDomain_valid {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (a : VariableTreeMessage f r t C) (j : Fin a.1.val) :
    variableTreeDomain f r t C a ⟨j.val,lt_trans j.isLt a.1.isLt⟩=
      orientedPublicDomain f r _ (t a.1) C a.2 ((finiteRankEquiv a.1.val).symm j) := by
  simp only [variableTreeDomain,dite_eq_left j.isLt]

lemma variableTreeDomain_coverage {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (m : Fin (w+1)) (σ : ℝ) (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V ≤ 5)
    (A₀ : Fin (m.val+1)→Finset (ℙ K V)) (B₀ : Fin (m.val+1)→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (j : Fin m.val) (a : ℙ K V) (b : ℙ K (Dual K V)) :
    (a,b)∈variableTreeDomain f r t C
      (variableTreeEncoded f r t C m σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ)
      ⟨j.val,lt_trans j.isLt m.isLt⟩ ↔
    Incident a b ∧ TargetCovered
      (orientedPivotContextAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ
        (finiteBalanced m.val) (t m) C ((finiteRankEquiv m.val).symm j))
      (orientedPivotCapsAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ
        (finiteBalanced m.val) (t m) C ((finiteRankEquiv m.val).symm j)) a b := by
  unfold variableTreeEncoded
  rw [variableTreeDomain_valid]
  exact (orientedPublicDomain_coverage f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ
    (finiteBalanced m.val) (t m) C _ (a,b)).trans and_comm

end

end SharpRamseyFive.ProjectiveIncidence

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
variable {α : Type*} [Fintype α]
lemma eventMass_filter_mean (p : Law α) (P : α→Prop) :
    eventMass p (Finset.univ.filter P)=mean p (fun a=>if P a then 1 else 0) := by
  simp only [eventMass,Finset.sum_filter,mean,mul_ite,mul_one,mul_zero]
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

theorem variable_table_target_failure (w : ℕ) (m : Fin (w+1))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (μ : Fin (m.val+1)→Law (Finset (ℙ K V)))
    (ν : Fin (m.val+1)→Law (Finset (ℙ K (Dual K V))))
    (X : Fin (m.val+1)→Finset (ℙ K V)→Finset (ℙ K V))
    (Y : Fin (m.val+1)→Finset (ℙ K (Dual K V))→Finset (ℙ K (Dual K V)))
    (hX : ∀i a,(X i a).Nonempty) (hY : ∀i b,(Y i b).Nonempty)
    (γ : Law Ω) (a : Ω→ℙ K V) (b : Ω→ℙ K (Dual K V))
    (hinc : ∀z,0<γ z→Incident (a z) (b z))
    (c δ τ P : ℝ) (hδ : 0<δ) (j : Fin m.val) :
    mean (adaptiveLaw γ (fun _=>adaptiveLaw (originalLevelLaw μ ν)
      (fun _=>variableTreeLaw f r w))) (fun z=>
        if (a z.1,b z.1)∉variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
          (variableTreeEncoded f r z.2.2 (Finset.univ,Finset.univ) m σ hσ hq hd
            (fun i=>X i (z.2.1.1 i)) (fun i=>Y i (z.2.1.2 i))
            (fun i=>hX i _) (fun i=>hY i _) c δ τ P hδ)
          ⟨j.val,lt_trans j.isLt m.isLt⟩ then 1 else 0)=
      orientedTargetFailure f r σ hσ hq hd μ ν X Y hX hY γ a b
        c δ τ P hδ (finiteBalanced m.val) ((finiteRankEquiv m.val).symm j) := by
  rw [orientedTargetFailure,eventMass_filter_mean,mean_adaptive,mean_adaptive]
  apply mean_congr_pos
  intro z hz
  rw [mean_adaptive,mean_adaptive]
  apply mean_congr
  intro lev
  have he : ∀t : VariableTreeTape f r w,
      ((a z,b z)∉variableTreeDomain f r t (Finset.univ,Finset.univ)
        (variableTreeEncoded f r t (Finset.univ,Finset.univ) m σ hσ hq hd
          (fun i=>X i (lev.1 i)) (fun i=>Y i (lev.2 i))
          (fun i=>hX i _) (fun i=>hY i _) c δ τ P hδ)
        ⟨j.val,lt_trans j.isLt m.isLt⟩) ↔
      ¬TargetCovered
        (orientedPivotContextAt f r σ hσ hq hd (fun i=>X i (lev.1 i))
          (fun i=>Y i (lev.2 i)) (fun i=>hX i _) (fun i=>hY i _)
          c δ τ P hδ (finiteBalanced m.val) (t m) (Finset.univ,Finset.univ)
          ((finiteRankEquiv m.val).symm j))
        (orientedPivotCapsAt f r σ hσ hq hd (fun i=>X i (lev.1 i))
          (fun i=>Y i (lev.2 i)) (fun i=>hX i _) (fun i=>hY i _)
          c δ τ P hδ (finiteBalanced m.val) (t m) (Finset.univ,Finset.univ)
          ((finiteRankEquiv m.val).symm j)) (a z) (b z) := by
    intro t
    rw [variableTreeDomain_coverage]
    simp only [hinc z hz,true_and]
  simp_rw [he]
  rw [←variableTreeLaw_eval f r w m,mean_map]
  congr 1
  funext t
  congr 1
end
end SharpRamseyFive.ProjectiveIncidence

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

lemma representative_late {w r : ℕ} (v : Fin w) (a : Fin r) (t : Fin (2*r)) :
    slotEmbedding (Sum.inr (v,t)) < slotEmbedding (Sum.inl ((v,true),a)) := by
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
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

omit [Finite K] [FiniteDimensional K V] in
lemma orderedCollision_symm (p : Law (I→FlagPair K V)) (e : I≃Fin n)
    (u : I→ℝ) (s : ℝ) (i j : I) : orderedCollision p e u s i j=orderedCollision p e u s j i :=
  add_comm _ _

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Repair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.repair_of_positive (p : Law α) (a : α) (h : 0<p a) : p.repair a=a := by
  simp only [Law.repair,ite_eq_left h]

lemma Law.repair_mean (p : Law α) (f : α→ℝ) :
    (∑ a,p a*f (p.repair a))=∑ a,p a*f a := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : 0<p a
  · rw [p.repair_of_positive a h]
  · rw [show p a=0 from le_antisymm (le_of_not_gt h) (p.nonneg a),zero_mul,zero_mul]

lemma repaired_levels_conditioned_domination (μ : Law (Finset α)) (p : Law α)
    (E : Finset α) (hE : 0<eventMass p E) (C : ℝ) (hC : 0≤C)
    (hsub : ∀ A,0<μ A→A⊆E)
    (hdom : ∀ a,(∑ A,μ A*uniformWeight A a)≤C*p a) :
    ∀ a,(∑ A,μ A*uniformWeight (μ.repair A) a)≤C*conditionOn p E hE a := by
  intro a
  rw [μ.repair_mean (fun A=>uniformWeight A a)]
  have h:=supported_levels_conditioned_domination μ p E hE C hC hsub hdom a
  rw [positiveLaw_mean μ (fun A=>uniformWeight A a)] at h
  exact h
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SurvivorRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open scoped Classical
noncomputable section
variable {w : ℕ}

lemma survivorRank_original (E : Finset (Fin w)) (v : Fin w) (hv : v∈E) :
    E.orderEmbOfFin rfl ⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩=v := by
  let j := (E.orderIsoOfFin rfl).symm ⟨v,hv⟩
  have hj : E.orderEmbOfFin rfl j=v := congrArg Subtype.val
    ((E.orderIsoOfFin rfl).apply_symm_apply ⟨v,hv⟩)
  have he : (⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩ : Fin E.card)=j := by
    apply Fin.ext
    change (survivorRank E v).val=j.val
    rw [←hj,survivorRank_orderEmb]
  rw [he,hj]
end
end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLevelProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalGoodReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
lemma relationMass_conditioned_good_le (R : α→β→Prop) (p : Law α) (q : Law β)
    (A : Finset α) (B : Finset β)
    (hA : (1:ℝ)/2≤eventMass p A) (hB : (1:ℝ)/2≤eventMass q B) (ρ : ℝ)
    (hρ : relationMass (fun a b=>a∈A ∧ b∈B ∧ R a b) p q≤ρ) :
    relationMass R (conditionOn p A (by linarith)) (conditionOn q B (by linarith))≤4*ρ := by
  rw [relationMass_conditioned_good]
  have hn:=relationMass_nonneg (fun a b=>a∈A ∧ b∈B ∧ R a b) p q p.nonneg q.nonneg
  have hab : (1:ℝ)/4≤eventMass p A*eventMass q B := by
    nlinarith [mul_le_mul hA hB (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤eventMass p A)]
  have hp : 0<eventMass p A*eventMass q B := lt_of_lt_of_le (by norm_num) hab
  apply (div_le_iff₀ hp).mpr
  have hr : 0≤ρ := hn.trans hρ
  nlinarith [mul_le_mul_of_nonneg_left hab hr]

lemma relationMass_restricted_conditionOn_right (R : α→β→Prop) (p : Law α) (q : Law β)
    (A : Finset α) (B : Finset β) (hB : 0<eventMass q B) :
    relationMass R (fun a=>if a∈A then p a else 0) (conditionOn q B hB)=
      relationMass (fun a b=>a∈A ∧ b∈B ∧ R a b) p q/eventMass q B := by
  simp only [relationMass,Finset.sum_filter,conditionOn_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : z.1∈A <;> by_cases hb : z.2∈B <;> by_cases hr : R z.1 z.2 <;>
    simp only [ha,hb,hr,ite_true,ite_false,true_and,false_and,and_false,
      zero_mul,mul_zero,zero_div,mul_div_assoc]

lemma relationMass_conditionOn_left_restricted (R : α→β→Prop) (p : Law α) (q : Law β)
    (A : Finset α) (B : Finset β) (hA : 0<eventMass p A) :
    relationMass R (conditionOn p A hA) (fun b=>if b∈B then q b else 0)=
      relationMass (fun a b=>a∈A ∧ b∈B ∧ R a b) p q/eventMass p A := by
  simp only [relationMass,Finset.sum_filter,conditionOn_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : z.1∈A <;> by_cases hb : z.2∈B <;> by_cases hr : R z.1 z.2 <;>
    simp only [ha,hb,hr,ite_true,ite_false,true_and,false_and,and_false,
      zero_mul,mul_zero,zero_div,div_mul_eq_mul_div]

lemma div_half_bound (a m ρ : ℝ) (hm : (1:ℝ)/2 ≤ m) (ha : 0≤a) (hρ : a≤ρ) :
    a/m≤2*ρ := by
  apply (div_le_iff₀ (by linarith : 0 < m)).mpr
  have hr : 0≤ρ := ha.trans hρ
  nlinarith [mul_le_mul_of_nonneg_left hm hr]
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

omit [Finite K] in
theorem ordered_good_reference_sparse (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j)
    (hi : (1:ℝ)/2≤eventMass (first (map p (fun x=>x i))) (reciprocalGoodA (map p (fun x=>x i)) (u i) s))
    (hj : (1:ℝ)/2≤eventMass (second (map p (fun x=>x j))) (reciprocalGoodB (map p (fun x=>x j)) (u j) s))
    (hgood : entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
      entropy (pair p (fun x=>x i) (fun x=>x j))+orderedCollision p e u s i j≤ε) :
    relationMass Incident
      (conditionOn (first (map p (fun x=>x i))) (reciprocalGoodA (map p (fun x=>x i)) (u i) s) (by linarith))
      (conditionOn (second (map p (fun x=>x j))) (reciprocalGoodB (map p (fun x=>x j)) (u j) s) (by linarith))≤
      320016*ε := by
  have hh:=relationMass_conditioned_good_le Incident (first (map p (fun x=>x i)))
    (second (map p (fun x=>x j))) _ _ hi hj (80004*ε)
    ((ordered_reciprocal_low_conflict hdim p e u s hcons i j hij).trans
      (mul_le_mul_of_nonneg_left hgood (by norm_num)))
  linarith
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
lemma early_middle_le (sel : (Fin w×Bool)→Fin r) (i j : Fin w) (hij : i≤j) (t : Fin (2*r)) :
    slotEmbedding (earlySlot sel i) < slotEmbedding (middleSlot j t) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · exact ordered_windows _ _ h
  · exact representative_early _ _ _
lemma middle_late_le (sel : (Fin w×Bool)→Fin r) (i j : Fin w) (hij : i≤j) (t : Fin (2*r)) :
    slotEmbedding (middleSlot i t) < slotEmbedding (lateSlot sel j) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · exact ordered_windows _ _ h
  · exact representative_late _ _ _
lemma early_late_le (sel : (Fin w×Bool)→Fin r) (i j : Fin w) (hij : i≤j) :
    slotEmbedding (earlySlot sel i) < slotEmbedding (lateSlot sel j) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · exact ordered_windows _ _ h
  · simp only [earlySlot,lateSlot,Fin.lt_def,slotEmbedding_val,windowCoordinates]
    have hh:=(sel (i,false)).isLt
    omega
end
end SharpRamseyFive.Windows
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]

local instance windowScoreBlockDE_r33679f_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.windowScoreIndexDE
omit [Finite K] [Nonempty (Fin r)] in
theorem window_reference_sparse (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r)
    (J d s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i < slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : Fin w) (hij : i≤j)
    (hgood : indexBad J d ε p (orderedCollision p (slotEquiv w r) u s) sel (earlySlot sel i)=0)
    (hi : (1:ℝ)/2≤eventMass (first (map p (fun x=>x (earlySlot sel i))))
      (reciprocalGoodA (map p (fun x=>x (earlySlot sel i))) (u (earlySlot sel i)) s))
    (hj : (1:ℝ)/2≤eventMass (second (map p (fun x=>x (lateSlot sel j))))
      (reciprocalGoodB (map p (fun x=>x (lateSlot sel j))) (u (lateSlot sel j)) s)) :
    relationMass Incident
      (conditionOn (first (map p (fun x=>x (earlySlot sel i))))
        (reciprocalGoodA (map p (fun x=>x (earlySlot sel i))) (u (earlySlot sel i)) s) (by linarith))
      (conditionOn (second (map p (fun x=>x (lateSlot sel j))))
        (reciprocalGoodB (map p (fun x=>x (lateSlot sel j))) (u (lateSlot sel j)) s) (by linarith))≤320016*ε := by
  apply ordered_good_reference_sparse hdim p (slotEquiv w r) u s ε hcons _ _
    (early_late_le sel i j hij) hi hj
  exact (good_index_scores J d ε p _ (fun _ _=>orderedCollision_nonneg ..) sel _ hgood).2 (j,true)
    (by simp [OtherBlock,earlySlot])

omit [Finite K] [Nonempty (Fin r)] in
theorem window_target_right_sparse (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r)
    (J d s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i < slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : Fin w) (hij : i≤j) (t : Fin (2*r))
    (hgood : indexBad J d ε p (orderedCollision p (slotEquiv w r) u s) sel (middleSlot i t)=0)
    (hj : (1:ℝ)/2≤eventMass (second (map p (fun x=>x (lateSlot sel j))))
      (reciprocalGoodB (map p (fun x=>x (lateSlot sel j))) (u (lateSlot sel j)) s)) :
    relationMass Incident
      (fun a=>if a∈reciprocalGoodA (map p (fun x=>x (middleSlot i t))) (u (middleSlot i t)) s
        then first (map p (fun x=>x (middleSlot i t))) a else 0)
      (conditionOn (second (map p (fun x=>x (lateSlot sel j))))
        (reciprocalGoodB (map p (fun x=>x (lateSlot sel j))) (u (lateSlot sel j)) s) (by linarith))≤160008*ε := by
  rw [relationMass_restricted_conditionOn_right]
  have hh:=(ordered_reciprocal_low_conflict hdim p (slotEquiv w r) u s hcons
    (middleSlot i t) (lateSlot sel j) (middle_late_le sel i j hij t)).trans
    (mul_le_mul_of_nonneg_left
      ((good_index_scores J d ε p _ (fun _ _=>orderedCollision_nonneg ..) sel _ hgood).2 (j,true) trivial)
      (by norm_num : (0:ℝ)≤80004))
  have h:=div_half_bound _ _ _ hj (relationMass_nonneg _ _ _ (Law.nonneg _) (Law.nonneg _)) hh
  change _≤2*(80004*ε) at h
  simpa only [reciprocalGoodA,reciprocalGoodB,←mul_assoc,show (2:ℝ)*80004=160008 by norm_num] using h

omit [Finite K] [Nonempty (Fin r)] in
theorem window_target_left_sparse (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r)
    (J d s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i < slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : Fin w) (hij : i≤j) (t : Fin (2*r))
    (hgood : indexBad J d ε p (orderedCollision p (slotEquiv w r) u s) sel (middleSlot j t)=0)
    (hi : (1:ℝ)/2≤eventMass (first (map p (fun x=>x (earlySlot sel i))))
      (reciprocalGoodA (map p (fun x=>x (earlySlot sel i))) (u (earlySlot sel i)) s)) :
    relationMass Incident
      (conditionOn (first (map p (fun x=>x (earlySlot sel i))))
        (reciprocalGoodA (map p (fun x=>x (earlySlot sel i))) (u (earlySlot sel i)) s) (by linarith))
      (fun b=>if b∈reciprocalGoodB (map p (fun x=>x (middleSlot j t))) (u (middleSlot j t)) s
        then second (map p (fun x=>x (middleSlot j t))) b else 0)≤160008*ε := by
  rw [relationMass_conditionOn_left_restricted]
  have hh:=(ordered_reciprocal_low_conflict hdim p (slotEquiv w r) u s hcons
    (earlySlot sel i) (middleSlot j t) (early_middle_le sel i j hij t)).trans
    (mul_le_mul_of_nonneg_left
      (good_index_scores_reverse J d ε p _ (fun _ _=>orderedCollision_nonneg ..) (fun _ _=>orderedCollision_symm ..)
        sel _ hgood (i,false) trivial) (by norm_num : (0:ℝ)≤80004))
  have h:=div_half_bound _ _ _ hi (relationMass_nonneg _ _ _ (Law.nonneg _) (Law.nonneg _)) hh
  change _≤2*(80004*ε) at h
  simpa only [reciprocalGoodA,reciprocalGoodB,←mul_assoc,show (2:ℝ)*80004=160008 by norm_num] using h
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowLossAggregation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
attribute [local instance] OAI.SharpRamseyFive.ProjectiveIncidence.origWindowIDE
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

theorem original_window_target_failure {w n : ℕ} (E : Finset (Fin w)) (_hE : E.Nonempty)
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (μ : Fin (E.card+1)→Law (Finset (ℙ K V)))
    (ν : Fin (E.card+1)→Law (Finset (ℙ K (Dual K V))))
    (X : Fin (E.card+1)→Finset (ℙ K V)→Finset (ℙ K V))
    (Y : Fin (E.card+1)→Finset (ℙ K (Dual K V))→Finset (ℙ K (Dual K V)))
    (hX : ∀i a,(X i a).Nonempty) (hY : ∀i b,(Y i b).Nonempty)
    (p : Law (Slots w n→FlagPair K V))
    (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
    (c δ τ P : ℝ) (hδ : 0<δ) (v : Fin w) (hv : v∈E) (j : Fin (2*n)) :
    mean (adaptiveLaw p (fun _=>adaptiveLaw (originalLevelLaw μ ν)
      (fun _=>variableTreeLaw f r w))) (fun z=>
        if z.1 (middleSlot v j)∉variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
          (variableTreeEncoded f r z.2.2 (Finset.univ,Finset.univ)
            ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩ σ hσ hq hd
            (fun i=>X i (z.2.1.1 i)) (fun i=>Y i (z.2.1.2 i))
            (fun i=>hX i _) (fun i=>hY i _) c δ τ P hδ)
          (survivorRank E v) then 1 else 0)=
      orientedTargetFailure f r σ hσ hq hd μ ν X Y hX hY p
        (fun x=>(x (middleSlot v j)).1) (fun x=>(x (middleSlot v j)).2)
        c δ τ P hδ (finiteBalanced E.card)
        ((finiteRankEquiv E.card).symm ⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩) := by
  have hh:=variable_table_target_failure f r w
    ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩ σ hσ hq hd μ ν X Y hX hY p
    (fun x=>(x (middleSlot v j)).1) (fun x=>(x (middleSlot v j)).2)
    (fun x hx=>hinc x hx _) c δ τ P hδ
    ⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩
  exact hh
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowTargetInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]
lemma map_first_value (p : Law Ω) (z : Ω→α×β) :
    map p (fun x=>(z x).1)=first (map p z) := by
  rw [←map_first, map_comp]; rfl
lemma map_second_value (p : Law Ω) (z : Ω→α×β) :
    map p (fun x=>(z x).2)=second (map p z) := by
  rw [←map_second, map_comp]; rfl
lemma eventMass_bad_map (p : Law Ω) (f : Ω→α) (G : Finset α) :
    eventMass p (Finset.univ.filter fun x=>f x∉G)=eventMass (map p f) Gᶜ := by
  rw [eventMass_map_preimage]
  congr 1
  ext x
  simp only [eventPreimage,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]

local instance inputWinBDE_r33679f_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.inputWinIDE
omit [FiniteDimensional K V] [Nonempty (Fin r)] in
theorem window_bad_target (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ)
    (sel : (Fin w×Bool)→Fin r) (v : Fin w) (t : Fin (2*r)) (s d ε C₀ : ℝ)
    (hs : 0 < s)
    (hA : ((support (first (map p (fun x=>x (middleSlot v t))))).card:ℝ) ≤
      32*Real.exp (5*Real.log (Nat.card K)-u (middleSlot v t)))
    (hB : ((support (second (map p (fun x=>x (middleSlot v t))))).card:ℝ) ≤
      32*Real.exp (u (middleSlot v t)))
    (hflag : ((support (map p (fun x=>x (middleSlot v t)))).card:ℝ) ≤ C₀*(Nat.card K:ℝ)^4)
    (hgood : indexBad (4*Real.log (Nat.card K)) d ε p
      (orderedCollision p (slotEquiv w r) u s) sel (middleSlot v t)=0) :
    eventMass p (Finset.univ.filter fun x=>(x (middleSlot v t)).1∉
      reciprocalGoodA (map p (fun y=>y (middleSlot v t))) (u (middleSlot v t)) s) ≤
        reciprocalBadMass s d C₀ ∧
    eventMass p (Finset.univ.filter fun x=>(x (middleSlot v t)).2∉
      reciprocalGoodB (map p (fun y=>y (middleSlot v t))) (u (middleSlot v t)) s) ≤
        reciprocalBadMass s d C₀ := by
  have hent:=(good_index_scores (4*Real.log (Nat.card K)) d ε p _
    (fun i j=>orderedCollision_nonneg p (slotEquiv w r) u s i j) sel _ hgood).1
  have hh:=reciprocal_bad_endpoints (map p (fun x=>x (middleSlot v t))) _ s d C₀
    hs hA hB hflag hent
  rw [eventMass_bad_map,eventMass_bad_map,map_first_value,map_second_value]
  exact hh
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section

theorem pivot_support_product (q u v k d a b : ℝ) (hq : 0<q)
    (hdrop : u-v≤d)
    (ha : Real.exp (5*Real.log q-u-k)/2≤a)
    (hb : Real.exp (v-k)/2≤b) :
    q^5*Real.exp (-d-2*k)/4≤a*b := by
  have he : Real.exp (5*Real.log q-u-k)/2*(Real.exp (v-k)/2)=
      q^5*Real.exp (v-u-2*k)/4 := by
    rw [div_mul_div_comm,←Real.exp_add]
    have hx : (5*Real.log q-u-k)+(v-k)=5*Real.log q+(v-u-2*k) := by ring
    have hfive : Real.exp (5*Real.log q)=Real.exp (Real.log q)^5 := by
      simpa using Real.exp_nat_mul (Real.log q) 5
    rw [hx,Real.exp_add,hfive,Real.exp_log hq]
    norm_num
  have hle := mul_le_mul ha hb (by positivity : 0≤Real.exp (v-k)/2)
    ((by positivity : 0≤Real.exp (5*Real.log q-u-k)/2).trans ha)
  rw [he] at hle
  refine le_trans ?_ hle
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Filter Asymptotics Real
open scoped Topology
noncomputable section

lemma reciprocal_bad_uniform {σ D b C : ℝ} (hσ : 1≤σ) (_hb : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤
      Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b)) := by
  have hσp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hσp b).trans_le hD
  have hs : σ^(3*b)≤D*σ^(2*b) := by
    calc
      _ = σ^b*σ^(2*b) := by rw [←Real.rpow_add hσp];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hσp.le _)
  have he : (D*σ^b)/(D*σ^(2*b))=σ^(-b) := by
    rw [mul_div_mul_left _ _ hDp.ne']
    rw [←Real.rpow_sub hσp]
    congr 1
    ring
  have hc := div_le_div_of_nonneg_left hC (Real.rpow_pos_of_pos hσp _) hs
  unfold reciprocalBadMass
  rw [mul_div_assoc,add_div,he]
  exact add_le_add (Real.exp_le_exp.mpr (neg_le_neg hs))
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hc) (by norm_num))

lemma reciprocal_core_uniform {σ D b C : ℝ} (hσ : 1≤σ) (hb : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))+
      2*Real.exp 1*reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤
    2*(σ^(-b)+(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+
      2*(Real.log σ/σ^(3*b)))+
      2*Real.exp 1*(Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b))) := by
  have hσp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hσp b).trans_le hD
  have hs : σ^(3*b)≤D*σ^(2*b) := by
    calc
      _ = σ^b*σ^(2*b) := by rw [←Real.rpow_add hσp];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hσp.le _)
  have he : (D*σ^b)/(D*σ^(2*b))=σ^(-b) := by
    rw [mul_div_mul_left _ _ hDp.ne',←Real.rpow_sub hσp]
    congr 1
    ring
  have hl : Real.log (5*σ+1)≤Real.log 6+Real.log σ := by
    rw [←Real.log_mul (by norm_num : (6:ℝ)≠0) hσp.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hn : 0≤Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1) := by
    have := Real.log_nonneg hσ
    positivity
  have hd := div_le_div_of_nonneg_left hn (Real.rpow_pos_of_pos hσp _) hs
  have hl' : (Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))≤
      (Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+2*(Real.log σ/σ^(3*b)) := by
    calc
      _ ≤ (Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1))/(D*σ^(2*b)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1))/σ^(3*b) := hd
      _ = _ := by ring
  have hf : 2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))≤
      2*(σ^(-b)+(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+2*(Real.log σ/σ^(3*b))) := by
    calc
      _ = 2*((D*σ^b)/(D*σ^(2*b))+
        (Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))) := by ring
      _ ≤ _ := by rw [he];linarith
  exact add_le_add hf (mul_le_mul_of_nonneg_left (reciprocal_bad_uniform hσ hb hD hC) (by positivity))

theorem eventually_reciprocal_endpoints {b : ℝ} (hb : 0<b) (C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop,∀ D : ℝ,σ^b≤D→
      reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤ε ∧
      2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤1/2 := by
  have ht := tendsto_rpow_neg_atTop hb
  have h3 : 0<3*b := by positivity
  have hn := tendsto_rpow_neg_atTop h3
  have hc : Tendsto (fun σ : ℝ=>C/σ^(3*b)) atTop (𝓝 0) :=
    (tendsto_rpow_atTop h3).const_div_atTop C
  have he : Tendsto (fun σ : ℝ=>Real.exp (-σ^(3*b))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop h3)
  have hbad : Tendsto (fun σ : ℝ=>Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b))) atTop (𝓝 0) := by
    simpa using he.add ((ht.add hc).const_mul 50)
  have hc' : Tendsto (fun σ : ℝ=>(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b))
      atTop (𝓝 0) :=
    (tendsto_rpow_atTop h3).const_div_atTop (Real.log 32+Real.log 33+2*(Real.log 6+1))
  have hl := (isLittleO_log_rpow_atTop h3).tendsto_div_nhds_zero
  have hcore := (((ht.add hc').add (hl.const_mul 2)).const_mul 2).add (hbad.const_mul (2*Real.exp 1))
  simp only [add_zero,mul_zero] at hcore
  filter_upwards [eventually_ge_atTop (1:ℝ),hbad.eventually_lt_const hε,
    hcore.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with σ hσ he hc
  intro D hD
  exact ⟨(reciprocal_bad_uniform hσ hb hD hC).trans he.le,
    (reciprocal_core_uniform hσ hb hD hC).trans hc.le⟩

lemma publicRetentionError_bound {σ b H : ℝ} (hσ : 1≤σ) (hH : 0≤H) (hH' : H≤σ^b) :
    publicRetentionError σ b H≤publicRetentionEnvelope σ b := by
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hEq : 0<Real.exp σ := Real.exp_pos _
  have hpow : 0<σ^(-1000*b) := Real.rpow_pos_of_pos hp _
  have hε : 0≤σ^(-2000*b)/Real.exp σ := by positivity
  have hmax : publicRetentionError σ b H≤publicRetentionError σ b (σ^b) := by
    unfold publicRetentionError
    dsimp only
    apply add_le_add
    · apply mul_le_mul hH' _ (by positivity) (by positivity)
      apply add_le_add _ le_rfl
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hH' (by norm_num)) (by positivity)) (by positivity)) (by positivity)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity))
        (by positivity)
  have he : Real.exp (-Real.exp σ)≤Real.exp (-σ) := by
    apply Real.exp_le_exp.mpr
    have := Real.add_one_le_exp σ
    linarith
  have hr1 : σ^b*σ^b*σ^(-2000*b)=σ^(-1998*b) := by
    rw [←Real.rpow_add hp,←Real.rpow_add hp]
    congr 1
    ring
  have hr2 : σ^b/σ^(-1000*b)*σ^(-2000*b)=σ^(-999*b) := by
    rw [←Real.rpow_sub hp,←Real.rpow_add hp]
    congr 1
    ring
  have hr3 : σ^b*σ^(-2000*b)=σ^(-1999*b) := by
    rw [←Real.rpow_add hp]
    congr 1
    ring
  have hrewrite : publicRetentionError σ b (σ^b)=
      (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)^2*320016)*σ^(-1998*b)+
      ((4*Real.exp 1)^2*320016)*σ^(-999*b)+5*(σ^b*Real.exp (-Real.exp σ))+
      (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008)*σ^(-1999*b)+
      (2*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008)*σ^(-2000*b) := by
    rw [←hr1,←hr2,←hr3]
    unfold publicRetentionError
    field_simp
    ring
  apply hmax.trans
  rw [hrewrite]
  unfold publicRetentionEnvelope
  have hh:=mul_le_mul_of_nonneg_left he (le_of_lt (Real.rpow_pos_of_pos hp b))
  linarith

lemma publicRetentionEnvelope_tendsto {b : ℝ} (hb : 0<b) :
    Tendsto (fun σ=>publicRetentionEnvelope σ b) atTop (𝓝 0) := by
  have h1:=tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<1998) hb)
  have h2:=tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<999) hb)
  have h3:=tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b 1 zero_lt_one
  have h4:=tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<1999) hb)
  have h5:=tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<2000) hb)
  simpa only [publicRetentionEnvelope,neg_mul,one_mul,neg_one_mul,mul_zero,add_zero] using
    ((((h1.const_mul (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)^2*320016)).add
      (h2.const_mul ((4*Real.exp 1)^2*320016))).add (h3.const_mul 5)).add
      (h4.const_mul (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008))).add
      (h5.const_mul (2*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008))

theorem eventually_retention_error {b : ℝ} (hb : 0<b) (C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop,∀ (D H : ℝ),σ^b≤D→0≤H→H≤σ^b→
      2*reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C+publicRetentionError σ b H≤ε := by
  filter_upwards [eventually_reciprocal_endpoints hb C (ε/4) hC (by positivity),
    (publicRetentionEnvelope_tendsto hb).eventually_lt_const (show 0<ε/2 by positivity),
    eventually_ge_atTop (1:ℝ)] with σ hbad herr hσ
  intro D H hD hH hH'
  have h1:=(hbad D hD).1
  have h2:=(publicRetentionError_bound hσ hH hH').trans herr.le
  linarith
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]

namespace ReciprocalWindows
local instance windowLevelsBlockDE_r33679f_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.windowLevelsIndexDE
variable {p : Law (Slots w r→FlagPair K V)} {u : Slots w r→ℝ}
  {sel : (Fin w×Bool)→Fin r} {e : I→Fin w} {s : ℝ}
  (W : ReciprocalWindows p u sel e s)

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma first_domination (i : I) (a : ℙ K V) :
    (∑ A,(W.early i).firstLaw A*uniformWeight (W.firstSupport i A) a) ≤
      (4*Real.exp 1)*W.firstReference i a := by
  exact repaired_levels_conditioned_domination _ _ _ _ _ (by positivity)
    (fun A h=>((W.early i).first_good A h).2.1) (W.early i).first_dom a
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma second_domination (i : I) (b : ℙ K (Dual K V)) :
    (∑ B,(W.late i).secondLaw B*uniformWeight (W.secondSupport i B) b) ≤
      (4*Real.exp 1)*W.secondReference i b := by
  exact repaired_levels_conditioned_domination _ _ _ _ _ (by positivity)
    (fun B h=>((W.late i).second_good B h).2.1) (W.late i).second_dom b

omit [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma support_product (k : ℝ) (hdrop : ∀ i,u (earlySlot sel (e i))-u (lateSlot sel (e i)) ≤ k)
    (i : I) (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) :
    (Nat.card K:ℝ)^5*Real.exp (-(k+2*s+Real.log 4)) ≤
      ((W.firstSupport i A).card:ℝ)*(W.secondSupport i B).card := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hh:=pivot_support_product (Nat.card K) (u (earlySlot sel (e i))) (u (lateSlot sel (e i)))
    s k (W.firstSupport i A).card (W.secondSupport i B).card hq (hdrop i)
    ((W.early i).first_size _ ((W.early i).firstLaw.repair_positive A))
    ((W.late i).second_size _ ((W.late i).secondLaw.repair_positive B))
  have he : Real.exp (-(k+2*s+Real.log 4))=Real.exp (-k-2*s)/4 := by
    rw [show -(k+2*s+Real.log 4)=(-k-2*s)-Real.log 4 by ring,
      Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<4)]
  simpa only [he,mul_div_assoc] using hh

omit [Finite K] [Nonempty (Fin r)] in
lemma reference_sparse [Preorder I] (hdim : finrank K V=5) (he : Monotone e)
    (d ε : ℝ)
    (hcons : ∀ x,0<p x → ∀ i j,slotEmbedding i < slotEmbedding j → Incident (x i).1 (x j).2 → Incident (x j).1 (x i).2)
    (hgood : ∀ i,indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (earlySlot sel (e i))=0)
    (i j : I) (hij : i ≤ j) :
    relationMass Incident (W.firstReference i) (W.secondReference j) ≤ 320016*ε := by
  exact window_reference_sparse hdim p u sel _ d s ε hcons (e i) (e j) (he hij)
    (hgood i) (W.early_half i) (W.late_half j)

omit [Finite K] [Nonempty (Fin r)] in
lemma target_right_sparse [Preorder I] (hdim : finrank K V=5) (he : Monotone e)
    (d ε : ℝ)
    (hcons : ∀ x,0<p x → ∀ i j,slotEmbedding i < slotEmbedding j → Incident (x i).1 (x j).2 → Incident (x j).1 (x i).2)
    (i j : I) (hij : i ≤ j) (t : Fin (2*r))
    (hgood : indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (middleSlot (e i) t)=0) :
    relationMass Incident
      (fun a=>if a∈reciprocalGoodA (map p (fun x=>x (middleSlot (e i) t))) (u (middleSlot (e i) t)) s
        then first (map p (fun x=>x (middleSlot (e i) t))) a else 0)
      (W.secondReference j) ≤ 160008*ε :=
  window_target_right_sparse hdim p u sel _ d s ε hcons (e i) (e j) (he hij) t hgood (W.late_half j)

omit [Finite K] [Nonempty (Fin r)] in
lemma target_left_sparse [Preorder I] (hdim : finrank K V=5) (he : Monotone e)
    (d ε : ℝ)
    (hcons : ∀ x,0<p x → ∀ i j,slotEmbedding i < slotEmbedding j → Incident (x i).1 (x j).2 → Incident (x j).1 (x i).2)
    (i j : I) (hij : i ≤ j) (t : Fin (2*r))
    (hgood : indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (middleSlot (e j) t)=0) :
    relationMass Incident (W.firstReference i)
      (fun b=>if b∈reciprocalGoodB (map p (fun x=>x (middleSlot (e j) t))) (u (middleSlot (e j) t)) s
        then second (map p (fun x=>x (middleSlot (e j) t))) b else 0) ≤ 160008*ε :=
  window_target_left_sparse hdim p u sel _ d s ε hcons (e i) (e j) (he hij) t hgood (W.early_half i)
end ReciprocalWindows

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_SurvivingWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open TreeCodec
open scoped Classical
noncomputable section
variable {w : ℕ}

lemma survivingOriginal_monotone (E : Finset (Fin w)) (hE : E.Nonempty) :
    Monotone (survivingOriginal E hE) := by
  intro i j hij
  apply (E.orderEmbOfFin rfl).monotone
  change min i.val (E.card-1) ≤ min j.val (E.card-1)
  exact min_le_min_right _ hij

lemma survivingOriginal_address (E : Finset (Fin w)) (hE : E.Nonempty)
    (j : Fin E.card) :
    survivingOriginal E hE (label (finiteBalanced E.card) ((finiteRankEquiv E.card).symm j))=
      E.orderEmbOfFin rfl j := by
  unfold survivingOriginal
  congr 1
  apply Fin.ext
  change min (label (finiteBalanced E.card) ((finiteRankEquiv E.card).symm j)).val (E.card-1)=j.val
  rw [finiteRankEquiv_label]
  exact min_eq_left (by omega)
end
end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_SurvivingWindowCode
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
attribute [local instance] OAI.SharpRamseyFive.Marking.swcProp
local instance swcBDE_r33679f_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.swcIDE
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w)) (hE : E.Nonempty)
  {s : ℝ} (W : ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

omit [Nonempty (Fin n)] in
lemma survivingTargetFailure_eq
    (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2) (v : Fin w) (hv : v∈E) (t : Fin (2*n)) :
    survivingTargetFailure f r p u sel E hE W σ hσ hq hd c δ τ P hδ v t=
      orientedTargetFailure f r σ hσ hq hd
        (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
        W.firstSupport W.secondSupport W.first_nonempty W.second_nonempty p
        (fun x=>(x (middleSlot v t)).1) (fun x=>(x (middleSlot v t)).2)
        c δ τ P hδ (finiteBalanced E.card)
        ((finiteRankEquiv E.card).symm ⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩) := by
  unfold survivingTargetFailure survivingExperiment survivingEncoded survivingLevelLaw
  convert original_window_target_failure f r E hE σ hσ hq hd
    (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
    W.firstSupport W.secondSupport W.first_nonempty W.second_nonempty p hinc c δ τ P hδ v hv t using 1
  all_goals try with_reducible_and_instances rfl
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowDeletionCount
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
attribute [local instance] OAI.SharpRamseyFive.Marking.allWindowProp
attribute [local instance] OAI.SharpRamseyFive.Marking.allWindowTDE
local instance allWindowBDE_r33679f_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
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
lemma allWindowFailure_nonempty (hE : E.Nonempty) (v : Fin w) (t : Fin (2*n)) :
    allWindowFailure f r p u sel E W σ hσ hq hd c δ τ P hδ v t=
      survivingTargetFailure f r p u sel E hE (W hE) σ hσ hq hd c δ τ P hδ v t := by
  simp only [allWindowFailure,allWindowExperiment,allWindowLevelLaw,allWindowEncoded,
    dite_eq_left hE,survivingTargetFailure,survivingExperiment]

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowTargetRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section

local instance (priority := high) winRetPropDE_r33679f_1 (P : Prop) : Decidable P := Classical.propDecidable P
local instance winRetBDE_r33679f_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance winRetIDE_r33679f_1 (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
lemma double_error_bound (a b c d e : ℝ) (ha : a ≤ c) (hb : b ≤ c) :
    a+b+d+e≤2*c+d+e := by linarith

theorem eventually_window_target_retention {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k s d ε C₀ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (w n : ℕ) [Nonempty (Fin n)]
      (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ)
      (sel : Fin w×Bool→Fin n) (e : I→Fin w) (he : Monotone e)
      (W : ReciprocalWindows p u sel e s)
      (hcons : ∀ x,0<p x → ∀ i j,slotEmbedding i < slotEmbedding j →
        Incident (x i).1 (x j).2 → Incident (x j).1 (x i).2)
      (hA : ∀ i,((support (first (map p (fun x=>x i)))).card:ℝ) ≤
        32*Real.exp (5*Real.log (Nat.card K)-u i))
      (hB : ∀ i,((support (second (map p (fun x=>x i)))).card:ℝ) ≤32*Real.exp (u i))
      (hflag : ∀ i,((support (map p (fun x=>x i))).card:ℝ) ≤C₀*(Nat.card K:ℝ)^4)
      (hgood : ∀ i,indexBad (4*Real.log (Nat.card K)) d ε p
        (orderedCollision p (slotEquiv w n) u s) sel (earlySlot sel (e i))=0)
      (hdrop : ∀ i,u (earlySlot sel (e i))-u (lateSlot sel (e i)) ≤ k)
      (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0 < s → 0 ≤ ε → 0 ≤ k+2*s+Real.log 4 →
      k+2*s+Real.log 4 ≤ Cb*D*σ^(6*beta η) →
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree) (t : Fin (2*n)),
      indexBad (4*Real.log (Nat.card K)) d ε p
        (orderedCollision p (slotEquiv w n) u s) sel (middleSlot (e (label tree j)) t)=0 →
      orientedTargetFailure f r σ hσ hq hd.le
        (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
        W.firstSupport W.secondSupport W.first_nonempty W.second_nonempty
        p (fun x=>(x (middleSlot (e (label tree j)) t)).1)
          (fun x=>(x (middleSlot (e (label tree j)) t)).2)
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree j ≤
      2*reciprocalBadMass s d C₀+
      tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*
        (4*Real.exp 1)^2*(320016*ε)+((Nat.card K:ℝ)/(σ^(-1000*beta η)))*
        (4*Real.exp 1)^2*(320016*ε)+5*Real.exp (-(Nat.card K:ℝ)))+
      (20*tree.height+2)*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*
        (4*Real.exp 1)*(160008*ε) := by
  filter_upwards [eventually_ordered_target_retention hη hη' Cb hCb] with σ hh
  intro D k s d ε C₀ R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 w n _ I _ _ _
    p u sel e he W hcons hA hB hflag hgood hdrop hσ hq hcard hr hL hs hε hb hbhi
  dsimp only
  intro tree hord j t ht
  have hbad:=window_bad_target p u sel (e (label tree j)) t s d ε C₀ hs
    (hA _) (hB _) (hflag _) ht
  have hright (i : I) (hi : label tree j ≤ i) :=
    W.target_right_sparse hd he d ε hcons (label tree j) i hi t ht
  have hleft (i : I) (hi : i ≤ label tree j) :=
    W.target_left_sparse hd he d ε hcons i (label tree j) hi t ht
  simp only [←map_first_value,←map_second_value] at hright hleft
  have hh':=hh D (k+2*s+Real.log 4) R L₀ q₀ K V hd hq3 I
    (fun _=>Finset (ℙ K V)) (fun _=>Finset (ℙ K (Dual K V)))
    (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
    W.firstSupport W.secondSupport W.first_nonempty W.second_nonempty
    W.firstReference W.secondReference (4*Real.exp 1) (320016*ε)
    (by positivity) (by positivity) W.first_domination W.second_domination
    (W.reference_sparse hd he d ε hcons hgood) hσ hq hcard hr hL hb hbhi
    (W.support_product k hdrop) tree hord j _ p
    (fun x=>(x (middleSlot (e (label tree j)) t)).1)
    (fun x=>(x (middleSlot (e (label tree j)) t)).2)
    (fun a=>a∈reciprocalGoodA (map p (fun x=>x (middleSlot (e (label tree j)) t)))
      (u (middleSlot (e (label tree j)) t)) s)
    (fun b=>b∈reciprocalGoodB (map p (fun x=>x (middleSlot (e (label tree j)) t)))
      (u (middleSlot (e (label tree j)) t)) s)
    (160008*ε) (by positivity) hright hleft
  apply hh'.trans
  apply double_error_bound
  · convert hbad.1 using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
  · convert hbad.2 using 1
    all_goals try with_reducible_and_instances rfl
    congr 2

end
end

open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section

local instance survRetPropDE_r33679f_1 (P : Prop) : Decidable P := Classical.propDecidable P
local instance survRetBDE_r33679f_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.survRetIDE
theorem eventually_surviving_target_retention {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k s d ε C₀ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n : ℕ) [Nonempty (Fin n)]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ)
      (sel : Fin w×Bool→Fin n) (E : Finset (Fin w)) (hE : E.Nonempty)
      (W : ReciprocalWindows p u sel (survivingOriginal E hE) s)
      (hcons : ∀x,0<p x→∀i j,slotEmbedding i < slotEmbedding j→
        Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
      (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
      (hA : ∀i,((support (first (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u i))
      (hB : ∀i,((support (second (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (u i))
      (hflag : ∀i,((support (map p (fun x=>x i))).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
      (hgood : ∀v∈E,indexBad (4*Real.log (Nat.card K)) d ε p
        (orderedCollision p (slotEquiv w n) u s) sel (earlySlot sel v)=0)
      (hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀→Range η σ D R→(L₀:ℝ)=L η σ D→
      0 < s→0≤ε→0≤k+2*s+Real.log 4→k+2*s+Real.log 4≤Cb*D*σ^(6*beta η)→
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (v : Fin w) (hv : v∈E) (t : Fin (2*n)),
      indexBad (4*Real.log (Nat.card K)) d ε p
        (orderedCollision p (slotEquiv w n) u s) sel (middleSlot v t)=0→
      survivingTargetFailure f r p u sel E hE W σ hσ hq hd.le
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) v t≤
      2*reciprocalBadMass s d C₀+
      (finiteBalanced E.card).height*(20*(finiteBalanced E.card).height*
        (50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*
        (4*Real.exp 1)^2*(320016*ε)+((Nat.card K:ℝ)/(σ^(-1000*beta η)))*
        (4*Real.exp 1)^2*(320016*ε)+5*Real.exp (-(Nat.card K:ℝ)))+
      (20*(finiteBalanced E.card).height+2)*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*
        (4*Real.exp 1)*(160008*ε) := by
  filter_upwards [eventually_window_target_retention hη hη' Cb hCb] with σ hh
  intro D k s d ε C₀ R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 w n _ p u sel E hE W
    hcons hinc hA hB hflag hgood hdrop hσ hq hcard hr hL hs hε hb hbhi
  dsimp only
  intro v hv t ht
  let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let j : Fin E.card:=⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩
  have heq : survivingOriginal E hE (label (finiteBalanced E.card) ((finiteRankEquiv E.card).symm j))=v := by
    rw [survivingOriginal_address]
    exact survivorRank_original E v hv
  rw [survivingTargetFailure_eq f r p u sel E hE W σ hσ hq hd.le
    (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) hinc v hv t]
  have hh':=hh D k s d ε C₀ R L₀ q₀ K V hd hq3 w n (Fin (E.card+1)) p u sel
    (survivingOriginal E hE) (survivingOriginal_monotone E hE) W hcons hA hB hflag
    (fun i=>hgood _ (survivingOriginal_mem E hE i))
    (fun i=>hdrop _ (survivingOriginal_mem E hE i)) hσ hq hcard hr hL hs hε hb hbhi
    (finiteBalanced E.card) (finiteBalanced_ordered E.card) ((finiteRankEquiv E.card).symm j) t
  simp only [heq] at hh'
  exact hh' ht
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

section
open Module FiniteEntropy ProjectiveIncidence Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section

local instance smallFailureBDE_r33679f_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.smallFailureIDE
theorem eventually_window_failure_small_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n H : ℕ) [Nonempty (Fin n)]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ)
      (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
      (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) (D*σ^(2*beta η)))
      (hcons : ∀x,0<p x→∀i j,slotEmbedding i < slotEmbedding j→
        Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
      (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
      (hA : ∀i,((support (first (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u i))
      (hB : ∀i,((support (second (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (u i))
      (_hflag : ∀i,((support (map p (fun x=>x i))).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
      (_hJ : 4*Real.log (Nat.card K)≤J)
      (_hgood : ∀v∈E,indexBad J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) p
        (orderedCollision p (slotEquiv w n) u (D*σ^(2*beta η))) sel (earlySlot sel v)=0)
      (_hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀→Range η σ D R→(L₀:ℝ)=L η σ D→
      0≤k+2*(D*σ^(2*beta η))+Real.log 4→
      k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η)→
      w<2^H→(H:ℝ)≤σ^beta η→
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (v : Fin w) (_hv : v∈E) (t : Fin (2*n)),
      indexBad J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) p
        (orderedCollision p (slotEquiv w n) u (D*σ^(2*beta η))) sel (middleSlot v t)=0→
      allWindowFailure f r p u sel E W σ hσ hq hd.le
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) v t≤ρ := by
  have hb : 0<beta η := by unfold beta;positivity
  filter_upwards [eventually_surviving_target_retention hη hη' Cb hCb,
    eventually_retention_error hb C₀ ρ hC hρ] with σ hret hnum
  intro D k J R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 w n H _ p u sel E W
    hcons hinc hA hB hflag hJ hgood hdrop hσ hq hcard hr hL hb0 hbhi hw hH
  dsimp only
  intro v hv t ht
  have hE : E.Nonempty := ⟨v,hv⟩
  have hD : σ^beta η≤D := hr.dlo
  have hDp : 0<D := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hσ) _).trans_le hD
  rw [allWindowFailure_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE]
  have hh:=hret D k (D*σ^(2*beta η)) (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
    C₀ R L₀ q₀ K V hd hq3 w n p u sel E hE (W hE) hcons hinc hA hB hflag
    (fun v hv=>indexBad_of_larger_cap hJ _ _ _ _ (hgood v hv)) hdrop hσ hq hcard hr hL
    (by positivity) (by positivity) hb0 hbhi v hv t
    (indexBad_of_larger_cap hJ _ _ _ _ ht)
  have hheight0 : (finiteBalanced E.card).height≤H :=
    finiteBalanced_height H E.card (lt_of_le_of_lt (by simpa using Finset.card_le_univ E) hw)
  have hheight : ((finiteBalanced E.card).height:ℝ)≤σ^beta η := by
    have hh' : ((finiteBalanced E.card).height:ℝ)≤H := by exact_mod_cast hheight0
    exact hh'.trans hH
  have hn:=hnum D (finiteBalanced E.card).height hD (by positivity) hheight
  apply hh.trans
  simpa only [publicRetentionError,hq,add_assoc] using hn
end
end

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology

end SharpRamseyFive.Marking

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.Marking.eventually_window_failure_small_oai := @OAI.SharpRamseyFive.Marking.eventually_window_failure_small_oai
