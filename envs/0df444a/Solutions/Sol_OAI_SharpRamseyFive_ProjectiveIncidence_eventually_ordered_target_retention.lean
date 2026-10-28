-- Prove2me | solution 1 for OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:31:09.675111+00:00
-- url     : https://prove2.me/submissions/7b3991a5-2fa2-4357-90d0-c3520d36885c

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_eventually_ordered_tree_missing
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_orientedGuardedNode_original

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

lemma event_markov (p : Law α) (w : α → ℝ) (hw : ∀ a,0≤w a) (t : ℝ)
    (E : Finset α) (hE : ∀ a∈E,t≤w a) :
    t*eventMass p E≤∑ a,p a*w a := by
  rw [eventMass,Finset.mul_sum]
  calc
    _ ≤ ∑ a∈E,p a*w a := Finset.sum_le_sum fun a ha => by
      simpa only [mul_comm t] using mul_le_mul_of_nonneg_left (hE a ha) (p.nonneg a)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
      mul_nonneg (p.nonneg a) (hw a))

end
open scoped BigOperators Classical

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

omit [Fintype α] in
lemma uniformWeight_nonneg (S : Finset α) (a : α) : 0 ≤ uniformWeight S a := by
  unfold uniformWeight;split_ifs <;> positivity
lemma relationMass_nonneg (R : α→β→Prop) (f : α→ℝ) (g : β→ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀b,0 ≤ g b) : 0 ≤ relationMass R f g :=
  Finset.sum_nonneg (fun entry _=>mul_nonneg (hf entry.1) (hg entry.2))

end

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

omit [Fintype α] in
lemma sum_uniformWeight (X H : Finset α) :
    (∑a∈H,uniformWeight X a)=((H∩X).card:ℝ)/X.card := by
  unfold uniformWeight
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have he : H.filter (fun a=>a∈X)=H∩X := by ext a;simp
  rw [he]
  ring

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PublicComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

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

end SharpRamseyFive.FiniteEntropy

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GuardedNodeOriginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α Ω J : Type*} [Fintype Ω] [Fintype J]

lemma evictionFraction_nonneg (X C : Finset α) : 0≤evictionFraction X C := by
  unfold evictionFraction;positivity

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_AmbientEviction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A Ω : Type*} [Fintype A] [Fintype Ω]

lemma not_mem_ambientTest (a : A) (Y : Option (Finset A)) :
    a∉ambientTest Y ↔ Excludes a Y := by cases Y <;> simp [ambientTest,Excludes]

lemma evictionFraction_ambient (X : Finset A) (Y : Option (Finset A)) :
    evictionFraction X (ambientTest Y)=∑a,uniformWeight X a*(if Excludes a Y then (1:ℝ) else 0) := by
  have hs : X\ambientTest Y=(Finset.univ.filter fun a=>Excludes a Y)∩X := by
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,
      true_and,not_mem_ambientTest,and_comm]
  unfold evictionFraction
  rw [hs,←sum_uniformWeight]
  simp only [Finset.sum_filter,mul_ite,mul_one,mul_zero]

lemma expected_ambient_eviction (p : Law Ω) (X : Finset A) (C : Ω→Option (Finset A)) :
    (∑ω,p ω*evictionFraction X (ambientTest (C ω)))=
      ∑a,uniformWeight X a*eventMass p (Finset.univ.filter fun ω=>Excludes a (C ω)) := by
  simp_rw [evictionFraction_ambient]
  simp only [eventMass,Finset.sum_filter,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EvictionDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]

lemma evictionFraction_univ (X : Finset A) : evictionFraction X Finset.univ = 0 := by
  simp [evictionFraction]

omit [Fintype A] in
lemma evictionFraction_inter (X U V : Finset A) :
    evictionFraction X (U ∩ V) ≤ evictionFraction X U + evictionFraction X V := by
  have hsub : X \ (U ∩ V) ⊆ (X \ U) ∪ (X \ V) := by
    intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union] at *
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  unfold evictionFraction
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc

omit [Fintype A] in
lemma trim_failure_inter (X U : Finset A)
    (h : ((X ∩ U).card : ℝ) < (9/10:ℝ)*X.card) :
    (1:ℝ)/10 ≤ evictionFraction X U := by
  have hp : (0:ℝ) < X.card := by
    have h0 : (0:ℝ) ≤ (X ∩ U).card := Nat.cast_nonneg _
    linarith only [h, h0]
  have he : X \ (X ∩ U) = X \ U := by ext a; simp
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := X) (s₂ := U))
  rw [he] at hc
  have hc' : ((X \ U).card : ℝ) + (X ∩ U).card = X.card := by exact_mod_cast hc
  exact (le_div_iff₀ hp).mpr (by linarith only [h, hc'])

theorem optional_inter_drift (p : Law Ω) (X U : Finset A)
    (out : Ω → Option (Finset A)) (ρ : ℝ)
    (h : (∑ ω, p ω * evictionFraction X (ReverseCap.ambientTest (out ω))) ≤ ρ) :
    (∑ ω, p ω * ((out ω).map (fun V => U ∩ V)).elim 0 (evictionFraction X)) ≤
      evictionFraction X U + ρ := by
  calc
    _ ≤ ∑ ω, p ω * (evictionFraction X U + evictionFraction X (ReverseCap.ambientTest (out ω))) := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (p.nonneg ω)
      cases ho : out ω with
      | none => simpa [ReverseCap.ambientTest, evictionFraction_univ] using evictionFraction_nonneg X U
      | some V => simpa [ReverseCap.ambientTest] using evictionFraction_inter X U V
    _ = evictionFraction X U + (∑ ω, p ω * evictionFraction X (ReverseCap.ambientTest (out ω))) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, p.sum_one, one_mul]
    _ ≤ _ := add_le_add_right h _

lemma optional_constant_drift {M : Ω → Type*} (p : Law Ω) (enc : ∀ ω, Option (M ω))
    (c : ℝ) (hc : 0 ≤ c) :
    (∑ ω, p ω * (enc ω).elim 0 (fun _ => c)) ≤ c := by
  calc
    _ ≤ ∑ ω, p ω * c := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (p.nonneg ω)
      cases enc ω <;> simp [hc]
    _ = _ := by rw [← Finset.sum_mul, p.sum_one, one_mul]

omit [Fintype A] in
theorem reached_trim_mass {C : Type*} [Fintype C]
    (p : Law Ω) (ctx : Ω → Option C) (domain : C → Finset A) (X : Finset A)
    (ρ : ℝ) (h : (∑ ω, p ω * (ctx ω).elim 0 (fun c => evictionFraction X (domain c))) ≤ ρ) :
    eventMass p (Finset.univ.filter (fun ω => ∃ c, ctx ω = some c ∧
      ((X ∩ domain c).card : ℝ) < (9/10:ℝ)*X.card)) ≤ 10*ρ := by
  let E := Finset.univ.filter (fun ω => ∃ c, ctx ω = some c ∧
    ((X ∩ domain c).card : ℝ) < (9/10:ℝ)*X.card)
  have hm := event_markov p (fun ω => (ctx ω).elim 0 (fun c => evictionFraction X (domain c)))
    (by intro ω; cases ctx ω with
        | none => exact le_rfl
        | some c => exact evictionFraction_nonneg _ _)
    (1/10) E (by
      intro ω hω
      obtain ⟨c, he, ht⟩ := (Finset.mem_filter.mp hω).2
      simpa [he] using trim_failure_inter X (domain c) ht)
  change eventMass p E ≤ _
  linarith only [hm, h]

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_TargetLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open ReverseCap
open scoped Classical BigOperators
noncomputable section
variable {Ω A B : Type*} [Fintype Ω]

local instance (priority := high) targetLossPropDecidable_r0311ea_1 (P : Prop) : Decidable P := Classical.propDecidable P
lemma target_mass_or (p : Law Ω) (P Q : Ω → Prop) :
    eventMass p (Finset.univ.filter (fun ω => P ω ∨ Q ω)) ≤
      eventMass p (Finset.univ.filter P) + eventMass p (Finset.univ.filter Q) := by
  simp only [eventMass, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]; linarith [p.nonneg ω]

lemma eventMass_filter_or7 (p : Law Ω) (P Q R S T U V : Ω → Prop) :
    eventMass p (Finset.univ.filter (fun ω => (((((P ω ∨ Q ω) ∨ R ω) ∨ S ω) ∨ T ω) ∨ U ω) ∨ V ω)) ≤
      eventMass p (Finset.univ.filter P) + eventMass p (Finset.univ.filter Q) +
      eventMass p (Finset.univ.filter R) + eventMass p (Finset.univ.filter S) +
      eventMass p (Finset.univ.filter T) + eventMass p (Finset.univ.filter U) +
      eventMass p (Finset.univ.filter V) := by
  have h2 := target_mass_or p P Q
  have h3 := target_mass_or p (fun ω => P ω ∨ Q ω) R
  have h4 := target_mass_or p (fun ω => (P ω ∨ Q ω) ∨ R ω) S
  have h5 := target_mass_or p (fun ω => ((P ω ∨ Q ω) ∨ R ω) ∨ S ω) T
  have h6 := target_mass_or p (fun ω => (((P ω ∨ Q ω) ∨ R ω) ∨ S ω) ∨ T ω) U
  have h7 := target_mass_or p (fun ω => ((((P ω ∨ Q ω) ∨ R ω) ∨ S ω) ∨ T ω) ∨ U ω) V
  linarith only [h2,h3,h4,h5,h6,h7]

theorem target_loss_split (p : Law Ω) (a : Ω → A) (b : Ω → B)
    (goodA : A → Prop) (goodB : B → Prop)
    (ctx : Ω → Option (Finset A × Finset B)) (caps : Ω → Option (Finset B × Finset A))
    (hcoh : ∀ ω, caps ω≠none → ctx ω≠none) :
    eventMass p (Finset.univ.filter (fun ω => ¬TargetCovered (ctx ω) (caps ω) (a ω) (b ω))) ≤
      eventMass p (Finset.univ.filter (fun ω => ¬goodA (a ω))) +
      eventMass p (Finset.univ.filter (fun ω => ¬goodB (b ω))) +
      eventMass p (Finset.univ.filter (fun ω => caps ω=none)) +
      eventMass p (Finset.univ.filter (fun ω => goodA (a ω) ∧ ∃ C, ctx ω=some C ∧ a ω∉C.1)) +
      eventMass p (Finset.univ.filter (fun ω => goodB (b ω) ∧ ∃ C, ctx ω=some C ∧ b ω∉C.2)) +
      eventMass p (Finset.univ.filter (fun ω => goodA (a ω) ∧ Excludes (a ω) ((caps ω).map Prod.snd))) +
      eventMass p (Finset.univ.filter (fun ω => goodB (b ω) ∧ Excludes (b ω) ((caps ω).map Prod.fst))) := by
  let P := fun ω => ¬goodA (a ω)
  let Q := fun ω => ¬goodB (b ω)
  let R := fun ω => caps ω=none
  let S := fun ω => goodA (a ω) ∧ ∃ C, ctx ω=some C ∧ a ω∉C.1
  let T := fun ω => goodB (b ω) ∧ ∃ C, ctx ω=some C ∧ b ω∉C.2
  let U := fun ω => goodA (a ω) ∧ Excludes (a ω) ((caps ω).map Prod.snd)
  let V := fun ω => goodB (b ω) ∧ Excludes (b ω) ((caps ω).map Prod.fst)
  have hs : ∀ ω, ¬TargetCovered (ctx ω) (caps ω) (a ω) (b ω) →
      (((((P ω ∨ Q ω) ∨ R ω) ∨ S ω) ∨ T ω) ∨ U ω) ∨ V ω := by
    intro ω hn
    by_cases hga : goodA (a ω)
    · by_cases hgb : goodB (b ω)
      · cases hd : caps ω with
        | none => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hd))))
        | some D =>
          obtain ⟨C,hc⟩ := Option.ne_none_iff_exists'.mp (hcoh ω (by simp [hd]))
          by_cases ha : a ω∈C.1
          · by_cases hb : b ω∈C.2
            · by_cases ha' : a ω∈D.2
              · by_cases hb' : b ω∈D.1
                · exact (hn ⟨C,D,hc,hd,ha,hb,ha',hb'⟩).elim
                · exact Or.inr ⟨hgb, by simp [Excludes, hd, hb']⟩
              · exact Or.inl (Or.inr ⟨hga, by simp [Excludes, hd, ha']⟩)
            · exact Or.inl (Or.inl (Or.inr ⟨hgb,C,hc,hb⟩))
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hga,C,hc,ha⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hgb)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hga)))))
  exact (eventMass_filter_mono p _ _ hs).trans (eventMass_filter_or7 p P Q R S T U V)
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IndependentTargetLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open ReverseCap
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ Z T A B : Type*} [Fintype Ω] [Fintype Θ] [Fintype Z] [Fintype T]
  [Fintype A] [Fintype B]

local instance (priority := high) independentTargetPropDecidable_r0311ea_1 (P : Prop) : Decidable P := Classical.propDecidable P
lemma independent_target_event (p : Law Ω) (q : Law Θ) (P : Ω → Θ → Prop) :
    eventMass (adaptiveLaw p (fun _ => q))
      (Finset.univ.filter (fun z => P z.1 z.2)) =
        ∑ x, p x * eventMass q (Finset.univ.filter (P x)) := by
  simp only [eventMass, Finset.sum_filter, Fintype.sum_prod_type, adaptiveLaw,
    Finset.mul_sum, mul_ite, mul_zero]

lemma independent_target_endpoint_event (p : Law Ω) (q : Law Θ) (endpoint : Ω → B)
    (good : B → Prop) (P : B → Θ → Prop) :
    eventMass (adaptiveLaw p (fun _ => q))
      (Finset.univ.filter (fun z => good (endpoint z.1) ∧ P (endpoint z.1) z.2)) =
      ∑ b, (if good b then map p endpoint b else 0) *
        eventMass q (Finset.univ.filter (P b)) := by
  calc
    _ = ∑ x, p x * eventMass q (Finset.univ.filter
        (fun ξ => good (endpoint x) ∧ P (endpoint x) ξ)) := by
      simp only [eventMass, Finset.sum_filter, Fintype.sum_prod_type, adaptiveLaw,
        Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ x, p x * (if good (endpoint x) then
        eventMass q (Finset.univ.filter (P (endpoint x))) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hg : good (endpoint x) <;> simp [hg, eventMass]
    _ = ∑ b, map p endpoint b * (if good b then
        eventMass q (Finset.univ.filter (P b)) else 0) := (sum_map p endpoint (fun b => if good b then eventMass q (Finset.univ.filter (P b)) else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs <;> simp

theorem independent_target_loss (p : Law Ω) (q : Law Θ) (a : Ω → A) (b : Ω → B)
    (goodA : A → Prop) (goodB : B → Prop)
    (ctx : Θ → Option (Finset A × Finset B)) (caps : Θ → Option (Finset B × Finset A))
    (hcoh : ∀ t, caps t≠none → ctx t≠none) :
    eventMass (adaptiveLaw p (fun _ => q)) (Finset.univ.filter
      (fun z => ¬TargetCovered (ctx z.2) (caps z.2) (a z.1) (b z.1))) ≤
      eventMass p (Finset.univ.filter (fun x => ¬goodA (a x))) +
      eventMass p (Finset.univ.filter (fun x => ¬goodB (b x))) +
      eventMass q (Finset.univ.filter (fun t => caps t=none)) +
      (∑ x, (if goodA x then map p a x else 0)*eventMass q
        (Finset.univ.filter (fun t => ∃ C, ctx t=some C ∧ x∉C.1))) +
      (∑ y, (if goodB y then map p b y else 0)*eventMass q
        (Finset.univ.filter (fun t => ∃ C, ctx t=some C ∧ y∉C.2))) +
      (∑ x, (if goodA x then map p a x else 0)*eventMass q
        (Finset.univ.filter (fun t => Excludes x ((caps t).map Prod.snd)))) +
      (∑ y, (if goodB y then map p b y else 0)*eventMass q
        (Finset.univ.filter (fun t => Excludes y ((caps t).map Prod.fst)))) := by
  have h := target_loss_split (adaptiveLaw p (fun _ => q)) (fun z => a z.1) (fun z => b z.1)
    goodA goodB (fun z => ctx z.2) (fun z => caps z.2) (fun z => hcoh z.2)
  rw [adaptive_event_first p (fun _ => q) (fun x => ¬goodA (a x)),
    adaptive_event_first p (fun _ => q) (fun x => ¬goodB (b x)),
    adaptive_event_second p (fun _ => q) (fun t => caps t=none),
    ← Finset.sum_mul, p.sum_one, one_mul] at h
  rw [independent_target_endpoint_event p q a goodA (fun x t => ∃ C, ctx t=some C ∧ x∉C.1),
    independent_target_endpoint_event p q b goodB (fun y t => ∃ C, ctx t=some C ∧ y∉C.2),
    independent_target_endpoint_event p q a goodA (fun x t => Excludes x ((caps t).map Prod.snd)),
    independent_target_endpoint_event p q b goodB (fun y t => Excludes y ((caps t).map Prod.fst))] at h
  exact h
end
end

open scoped Classical BigOperators
noncomputable section
variable {Z T A : Type*} [Fintype Z] [Fintype T] [Fintype A]
local instance (priority := high) targetProductPropDecidable_r0311ea_1 (P : Prop) : Decidable P := Classical.propDecidable P
lemma independent_target_event_general (μ : Law Z) (q : Law T) (P : Z × T → Prop) :
    eventMass (adaptiveLaw μ (fun _ => q)) (Finset.univ.filter P) =
      ∑ z, μ z*eventMass q (Finset.univ.filter (fun t => P (z,t))) := by
  exact independent_target_event μ q (fun z t => P (z,t))

lemma independent_weighted_event (μ : Law Z) (q : Law T) (g : A → ℝ)
    (P : A → Z × T → Prop) :
    (∑ a, g a*eventMass (adaptiveLaw μ (fun _ => q))
      (Finset.univ.filter (P a))) =
    ∑ z, μ z*(∑ a, g a*eventMass q (Finset.univ.filter (fun t => P a (z,t)))) := by
  simp_rw [independent_target_event_general μ q]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  ring
end

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) [∀a c,Fintype (Ω a c)]
  (p : ∀a c,Law (Ω a c))

lemma root_tape_law (a : A) (l r : BinaryTree A) (c : C) :
    map (tapeLaw Ω p (.node a l r)) (fun ω=>ω.1 c)=p a c := by
  exact (map_independent_left (piLaw (p a))
    (adaptiveLaw (tapeLaw Ω p l) (fun _=>tapeLaw Ω p r)) (fun ω=>ω c)).trans (piLaw_eval (p a) c)

lemma root_output_law {D : Type z} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C) (out : Ω a c→D) :
    map (tapeLaw Ω p (.node a l r)) (fun ω=>out (ω.1 c))=map (p a c) out := by
  have h := congrArg (fun q=>map q out) (root_tape_law Ω p a l r c)
  simpa only [map_comp,Function.comp_def] using h

lemma left_continuation_law {D : Type z} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C)
    (nextContext : Ω a c→Option C) (out : Option C→Tape Ω l→D) :
    map (tapeLaw Ω p (.node a l r)) (fun ω=>out (nextContext (ω.1 c)) ω.2.1)=
      map (adaptiveLaw (map (p a c) nextContext)
        (fun C=>map (tapeLaw Ω p l) (out C))) Prod.snd := by
  rw [tapeLaw]
  have h := public_composition (piLaw (p a))
    (adaptiveLaw (tapeLaw Ω p l) (fun _=>tapeLaw Ω p r))
    (fun ω=>nextContext (ω c)) (fun C ω=>out C ω.1)
    (fun C=>map (tapeLaw Ω p l) (out C))
    (fun C=>map_independent_left _ _ (out C))
  have hc : map (piLaw (p a)) (fun ω=>nextContext (ω c))=map (p a c) nextContext := by
    have ht := congrArg (fun q=>map q nextContext) (piLaw_eval (p a) c)
    simpa only [map_comp,Function.comp_def] using ht
  rw [hc] at h
  exact h

lemma right_continuation_law {D : Type z} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C)
    (nextContext : Ω a c→Option C) (out : Option C→Tape Ω r→D) :
    map (tapeLaw Ω p (.node a l r)) (fun ω=>out (nextContext (ω.1 c)) ω.2.2)=
      map (adaptiveLaw (map (p a c) nextContext)
        (fun C=>map (tapeLaw Ω p r) (out C))) Prod.snd := by
  rw [tapeLaw]
  have h := public_composition (piLaw (p a))
    (adaptiveLaw (tapeLaw Ω p l) (fun _=>tapeLaw Ω p r))
    (fun ω=>nextContext (ω c)) (fun C ω=>out C ω.2)
    (fun C=>map (tapeLaw Ω p r) (out C))
    (fun C=>map_independent_right _ _ (out C))
  have hc : map (piLaw (p a)) (fun ω=>nextContext (ω c))=map (p a c) nextContext := by
    have ht := congrArg (fun q=>map q nextContext) (piLaw_eval (p a) c)
    simpa only [map_comp,Function.comp_def] using ht
  rw [hc] at h
  exact h
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
universe u v w z s
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A → C → Type w) [∀ a c, Fintype (Ω a c)]
  (M : ∀ a c, Ω a c → Type z)
  (left right : ∀ a c t, M a c t → C)

variable {D : Type s}

theorem probe_event_bound [Fintype D] (p : ∀ a c, Law (Ω a c))
    (enc : ∀ a c t, Option (M a c t)) (test : ∀ a c, Ω a c → Option D)
    (P : Option D → Prop) (hP : ¬ P none) (B : A → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hlocal : ∀ a c, eventMass (map (p a c)
      (fun t => test a c t)) (Finset.univ.filter P) ≤ B a)
    (b : BinaryTree A) (c : C) (j : Address b) :
    eventMass (map (tapeLaw Ω p b) (fun ω => probe Ω M left right enc test b ω c j))
      (Finset.univ.filter P) ≤ B (label b j) := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    rcases j with j | (j | j)
    · change eventMass (map (tapeLaw Ω p (.node a l r))
        (fun ω => test a c (ω.1 c))) _ ≤ B a
      rw [root_output_law Ω p a l r c (fun t => test a c t)]
      exact hlocal a c
    · let next : Ω a c → Option C := fun t => (enc a c t).map (left a c t)
      let f : Option C → Tape Ω l → Option D := fun x ω =>
        x.elim none (fun c' => probe Ω M left right enc test l ω c' j)
      change eventMass (map (tapeLaw Ω p (.node a l r))
        (fun ω => f (next (ω.1 c)) ω.2.1)) _ ≤ _
      rw [left_continuation_law Ω p a l r c next f, eventMass_map_filter]
      apply adaptive_event_second_le
      intro x
      cases x with
      | none =>
        rw [eventMass_map_filter]
        simp only [f, Option.elim_none]
        simp [hP, eventMass, hB]
      | some c' => exact ihl c' j
    · let next : Ω a c → Option C := fun t => (enc a c t).map (right a c t)
      let f : Option C → Tape Ω r → Option D := fun x ω =>
        x.elim none (fun c' => probe Ω M left right enc test r ω c' j)
      change eventMass (map (tapeLaw Ω p (.node a l r))
        (fun ω => f (next (ω.1 c)) ω.2.2)) _ ≤ _
      rw [right_continuation_law Ω p a l r c next f, eventMass_map_filter]
      apply adaptive_event_second_le
      intro x
      cases x with
      | none =>
        rw [eventMass_map_filter]
        simp only [f, Option.elim_none]
        simp [hP, eventMass, hB]
      | some c' => exact ihr c' j

theorem observe_event_bound [Fintype D] (p : ∀ a c, Law (Ω a c))
    (enc : ∀ a c t, Option (M a c t)) (out : ∀ a c t, M a c t → D)
    (P : Option D → Prop) (hP : ¬ P none) (B : A → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hlocal : ∀ a c, eventMass (map (p a c)
      (fun t => (enc a c t).map (out a c t))) (Finset.univ.filter P) ≤ B a)
    (b : BinaryTree A) (c : C) (j : Address b) :
    eventMass (map (tapeLaw Ω p b) (fun ω => observe Ω M left right enc out b ω c j))
      (Finset.univ.filter P) ≤ B (label b j) :=
  probe_event_bound Ω M left right p enc _ P hP B hB hlocal b c j

end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma sum_adaptive (p : Law α) (q : α → Law β) (f : α × β → ℝ) :
    (∑ z, adaptiveLaw p q z * f z) = ∑ a, p a * (∑ b, q a b * f (a,b)) := by
  simp only [adaptiveLaw, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
universe u v w z s
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A → C → Type w) [∀ a c, Fintype (Ω a c)]
  (p : ∀ a c, Law (Ω a c))

lemma left_continuation_mean {D : Type s} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C)
    (next : Ω a c → Option C) (out : Option C → Tape Ω l → D) (f : D → ℝ) :
    (∑ ω, tapeLaw Ω p (.node a l r) ω * f (out (next (ω.1 c)) ω.2.1)) =
      ∑ t, p a c t * (∑ ω, tapeLaw Ω p l ω * f (out (next t) ω)) := by
  have h := congrArg (fun q : Law D => ∑ x, q x * f x)
    (left_continuation_law Ω p a l r c next out)
  simpa only [sum_map, sum_adaptive, Prod.snd] using h

lemma right_continuation_mean {D : Type s} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C)
    (next : Ω a c → Option C) (out : Option C → Tape Ω r → D) (f : D → ℝ) :
    (∑ ω, tapeLaw Ω p (.node a l r) ω * f (out (next (ω.1 c)) ω.2.2)) =
      ∑ t, p a c t * (∑ ω, tapeLaw Ω p r ω * f (out (next t) ω)) := by
  have h := congrArg (fun q : Law D => ∑ x, q x * f x)
    (right_continuation_law Ω p a l r c next out)
  simpa only [sum_map, sum_adaptive, Prod.snd] using h

variable (M : ∀ a c, Ω a c → Type z)
  (left right : ∀ a c t, M a c t → C)

lemma pathBudget_nonneg (ρL ρR : A → ℝ) (hL : ∀ a, 0 ≤ ρL a) (hR : ∀ a, 0 ≤ ρR a)
    (b : BinaryTree A) (j : Address b) : 0 ≤ pathBudget ρL ρR b j := by
  induction b with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    rcases j with j | (j | j)
    · exact le_rfl
    · exact add_nonneg (hL a) (ihl j)
    · exact add_nonneg (hR a) (ihr j)

theorem context_cost_bound (enc : ∀ a c t, Option (M a c t)) (cost : C → ℝ)
    (_hcost : ∀ c, 0 ≤ cost c) (ρL ρR : A → ℝ)
    (hL : ∀ a, 0 ≤ ρL a) (hR : ∀ a, 0 ≤ ρR a)
    (hleft : ∀ a c, (∑ t, p a c t * ((enc a c t).map (left a c t)).elim 0 cost) ≤ cost c + ρL a)
    (hright : ∀ a c, (∑ t, p a c t * ((enc a c t).map (right a c t)).elim 0 cost) ≤ cost c + ρR a)
    (b : BinaryTree A) (c : C) (j : Address b) :
    (∑ ω, tapeLaw Ω p b ω * (contextAt Ω M left right enc b ω c j).elim 0 cost) ≤
      cost c + pathBudget ρL ρR b j := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    rcases j with j | (j | j)
    · simp only [contextAt, probe, Option.elim_some, pathBudget, ← Finset.sum_mul,
        (tapeLaw Ω p (.node a l r)).sum_one, one_mul, add_zero, le_refl]
    · let next : Ω a c → Option C := fun t => (enc a c t).map (left a c t)
      let out : Option C → Tape Ω l → Option C := fun x ω =>
        x.elim none (fun c' => contextAt Ω M left right enc l ω c' j)
      change (∑ ω, tapeLaw Ω p (.node a l r) ω *
        (out (next (ω.1 c)) ω.2.1).elim 0 cost) ≤ cost c + (ρL a + pathBudget ρL ρR l j)
      rw [left_continuation_mean Ω p a l r c next out (fun x => x.elim 0 cost)]
      have ht (t : Ω a c) : (∑ ω, tapeLaw Ω p l ω * (out (next t) ω).elim 0 cost) ≤
          (next t).elim 0 cost + pathBudget ρL ρR l j := by
        cases hx : next t with
        | none => simpa [hx, out] using pathBudget_nonneg ρL ρR hL hR l j
        | some c' => simpa [hx, out] using ihl c' j
      calc
        _ ≤ ∑ t, p a c t * ((next t).elim 0 cost + pathBudget ρL ρR l j) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ht t) ((p a c).nonneg t)
        _ = (∑ t, p a c t * (next t).elim 0 cost) + pathBudget ρL ρR l j := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (p a c).sum_one, one_mul]
        _ ≤ _ := by have h := hleft a c; dsimp only [next]; linarith only [h]
    · let next : Ω a c → Option C := fun t => (enc a c t).map (right a c t)
      let out : Option C → Tape Ω r → Option C := fun x ω =>
        x.elim none (fun c' => contextAt Ω M left right enc r ω c' j)
      change (∑ ω, tapeLaw Ω p (.node a l r) ω *
        (out (next (ω.1 c)) ω.2.2).elim 0 cost) ≤ cost c + (ρR a + pathBudget ρL ρR r j)
      rw [right_continuation_mean Ω p a l r c next out (fun x => x.elim 0 cost)]
      have ht (t : Ω a c) : (∑ ω, tapeLaw Ω p r ω * (out (next t) ω).elim 0 cost) ≤
          (next t).elim 0 cost + pathBudget ρL ρR r j := by
        cases hx : next t with
        | none => simpa [hx, out] using pathBudget_nonneg ρL ρR hL hR r j
        | some c' => simpa [hx, out] using ihr c' j
      calc
        _ ≤ ∑ t, p a c t * ((next t).elim 0 cost + pathBudget ρL ρR r j) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ht t) ((p a c).nonneg t)
        _ = (∑ t, p a c t * (next t).elim 0 cost) + pathBudget ρL ρR r j := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (p a c).sum_one, one_mul]
        _ ≤ _ := by have h := hright a c; dsimp only [next]; linarith only [h]

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeOriginalTrims
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec

section
open FiniteEntropy BinaryTree ReverseCap
open scoped Classical BigOperators
universe u v w z
variable {I : Type u} {A B : Type v} [Fintype A] [Fintype B]
  (Ω : I → (Finset A × Finset B) → Type w) [∀ i c, Fintype (Ω i c)]
  (p : ∀ i c, Law (Ω i c)) (M : ∀ i c, Ω i c → Type z)
  (out : ∀ i c t, M i c t → Finset A × Finset B)

theorem first_context_eviction (enc : ∀ i c t, Option (M i c t))
    (X : Finset A) (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcap : ∀ i c, (∑ t, p i c t * evictionFraction X
      (ambientTest ((enc i c t).map (fun m => (out i c t m).1)))) ≤ ρ i)
    (b : BinaryTree I) (c : Finset A × Finset B) (j : Address b) :
    (∑ ω, tapeLaw Ω p b ω *
      (contextAt Ω M (capLeft Ω M out) (capRight Ω M out) enc b ω c j).elim 0
        (fun C => evictionFraction X C.1)) ≤
      evictionFraction X c.1 + pathBudget ρ (fun _ => 0) b j := by
  apply context_cost_bound Ω p M (capLeft Ω M out) (capRight Ω M out) enc
    (fun C => evictionFraction X C.1) (fun _ => evictionFraction_nonneg _ _) ρ (fun _ => 0)
    hρ (fun _ => le_rfl)
  · intro i c
    convert optional_inter_drift (p i c) X c.1
      (fun t => (enc i c t).map (fun m => (out i c t m).1)) (ρ i) (hcap i c) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro t ht
    cases enc i c t <;> rfl
  · intro i c
    simpa only [add_zero] using (show
      (∑ t, p i c t * ((enc i c t).map (capRight Ω M out i c t)).elim 0
        (fun C => evictionFraction X C.1)) ≤ evictionFraction X c.1 from by
      convert optional_constant_drift (p i c) (enc i c) (evictionFraction X c.1)
        (evictionFraction_nonneg _ _) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro t ht
      cases enc i c t <;> rfl)

theorem second_context_eviction (enc : ∀ i c t, Option (M i c t))
    (X : Finset B) (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcap : ∀ i c, (∑ t, p i c t * evictionFraction X
      (ambientTest ((enc i c t).map (fun m => (out i c t m).2)))) ≤ ρ i)
    (b : BinaryTree I) (c : Finset A × Finset B) (j : Address b) :
    (∑ ω, tapeLaw Ω p b ω *
      (contextAt Ω M (capLeft Ω M out) (capRight Ω M out) enc b ω c j).elim 0
        (fun C => evictionFraction X C.2)) ≤
      evictionFraction X c.2 + pathBudget (fun _ => 0) ρ b j := by
  apply context_cost_bound Ω p M (capLeft Ω M out) (capRight Ω M out) enc
    (fun C => evictionFraction X C.2) (fun _ => evictionFraction_nonneg _ _) (fun _ => 0) ρ
    (fun _ => le_rfl) hρ
  · intro i c
    simpa only [add_zero] using (show
      (∑ t, p i c t * ((enc i c t).map (capLeft Ω M out i c t)).elim 0
        (fun C => evictionFraction X C.2)) ≤ evictionFraction X c.2 from by
      convert optional_constant_drift (p i c) (enc i c) (evictionFraction X c.2)
        (evictionFraction_nonneg _ _) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro t ht
      cases enc i c t <;> rfl)
  · intro i c
    convert optional_inter_drift (p i c) X c.2
      (fun t => (enc i c t).map (fun m => (out i c t m).2)) (ρ i) (hcap i c) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro t ht
    cases enc i c t <;> rfl

theorem first_original_trim (enc : ∀ i c t, Option (M i c t))
    (X : Finset A) (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcap : ∀ i c, (∑ t, p i c t * evictionFraction X
      (ambientTest ((enc i c t).map (fun m => (out i c t m).1)))) ≤ ρ i)
    (b : BinaryTree I) (j : Address b) :
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω => ∃ C,
      contextAt Ω M (capLeft Ω M out) (capRight Ω M out) enc b ω (Finset.univ,Finset.univ) j = some C ∧
      ((X ∩ C.1).card : ℝ) < (9/10:ℝ)*X.card)) ≤
        10 * pathBudget ρ (fun _ => 0) b j := by
  apply reached_trim_mass _ _ Prod.fst X _
  simpa only [evictionFraction_univ, zero_add] using
    first_context_eviction Ω p M out enc X ρ hρ hcap b (Finset.univ,Finset.univ) j

theorem second_original_trim (enc : ∀ i c t, Option (M i c t))
    (X : Finset B) (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcap : ∀ i c, (∑ t, p i c t * evictionFraction X
      (ambientTest ((enc i c t).map (fun m => (out i c t m).2)))) ≤ ρ i)
    (b : BinaryTree I) (j : Address b) :
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω => ∃ C,
      contextAt Ω M (capLeft Ω M out) (capRight Ω M out) enc b ω (Finset.univ,Finset.univ) j = some C ∧
      ((X ∩ C.2).card : ℝ) < (9/10:ℝ)*X.card)) ≤
        10 * pathBudget (fun _ => 0) ρ b j := by
  apply reached_trim_mass _ _ Prod.snd X _
  simpa only [evictionFraction_univ, zero_add] using
    second_context_eviction Ω p M out enc X ρ hρ hcap b (Finset.univ,Finset.univ) j

end

open FiniteEntropy BinaryTree
open scoped Classical BigOperators
universe u v w z

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OriginalLevelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
variable {I W : Type*} [Fintype W]
lemma mean_pathBudget (p : W → ℝ) (ρL ρR : W → I → ℝ)
    (b : BinaryTree I) (j : Address b) :
    (∑ ω, p ω * pathBudget (ρL ω) (ρR ω) b j) =
      pathBudget (fun i => ∑ ω, p ω * ρL ω i) (fun i => ∑ ω, p ω * ρR ω i) b j := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · simp only [pathBudget, mul_zero, Finset.sum_const_zero]
    · simp only [pathBudget, mul_add, Finset.sum_add_distrib, ihl]
    · simp only [pathBudget, mul_add, Finset.sum_add_distrib, ihr]

lemma pathBudget_mono (ρL ρR τL τR : I → ℝ)
    (hL : ∀ i, ρL i ≤ τL i) (hR : ∀ i, ρR i ≤ τR i)
    (b : BinaryTree I) (j : Address b) :
    pathBudget ρL ρR b j ≤ pathBudget τL τR b j := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · rfl
    · exact add_le_add (hL i) (ihl j)
    · exact add_le_add (hR i) (ihr j)

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeDecoder
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]

lemma cap_eviction_from_domination (p : Law Ω) (R : A → B → Prop)
    (X : Finset A) (Y : Finset B) (cap : Ω → Option (Finset B)) (C : ℝ)
    (hlocal : ∀ b, eventMass p (Finset.univ.filter (fun ω => Excludes b (cap ω))) ≤
      C * ((((Finset.univ.filter (fun a => R a b)) ∩ X).card : ℝ) / X.card)) :
    (∑ ω, p ω * evictionFraction Y (ambientTest (cap ω))) ≤
      C * relationMass R (uniformWeight X) (uniformWeight Y) := by
  rw [expected_ambient_eviction, relationMass_by_target, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  rw [sum_uniformWeight]
  have hg : 0 ≤ uniformWeight Y b := by unfold uniformWeight; positivity
  have h := mul_le_mul_of_nonneg_left (hlocal b) hg
  nlinarith only [h]

end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem oriented_point_cap_eviction
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ)
    (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (X : Finset (ℙ K V)) :
    (∑ t, orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K) t *
      evictionFraction X (ambientTest ((orientedGuardedNodeEncoded f r σ hσ hq hd.le
        A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (fun m => (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)))) ≤
      (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass (fun b a => Incident a b) (uniformWeight B₀) (uniformWeight X) := by
  let enc := orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ
  let dec := orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K)
  let p := orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)
  have h := (orientedGuardedNode_original f r σ hσ hq hd hq3 A₀ UA B₀ UB
    hA₀ hB₀ c δ τ P hc hc9 hδ hτ).2
  have hh := cap_eviction_from_domination (map p (fun t => (enc t).map (dec t)))
    (fun b a => Incident a b) B₀ X (fun out => out.map Prod.snd)
    (50*(Nat.card K:ℝ)/(9*(c*δ))) (by
      intro a
      have he : (Finset.univ.filter (Incident a)) ∩ B₀ = B₀.filter (Incident a) := by
        ext b; simp [and_comm]
      simpa only [he] using h a)
  rw [sum_map] at hh
  simpa only [Option.map_map, Function.comp_def, enc, dec, p] using hh

theorem oriented_dual_cap_eviction
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ)
    (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (X : Finset (ℙ K (Dual K V))) :
    (∑ t, orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K) t *
      evictionFraction X (ambientTest ((orientedGuardedNodeEncoded f r σ hσ hq hd.le
        A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (fun m => (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1)))) ≤
      (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass Incident (uniformWeight A₀) (uniformWeight X) := by
  let enc := orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ
  let dec := orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K)
  let p := orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)
  have h := (orientedGuardedNode_original f r σ hσ hq hd hq3 A₀ UA B₀ UB
    hA₀ hB₀ c δ τ P hc hc9 hδ hτ).1
  have hh := cap_eviction_from_domination (map p (fun t => (enc t).map (dec t)))
    Incident A₀ X (fun out => out.map Prod.fst)
    (50*(Nat.card K:ℝ)/(9*(c*δ))) (by
      intro b
      have he : (Finset.univ.filter (fun a => Incident a b)) ∩ A₀ = A₀.filter (fun a => Incident a b) := by
        ext a; simp [and_comm]
      simpa only [he] using h b)
  rw [sum_map] at hh
  simpa only [Option.map_map, Function.comp_def, enc, dec, p] using hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TreeTrims
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}

theorem oriented_original_point_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (X : Finset (ℙ K V)) (b : BinaryTree I) (j : Address b) :
    eventMass (orientedPivotTreeLaw f r b) (Finset.univ.filter (fun ω => ∃ C,
      orientedPivotContextAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ b ω
        (Finset.univ,Finset.univ) j = some C ∧
      ((X ∩ C.1).card : ℝ) < (9/10:ℝ)*X.card)) ≤
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass (fun b a => Incident a b) (uniformWeight (B₀ i)) (uniformWeight X))
        (fun _ => 0) b j := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let p := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let out : ∀ i C t, M i C t → Finset (ℙ K V) × Finset (ℙ K (Dual K V)) :=
    fun _ C t m => (orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m).swap
  let enc : ∀ i C t, Option (M i C t) := fun i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t
  apply first_original_trim Ω p M out enc X
  · intro i
    apply mul_nonneg (by positivity)
    exact relationMass_nonneg _ _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _)
  · intro i C
    exact oriented_point_cap_eviction (f C) (r C) σ hσ hq hd hq3
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hc hc9 hδ hτ X

theorem oriented_original_dual_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (X : Finset (ℙ K (Dual K V))) (b : BinaryTree I) (j : Address b) :
    eventMass (orientedPivotTreeLaw f r b) (Finset.univ.filter (fun ω => ∃ C,
      orientedPivotContextAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ b ω
        (Finset.univ,Finset.univ) j = some C ∧
      ((X ∩ C.2).card : ℝ) < (9/10:ℝ)*X.card)) ≤
      10 * pathBudget (fun _ => 0)
        (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
          relationMass Incident (uniformWeight (A₀ i)) (uniformWeight X)) b j := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let p := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let out : ∀ i C t, M i C t → Finset (ℙ K V) × Finset (ℙ K (Dual K V)) :=
    fun _ C t m => (orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m).swap
  let enc : ∀ i C t, Option (M i C t) := fun i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t
  apply second_original_trim Ω p M out enc X
  · intro i
    apply mul_nonneg (by positivity)
    exact relationMass_nonneg _ _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _)
  · intro i C
    exact oriented_dual_cap_eviction (f C) (r C) σ hσ hq hd hq3
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hc hc9 hδ hτ X

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LevelTreeTrims
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma relationMass_swap (R : α → β → Prop) (f : α → ℝ) (g : β → ℝ) :
    relationMass (fun b a => R a b) g f = relationMass R f g := by
  simp only [relationMass, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring
end SharpRamseyFive.FiniteEntropy

end

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A B Ω Ξ ι Θ : Type*} [Fintype A] [Fintype B] [Fintype Ω]
  [Fintype Ξ] [Fintype ι] [Fintype Θ]

lemma relationMass_mixture_left (R : A → B → Prop) (μ : Law ι)
    (f : ι → A → ℝ) (g : B → ℝ) :
    (∑ i, μ i * relationMass R (f i) g) =
      relationMass R (fun a => ∑ i, μ i * f i a) g := by
  simp only [relationMass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

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

lemma ordered_pathBudget_bound (b : BinaryTree I) (hb : Ordered b) (j : Address b)
    (f g : I→ℝ) (ε : ℝ) (hε : 0≤ε)
    (hf : ∀ a,label b j≤a→f a≤ε) (hg : ∀ a,a≤label b j → g a≤ε) :
    pathBudget f g b j≤b.height*ε := by
  induction b with
  | nil=>exact nomatch j
  | node a l r ihl ihr=>
    obtain ⟨hleft,hright,hl,hr⟩:=hb
    have hL : (l.height:ℝ)+1≤(BinaryTree.node a l r).height := by
      simp only [BinaryTree.height,Nat.cast_add,Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 1
    have hR : (r.height:ℝ)+1≤(BinaryTree.node a l r).height := by
      simp only [BinaryTree.height,Nat.cast_add,Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right (le_max_right _ _) 1
    rcases j with j | (j | j)
    · exact mul_nonneg (Nat.cast_nonneg _) hε
    · have h1:=ihl hl j hf hg
      have h2:=hf a (hleft j)
      have h3:=mul_le_mul_of_nonneg_right hL hε
      change f a+pathBudget f g l j≤_
      linarith
    · have h1:=ihr hr j hf hg
      have h2:=hg a (hright j)
      have h3:=mul_le_mul_of_nonneg_right hR hε
      change g a+pathBudget f g r j≤_
      linarith

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree FiniteEntropy
open scoped Classical BigOperators
variable {I : Type*} [Preorder I]

lemma directed_target_budget (tree : BinaryTree I) (hord : Ordered tree)
    (gA gB : I → ℝ) (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (j : Address tree)
    (hA : ∀ i,label tree j ≤ i → gA i ≤ ε) (hB : ∀ i,i ≤ label tree j → gB i ≤ ε) :
    10*pathBudget (fun i=>C*gA i) (fun _=>0) tree j+
      10*pathBudget (fun _=>0) (fun i=>C*gB i) tree j+
      C*gA (label tree j)+C*gB (label tree j) ≤ (20*tree.height+2)*C*ε := by
  have hh:=mul_nonneg hC hε
  have h1:=ordered_pathBudget_bound tree hord j (fun i=>C*gA i) (fun _=>0) (C*ε) hh
    (fun i hi=>mul_le_mul_of_nonneg_left (hA i hi) hC) (fun _ _=>hh)
  have h2:=ordered_pathBudget_bound tree hord j (fun _=>0) (fun i=>C*gB i) (C*ε) hh
    (fun _ _=>hh) (fun i hi=>mul_le_mul_of_nonneg_left (hB i hi) hC)
  have h3:=mul_le_mul_of_nonneg_left (hA _ le_rfl) hC
  have h4:=mul_le_mul_of_nonneg_left (hB _ le_rfl) hC
  linarith
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OriginalMarginalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
lemma originalLevelLaw_first_mean (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (f : A i → ℝ) :
    (∑ z, originalLevelLaw μ ν z*f (z.1 i)) = ∑ a, μ i a*f a := by
  rw [originalLevelLaw, sum_adaptive]
  simp only [← Finset.sum_mul, (piLaw ν).sum_one, one_mul]
  exact piLaw_eval_expectation μ i f

lemma originalLevelLaw_second_mean (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (j : J) (f : B j → ℝ) :
    (∑ z, originalLevelLaw μ ν z*f (z.2 j)) = ∑ b, ν j b*f b := by
  rw [originalLevelLaw, sum_adaptive]
  simp only [piLaw_eval_expectation ν j, ← Finset.sum_mul, (piLaw μ).sum_one, one_mul]

variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma relationMass_singleton_right (R : X → Y → Prop) (f : X → ℝ) (b : Y) :
    relationMass R f (uniformWeight {b}) = ∑ a∈Finset.univ.filter (fun a => R a b), f a := by
  rw [relationMass_by_target]
  simp [uniformWeight]

lemma relationMass_weighted_singleton (R : X → Y → Prop) (f : X → ℝ) (g : Y → ℝ) :
    (∑ b, g b*relationMass R f (uniformWeight {b})) = relationMass R f g := by
  simp_rw [relationMass_singleton_right R f]
  rw [relationMass_by_target R f g]

lemma relationMass_mixture_right {ι : Type*} [Fintype ι] (R : X → Y → Prop) (μ : Law ι)
    (f : X → ℝ) (g : ι → Y → ℝ) :
    (∑ i, μ i * relationMass R f (g i)) = relationMass R f (fun b => ∑ i, μ i*g i b) := by
  simp_rw [← relationMass_swap R f]
  exact relationMass_mixture_left (fun y x => R x y) μ g f

lemma originalLevelLaw_right_domination (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (j : J) (R : X → Y → Prop) (S : B j → Finset Y) (g : X → ℝ) (q : Y → ℝ)
    (L : ℝ) (hg : ∀ a, 0≤g a)
    (hν : ∀ b, (∑ t, ν j t*uniformWeight (S t) b) ≤ L*q b) :
    (∑ z, originalLevelLaw μ ν z*relationMass R g (uniformWeight (S (z.2 j)))) ≤
      L*relationMass R g q := by
  rw [originalLevelLaw_second_mean μ ν j (fun t => relationMass R g (uniformWeight (S t))), relationMass_mixture_right]
  simp only [relationMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have h := mul_le_mul_of_nonneg_left (hν z.2) (hg z.1)
  rw [← Finset.mul_sum]
  nlinarith only [h]

lemma originalLevelLaw_left_domination (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (R : X → Y → Prop) (S : A i → Finset X) (p : X → ℝ) (g : Y → ℝ)
    (L : ℝ) (hg : ∀ b, 0≤g b)
    (hμ : ∀ a, (∑ t, μ i t*uniformWeight (S t) a) ≤ L*p a) :
    (∑ z, originalLevelLaw μ ν z*relationMass R (uniformWeight (S (z.1 i))) g) ≤
      L*relationMass R p g := by
  rw [originalLevelLaw_first_mean μ ν i (fun t => relationMass R (uniformWeight (S t)) g), relationMass_mixture_left]
  simp only [relationMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have h := mul_le_mul_of_nonneg_right (hμ z.1) (hg z.2)
  nlinarith only [h]
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_TargetAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
variable {I Z X : Type*} [Fintype Z] [Fintype X]
lemma mean_pathBudget_twice (μ : Z → ℝ) (g : X → ℝ)
    (ρL ρR : Z → X → I → ℝ) (tree : BinaryTree I) (j : Address tree) :
    (∑ z, μ z * (∑ a, g a * pathBudget (ρL z a) (ρR z a) tree j)) =
      pathBudget (fun i => ∑ z, μ z * (∑ a, g a * ρL z a i))
        (fun i => ∑ z, μ z * (∑ a, g a * ρR z a i)) tree j := by
  simp_rw [mean_pathBudget g]
  exact mean_pathBudget μ _ _ tree j
end SharpRamseyFive.TreeCodec
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
  {X Y : Type*} [Fintype X] [Fintype Y]

lemma original_target_mean_point (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (j : J) (R : X → Y → Prop) (S : B j → Finset Y) (g : X → ℝ) (q : Y → ℝ)
    (C L : ℝ) (hC : 0≤C) (hg : ∀ a, 0≤g a)
    (hν : ∀ b, (∑ t, ν j t*uniformWeight (S t) b) ≤ L*q b) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*(C *
      relationMass (fun b a => R a b) (uniformWeight (S (z.2 j))) (uniformWeight {a})))) ≤
        C*L*relationMass R g q := by
  have he (z : (∀ i, A i) × (∀ j, B j)) :
      (∑ a, g a*(C*relationMass (fun b a => R a b) (uniformWeight (S (z.2 j))) (uniformWeight {a}))) =
        C*relationMass R g (uniformWeight (S (z.2 j))) := by
    rw [← relationMass_swap R g, ← relationMass_weighted_singleton]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [he]
  calc
    _ = C*(∑ z, originalLevelLaw μ ν z*relationMass R g (uniformWeight (S (z.2 j)))) := by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    _ ≤ C*(L*relationMass R g q) :=
      mul_le_mul_of_nonneg_left (originalLevelLaw_right_domination μ ν j R S g q L hg hν) hC
    _ = _ := by ring

lemma original_target_mean_dual (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (R : X → Y → Prop) (S : A i → Finset X) (p : X → ℝ) (g : Y → ℝ)
    (C L : ℝ) (hC : 0≤C) (hg : ∀ b, 0≤g b)
    (hμ : ∀ a, (∑ t, μ i t*uniformWeight (S t) a) ≤ L*p a) :
    (∑ z, originalLevelLaw μ ν z * (∑ b, g b*(C *
      relationMass R (uniformWeight (S (z.1 i))) (uniformWeight {b})))) ≤
        C*L*relationMass R p g := by
  have he (z : (∀ i, A i) × (∀ j, B j)) :
      (∑ b, g b*(C*relationMass R (uniformWeight (S (z.1 i))) (uniformWeight {b}))) =
        C*relationMass R (uniformWeight (S (z.1 i))) g := by
    rw [← relationMass_weighted_singleton R _ g]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [he]
  calc
    _ = C*(∑ z, originalLevelLaw μ ν z*relationMass R (uniformWeight (S (z.1 i))) g) := by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    _ ≤ C*(L*relationMass R p g) :=
      mul_le_mul_of_nonneg_left (originalLevelLaw_left_domination μ ν i R S p g L hg hμ) hC
    _ = _ := by ring
end SharpRamseyFive.FiniteEntropy

end

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
variable {I Z A : Type*} [Fintype Z] [Fintype A]
lemma mean_two_pathBudget_scaled (μ : Z → ℝ) (g : A → ℝ)
    (ρL ρR : Z → A → I → ℝ) (c : ℝ) (tree : BinaryTree I) (j : Address tree) :
    (∑ z, μ z*(∑ a, g a*(c*pathBudget (ρL z a) (ρR z a) tree j))) =
      c*pathBudget (fun i => ∑ z, μ z*(∑ a, g a*ρL z a i))
        (fun i => ∑ z, μ z*(∑ a, g a*ρR z a i)) tree j := by
  rw [← mean_pathBudget_twice]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  ring
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TargetCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
noncomputable section
variable {I : Type}

local instance (priority := high) actualTargetCapsPropDecidable_r0311ea_1 (P : Prop) : Decidable P := Classical.propDecidable P
theorem oriented_original_point_cap
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (x : (ℙ K V)) (tree : BinaryTree I) (j : Address tree) :
    eventMass (orientedPivotTreeLaw f r tree) (Finset.univ.filter (fun ω =>
      Excludes x ((orientedPivotCapsAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω
        (Finset.univ,Finset.univ) j).map Prod.snd))) ≤
      (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass (fun b a => Incident a b) (uniformWeight (B₀ (label tree j))) (uniformWeight {x}) := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let p := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let enc : ∀ i C t, Option (M i C t) := fun i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t
  let out : ∀ i C t, M i C t → _ := fun _ C t =>
    orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t
  let rate := fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
    relationMass (fun b a => Incident a b) (uniformWeight (B₀ i)) (uniformWeight {x})
  have hn : ∀ i, 0 ≤ rate i := fun i => mul_nonneg (by positivity)
    (relationMass_nonneg _ _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _))
  have hh := observe_event_bound Ω M (fun _ => orientedPivotLeft f r) (fun _ => orientedPivotRight f r)
    p enc out (fun o => Excludes x (o.map Prod.snd)) (by simp [Excludes]) rate hn
    (fun i C => by
      have h := (orientedGuardedNode_original (f C) (r C) σ hσ hq hd hq3 (A₀ i) C.1 (B₀ i) C.2
        (hA₀ i) (hB₀ i) c δ τ P hc hc9 hδ hτ).2 x
      dsimp only [rate]
      rw [relationMass_singleton_right, sum_uniformWeight]
      have he : (Finset.univ.filter (fun y => Incident x y)) ∩ B₀ i =
          (B₀ i).filter (fun y => Incident x y) := by ext y; simp [and_comm]
      rw [he]
      exact h) tree (Finset.univ,Finset.univ) j
  rw [eventMass_map_filter] at hh
  exact hh

theorem oriented_original_dual_cap
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (x : (ℙ K (Dual K V))) (tree : BinaryTree I) (j : Address tree) :
    eventMass (orientedPivotTreeLaw f r tree) (Finset.univ.filter (fun ω =>
      Excludes x ((orientedPivotCapsAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω
        (Finset.univ,Finset.univ) j).map Prod.fst))) ≤
      (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass Incident (uniformWeight (A₀ (label tree j))) (uniformWeight {x}) := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let p := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let enc : ∀ i C t, Option (M i C t) := fun i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t
  let out : ∀ i C t, M i C t → _ := fun _ C t =>
    orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t
  let rate := fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
    relationMass Incident (uniformWeight (A₀ i)) (uniformWeight {x})
  have hn : ∀ i, 0 ≤ rate i := fun i => mul_nonneg (by positivity)
    (relationMass_nonneg _ _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _))
  have hh := observe_event_bound Ω M (fun _ => orientedPivotLeft f r) (fun _ => orientedPivotRight f r)
    p enc out (fun o => Excludes x (o.map Prod.fst)) (by simp [Excludes]) rate hn
    (fun i C => by
      have h := (orientedGuardedNode_original (f C) (r C) σ hσ hq hd hq3 (A₀ i) C.1 (B₀ i) C.2
        (hA₀ i) (hB₀ i) c δ τ P hc hc9 hδ hτ).1 x
      dsimp only [rate]
      rw [relationMass_singleton_right, sum_uniformWeight]
      have he : (Finset.univ.filter (fun y => Incident y x)) ∩ A₀ i =
          (A₀ i).filter (fun y => Incident y x) := by ext y; simp [and_comm]
      rw [he]
      exact h) tree (Finset.univ,Finset.univ) j
  rw [eventMass_map_filter] at hh
  exact hh

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TargetTrims
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open scoped Classical
variable {α : Type*}
lemma singleton_trim_iff (a : α) (U : Finset α) :
    (({a} ∩ U).card:ℝ) < (9/10:ℝ)*({a}:Finset α).card ↔ a∉U := by
  by_cases h : a∈U
  · simp [Finset.singleton_inter_of_mem h, h]
    norm_num
  · simp [Finset.singleton_inter_of_notMem h, h]
end SharpRamseyFive.ReverseCap
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTargetTrimsPropDecidable_r0311ea_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_original_point_target
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (a : ℙ K V) (tree : BinaryTree I) (j : Address tree) :
    eventMass (orientedPivotTreeLaw f r tree) (Finset.univ.filter (fun ω => ∃ C,
      orientedPivotContextAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω
        (Finset.univ,Finset.univ) j = some C ∧ a∉C.1)) ≤
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass (fun b a => Incident a b) (uniformWeight (B₀ i)) (uniformWeight {a}))
        (fun _ => 0) tree j := by
  have h := oriented_original_point_trim f r σ hσ hq hd hq3 A₀ B₀ hA₀ hB₀ c δ τ P hc hc9 hδ hτ {a} tree j
  simpa only [singleton_trim_iff] using h

theorem oriented_original_dual_target
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (b : ℙ K (Dual K V)) (tree : BinaryTree I) (j : Address tree) :
    eventMass (orientedPivotTreeLaw f r tree) (Finset.univ.filter (fun ω => ∃ C,
      orientedPivotContextAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω
        (Finset.univ,Finset.univ) j = some C ∧ b∉C.2)) ≤
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass Incident (uniformWeight (A₀ i)) (uniformWeight {b})) tree j := by
  have h := oriented_original_dual_trim f r σ hσ hq hd hq3 A₀ B₀ hA₀ hB₀ c δ τ P hc hc9 hδ hτ {b} tree j
  simpa only [singleton_trim_iff] using h
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LevelTargetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) levelTargetBoundsPropDecidable_r0311ea_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_level_point_target_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K (Dual K V))) (g : ℙ K V → ℝ) (hg : ∀ a, 0≤g a)
    (L : ℝ) (hflat : ∀ i a, (∑ s, ν i s*uniformWeight (Y i s) a) ≤ L*p i a)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧ a∉C.1)))) ≤
      10*pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ)))*L*relationMass Incident (g) (p i)) (fun _ => 0) tree j := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) a i => C₀ * relationMass
    (fun b a => Incident a b) (uniformWeight (Y i (z.2 i))) (uniformWeight {a})
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) (a : ℙ K V) :=
    oriented_original_point_target f r σ hσ hq hd hq3
      (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
      c δ τ P hc hc9 hδ hτ a tree j
  have hm (i : I) : (∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) ≤
      C₀*L*relationMass Incident g (p i) :=
    original_target_mean_point μ ν i Incident (Y i) g (p i) C₀ L hC₀ hg (hflat i)
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z*(∑ a, g a*(10*pathBudget (ρ z a) (fun _ => 0) tree j)) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint z a) (hg a))
        ((originalLevelLaw μ ν).nonneg z)
    _ = 10*pathBudget (fun i => ∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) (fun _ => 0) tree j := by
      simpa only [mul_zero, Finset.sum_const_zero] using
        mean_two_pathBudget_scaled (originalLevelLaw μ ν) g ρ (fun _ _ _ => 0) 10 tree j
    _ ≤ _ := mul_le_mul_of_nonneg_left (pathBudget_mono _ _ _ _
      hm (fun _ => le_refl 0) tree j) (by norm_num)

theorem oriented_level_point_target_cap
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K (Dual K V))) (g : ℙ K V → ℝ) (hg : ∀ a, 0≤g a)
    (L : ℝ) (hflat : ∀ i a, (∑ s, ν i s*uniformWeight (Y i s) a) ≤ L*p i a)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => Excludes a ((orientedPivotCapsAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j).map Prod.snd))))) ≤
      (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ)))*L*relationMass Incident (g) (p i)) (label tree j) := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) a i => C₀ * relationMass
    (fun b a => Incident a b) (uniformWeight (Y i (z.2 i))) (uniformWeight {a})
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) (a : ℙ K V) :=
    oriented_original_point_cap f r σ hσ hq hd hq3
      (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
      c δ τ P hc hc9 hδ hτ a tree j
  have hm (i : I) : (∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) ≤
      C₀*L*relationMass Incident g (p i) :=
    original_target_mean_point μ ν i Incident (Y i) g (p i) C₀ L hC₀ hg (hflat i)
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a (label tree j)) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint z a) (hg a))
        ((originalLevelLaw μ ν).nonneg z)
    _ ≤ _ := hm (label tree j)

theorem oriented_level_dual_target_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (g : ℙ K (Dual K V) → ℝ) (hg : ∀ a, 0≤g a)
    (L : ℝ) (hflat : ∀ i a, (∑ s, μ i s*uniformWeight (X i s) a) ≤ L*p i a)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧ a∉C.2)))) ≤
      10*pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ)))*L*relationMass Incident (p i) (g)) tree j := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) a i => C₀ * relationMass
    Incident (uniformWeight (X i (z.1 i))) (uniformWeight {a})
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) (a : ℙ K (Dual K V)) :=
    oriented_original_dual_target f r σ hσ hq hd hq3
      (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
      c δ τ P hc hc9 hδ hτ a tree j
  have hm (i : I) : (∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) ≤
      C₀*L*relationMass Incident (p i) g :=
    original_target_mean_dual μ ν i Incident (X i) (p i) g C₀ L hC₀ hg (hflat i)
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z*(∑ a, g a*(10*pathBudget (fun _ => 0) (ρ z a) tree j)) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint z a) (hg a))
        ((originalLevelLaw μ ν).nonneg z)
    _ = 10*pathBudget (fun _ => 0) (fun i => ∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) tree j := by
      simpa only [mul_zero, Finset.sum_const_zero] using
        mean_two_pathBudget_scaled (originalLevelLaw μ ν) g (fun _ _ _ => 0) ρ 10 tree j
    _ ≤ _ := mul_le_mul_of_nonneg_left (pathBudget_mono _ _ _ _
      (fun _ => le_refl 0) hm tree j) (by norm_num)

theorem oriented_level_dual_target_cap
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (g : ℙ K (Dual K V) → ℝ) (hg : ∀ a, 0≤g a)
    (L : ℝ) (hflat : ∀ i a, (∑ s, μ i s*uniformWeight (X i s) a) ≤ L*p i a)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => Excludes a ((orientedPivotCapsAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j).map Prod.fst))))) ≤
      (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ)))*L*relationMass Incident (p i) (g)) (label tree j) := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) a i => C₀ * relationMass
    Incident (uniformWeight (X i (z.1 i))) (uniformWeight {a})
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) (a : ℙ K (Dual K V)) :=
    oriented_original_dual_cap f r σ hσ hq hd hq3
      (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
      c δ τ P hc hc9 hδ hτ a tree j
  have hm (i : I) : (∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) ≤
      C₀*L*relationMass Incident (p i) g :=
    original_target_mean_dual μ ν i Incident (X i) (p i) g C₀ L hC₀ hg (hflat i)
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a (label tree j)) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint z a) (hg a))
        ((originalLevelLaw μ ν).nonneg z)
    _ ≤ _ := hm (label tree j)
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeObservationRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z s
variable {I : Type u} {C : Type v}
  (Ω : I → C → Type w)
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  (enc : ∀ i c t, Option (M i c t))
  {D : Type s} (out : ∀ i c t, M i c t → D)

lemma observe_none_iff_success (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    observe Ω M left right enc out b ω c j = none ↔ successAt Ω M left right enc b ω c j = none := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · simp only [successAt, observe, probe, Option.map_eq_none_iff]
    · cases he : enc i c (ω.1 c) with
      | none => simp only [successAt, observe, probe, he, Option.map_none, Option.elim_none]
      | some m =>
        simpa only [successAt, observe, probe, he, Option.map_some, Option.elim_some] using
          ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp only [successAt, observe, probe, he, Option.map_none, Option.elim_none]
      | some m =>
        simpa only [successAt, observe, probe, he, Option.map_some, Option.elim_some] using
          ihr ω.2.2 (right i c (ω.1 c) m) j

lemma context_none_observe (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    contextAt Ω M left right enc b ω c j = none → observe Ω M left right enc out b ω c j = none := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · simp only [contextAt, probe, Option.some_ne_none, false_implies]
    · cases he : enc i c (ω.1 c) with
      | none => simp only [contextAt, observe, probe, he, Option.map_none, Option.elim_none, implies_true]
      | some m =>
        simpa only [contextAt, observe, probe, he, Option.map_some, Option.elim_some] using
          ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp only [contextAt, observe, probe, he, Option.map_none, Option.elim_none, implies_true]
      | some m =>
        simpa only [contextAt, observe, probe, he, Option.map_some, Option.elim_some] using
          ihr ω.2.2 (right i c (ω.1 c) m) j

lemma observe_context_coherent (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    observe Ω M left right enc out b ω c j ≠ none → contextAt Ω M left right enc b ω c j ≠ none :=
  mt (context_none_observe Ω M left right enc out b ω c j)
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TargetCoherence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma oriented_caps_none_iff
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree)
    (C : PivotContext K V) (j : Address tree) :
    orientedPivotCapsAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j = none ↔
      orientedPivotSuccessAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j = none :=
  observe_none_iff_success (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t)
    (fun _ C t => orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t)
    tree ω C j

omit [Fintype I] [DecidableEq I] in
lemma oriented_caps_context_coherent
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree)
    (C : PivotContext K V) (j : Address tree) :
    orientedPivotCapsAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j ≠ none →
      orientedPivotContextAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j ≠ none :=
  observe_context_coherent (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t)
    (fun _ C t => orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t)
    tree ω C j
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TargetRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTargetRetentionPropDecidable_r0311ea_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I Ω : Type} [Fintype I] [DecidableEq I] [Fintype Ω]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_actual_target_loss
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ)
    (hflatA : ∀ i a, (∑ s, μ i s*uniformWeight (X i s) a) ≤ L*p i a)
    (hflatB : ∀ i b, (∑ s, ν i s*uniformWeight (Y i s) b) ≤ L*q i b)
    (γ : Law Ω) (a : Ω → ℙ K V) (b : Ω → ℙ K (Dual K V))
    (goodA : ℙ K V → Prop) (goodB : ℙ K (Dual K V) → Prop)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    let ctx := fun z : ((∀ i, A i) × (∀ i, B i)) × OrientedPivotTreeTape f r tree =>
      orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1.1 i)) (fun i => Y i (z.1.2 i))
        (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree z.2 (Finset.univ,Finset.univ) j
    let caps := fun z : ((∀ i, A i) × (∀ i, B i)) × OrientedPivotTreeTape f r tree =>
      orientedPivotCapsAt f r σ hσ hq hd.le (fun i => X i (z.1.1 i)) (fun i => Y i (z.1.2 i))
        (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree z.2 (Finset.univ,Finset.univ) j
    let gA := fun x => if goodA x then map γ a x else 0
    let gB := fun y => if goodB y then map γ b y else 0
    let C₀ := 50*(Nat.card K:ℝ)/(9*(c*δ))
    eventMass (adaptiveLaw γ (fun _ => adaptiveLaw (originalLevelLaw μ ν)
      (fun _ => orientedPivotTreeLaw f r tree))) (Finset.univ.filter
        (fun z => ¬TargetCovered (ctx z.2) (caps z.2) (a z.1) (b z.1))) ≤
      eventMass γ (Finset.univ.filter (fun x => ¬goodA (a x))) +
      eventMass γ (Finset.univ.filter (fun x => ¬goodB (b x))) +
      (∑ z, originalLevelLaw μ ν z*eventMass (orientedPivotTreeLaw f r tree)
        (Finset.univ.filter (fun ω => orientedPivotSuccessAt f r σ hσ hq hd.le
          (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
          c δ τ P hδ tree ω (Finset.univ,Finset.univ) j=none))) +
      10*pathBudget (fun i => C₀*L*relationMass Incident gA (q i)) (fun _ => 0) tree j +
      10*pathBudget (fun _ => 0) (fun i => C₀*L*relationMass Incident (p i) gB) tree j +
      C₀*L*relationMass Incident gA (q (label tree j)) +
      C₀*L*relationMass Incident (p (label tree j)) gB := by
  dsimp only
  let ctx := fun z : ((∀ i, A i) × (∀ i, B i)) × OrientedPivotTreeTape f r tree =>
    orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1.1 i)) (fun i => Y i (z.1.2 i))
      (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree z.2 (Finset.univ,Finset.univ) j
  let caps := fun z : ((∀ i, A i) × (∀ i, B i)) × OrientedPivotTreeTape f r tree =>
    orientedPivotCapsAt f r σ hσ hq hd.le (fun i => X i (z.1.1 i)) (fun i => Y i (z.1.2 i))
      (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree z.2 (Finset.univ,Finset.univ) j
  let gA := fun x => if goodA x then map γ a x else 0
  let gB := fun y => if goodB y then map γ b y else 0
  have hgA : ∀ x, 0≤gA x := by intro x; dsimp [gA]; split_ifs; exact (map γ a).nonneg x; rfl
  have hgB : ∀ y, 0≤gB y := by intro y; dsimp [gB]; split_ifs; exact (map γ b).nonneg y; rfl
  have hcoh : ∀ z, caps z≠none → ctx z≠none := by
    intro z
    exact oriented_caps_context_coherent f r σ hσ hq hd.le _ _ _ _ c δ τ P hδ tree z.2 _ j
  have h := independent_target_loss γ
    (adaptiveLaw (originalLevelLaw μ ν) (fun _ => orientedPivotTreeLaw f r tree))
    a b goodA goodB ctx caps hcoh
  have hn : eventMass (adaptiveLaw (originalLevelLaw μ ν) (fun _ => orientedPivotTreeLaw f r tree))
      (Finset.univ.filter (fun z => caps z=none)) =
      ∑ z, originalLevelLaw μ ν z*eventMass (orientedPivotTreeLaw f r tree)
        (Finset.univ.filter (fun ω => orientedPivotSuccessAt f r σ hσ hq hd.le
          (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
          c δ τ P hδ tree ω (Finset.univ,Finset.univ) j=none)) := by
    rw [independent_target_event_general]
    apply Finset.sum_congr rfl
    intro z _
    congr 2
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact oriented_caps_none_iff f r σ hσ hq hd.le _ _ _ _ c δ τ P hδ tree ω _ j
  rw [hn] at h
  dsimp only [ctx,caps] at h
  rw [independent_weighted_event, independent_weighted_event,
    independent_weighted_event, independent_weighted_event] at h
  have h1 := oriented_level_point_target_trim f r σ hσ hq hd hq3 μ ν X Y hX hY q gA hgA L hflatB c δ τ P hc hc9 hδ hτ tree j
  have h2 := oriented_level_dual_target_trim f r σ hσ hq hd hq3 μ ν X Y hX hY p gB hgB L hflatA c δ τ P hc hc9 hδ hτ tree j
  have h3 := oriented_level_point_target_cap f r σ hσ hq hd hq3 μ ν X Y hX hY q gA hgA L hflatB c δ τ P hc hc9 hδ hτ tree j
  have h4 := oriented_level_dual_target_cap f r σ hσ hq hd hq3 μ ν X Y hX hY p gB hgB L hflatA c δ τ P hc hc9 hδ hτ tree j
  exact h.trans (add_le_add (add_le_add (add_le_add (add_le_add_right h1 _) h2) h3) h4)
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrderedTargetRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section

local instance (priority := high) orderedTargetPropDecidable_r0311ea_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V I Ω : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Fintype I] [DecidableEq I] [Fintype Ω]
  {A B : I → Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]

theorem eventually_ordered_target_retention_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
      (A B : I → Type) [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
      (μ : ∀ i,Law (A i)) (ν : ∀ i,Law (B i))
      (X : ∀ i,A i → Finset (ℙ K V)) (Y : ∀ i,B i → Finset (ℙ K (Dual K V)))
      (hX : ∀ i a,(X i a).Nonempty) (hY : ∀ i b,(Y i b).Nonempty)
      (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
      (F ε : ℝ) (hF : 0 ≤ F) (hε : 0 ≤ ε)
      (hμ : ∀ i a,(∑ s,μ i s*uniformWeight (X i s) a) ≤ F*p i a)
      (hν : ∀ i b,(∑ t,ν i t*uniformWeight (Y i t) b) ≤ F*q i b)
      (hsparse : ∀ i j,i ≤ j → relationMass Incident (p i) (q j) ≤ ε)
      (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0 ≤ b → b ≤ Cb*D*σ^(6*beta η) →
      (∀ i a d,(Nat.card K:ℝ)^5*Real.exp (-b) ≤ ((X i a).card:ℝ)*(Y i d).card) →
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree),
      ∀ (Ω : Type) [Fintype Ω] (γ : Law Ω) (a : Ω → ℙ K V) (b₀ : Ω → ℙ K (Dual K V))
        (goodA : ℙ K V → Prop) (goodB : ℙ K (Dual K V) → Prop) (ε₀ : ℝ),0 ≤ ε₀ →
        (∀ i,label tree j ≤ i → relationMass Incident (fun x=>if goodA x then map γ a x else 0) (q i) ≤ ε₀) →
        (∀ i,i ≤ label tree j → relationMass Incident (p i) (fun y=>if goodB y then map γ b₀ y else 0) ≤ ε₀) →
      orientedTargetFailure f r σ hσ hq hd.le μ ν X Y hX hY γ a b₀
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree j ≤
      eventMass γ (Finset.univ.filter fun x=>¬goodA (a x))+
      eventMass γ (Finset.univ.filter fun x=>¬goodB (b₀ x))+
      tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2*ε+
        ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*ε+5*Real.exp (-(Nat.card K:ℝ)))+
      (20*tree.height+2)*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F*ε₀ := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-1000*beta η) ≤ ((9/100000:ℝ)*(9/10)^2)/1000 := by
    have hp : 0<1000*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<((9/100000:ℝ)*(9/10)^2)/1000)).mono
        (fun σ h=>by simpa only [neg_mul] using h.le)
  filter_upwards [eventually_ordered_tree_missing hη hη' Cb hCb,ht] with σ hh ht
  intro D b R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 I _ _ _ A B _ _ μ ν X Y hX hY p q F ε hF hε hμ hν hsparse hσ hq hcard hr hL hb hbhi hprod
  dsimp only
  intro tree hord j Ω _ γ a b₀ goodA goodB ε₀ hε₀ hA hB
  let f:=fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r:=fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
    (P η σ D R) (σ^(-800*beta η)) R L₀
  have hn:=hh D b R L₀ q₀ K V hd hq3 I A B μ ν X Y hX hY p q F ε hF hε hμ hν hsparse
    hσ hq hcard hr hL hb hbhi hprod tree hord j
  have hτ : 1000*σ^(-1000*beta η) ≤ (9/100000:ℝ)*(9/10)^2 := by linarith only [ht]
  have htarg:=oriented_actual_target_loss f r σ hσ hq hd hq3 μ ν X Y hX hY p q F hμ hν
    γ a b₀ goodA goodB (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R)
    (by norm_num) (by norm_num) (by norm_num) hτ tree j
  have hbudget:=directed_target_budget tree hord
    (fun i=>relationMass Incident (fun x=>if goodA x then map γ a x else 0) (q i))
    (fun i=>relationMass Incident (p i) (fun y=>if goodB y then map γ b₀ y else 0))
    ε₀ ((50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F) hε₀ (by positivity) j hA hB
  dsimp only at htarg
  change orientedTargetFailure f r σ hσ hq hd.le μ ν X Y hX hY γ a b₀ _ _ _ _ _ tree j ≤ _ at htarg
  change orientedTargetFailure f r σ hσ hq hd.le μ ν X Y hX hY γ a b₀ _ _ _ _ _ tree j ≤ _
  calc
    _  ≤  _ := htarg
    _  ≤  _ := by
      dsimp only [f,r] at *
      nlinarith only [hn,hbudget]
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention_oai := @OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention_oai
