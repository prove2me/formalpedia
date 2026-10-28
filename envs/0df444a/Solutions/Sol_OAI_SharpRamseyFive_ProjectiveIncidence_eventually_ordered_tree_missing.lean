-- Prove2me | solution 1 for OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:31:33.506581+00:00
-- url     : https://prove2.me/submissions/9667a5ab-01f4-43b2-a211-548eaa4ce071

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_eventually_oriented_ready_encoded_failure
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

lemma eventMass_filter_union (p : Law A) (P Q : A→Prop) :
    eventMass p (Finset.univ.filter fun a=>P a∨Q a) ≤
      eventMass p (Finset.univ.filter P)+eventMass p (Finset.univ.filter Q) := by
  simp only [eventMass,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq,p.nonneg a]

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
variable {I : Type u}

lemma pathSum_zero (b : BinaryTree I) (j : Address b) : pathSum b (fun _ => 0) j = 0 := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · rfl
    · simp only [pathSum, ihl, add_zero]
    · simp only [pathSum, ihr, add_zero]

lemma pathSum_mono (b : BinaryTree I) (f g : Address b → ℝ) (h : ∀ k, f k ≤ g k)
    (j : Address b) : pathSum b f j ≤ pathSum b g j := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · exact h _
    · exact add_le_add (h _) (ihl _ _ (fun k => h _) j)
    · exact add_le_add (h _) (ihr _ _ (fun k => h _) j)

lemma pathSum_const_le_height (b : BinaryTree I) (j : Address b) (a : ℝ) (ha : 0 ≤ a) :
    pathSum b (fun _ => a) j ≤ b.height * a := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    have hL : (l.height:ℝ)+1 ≤ (BinaryTree.node i l r).height := by
      simp only [BinaryTree.height, Nat.cast_add, Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 1
    have hR : (r.height:ℝ)+1 ≤ (BinaryTree.node i l r).height := by
      simp only [BinaryTree.height, Nat.cast_add, Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right (le_max_right _ _) 1
    rcases j with j | (j | j)
    · have hz : (0:ℝ) ≤ l.height := Nat.cast_nonneg _
      have h := mul_le_mul_of_nonneg_right hL ha
      simpa only [pathSum] using (show a ≤ (BinaryTree.node i l r).height*a by nlinarith only [h, hz, ha])
    · have h := mul_le_mul_of_nonneg_right hL ha
      simpa only [pathSum] using (show a+pathSum l (fun _ => a) j ≤ (BinaryTree.node i l r).height*a by linarith only [h, ihl j])
    · have h := mul_le_mul_of_nonneg_right hR ha
      simpa only [pathSum] using (show a+pathSum r (fun _ => a) j ≤ (BinaryTree.node i l r).height*a by linarith only [h, ihr j])

lemma mean_pathSum {W : Type*} [Fintype W] (p : W → ℝ)
    (b : BinaryTree I) (f : W → Address b → ℝ) (j : Address b) :
    (∑ ω, p ω * pathSum b (f ω) j) = pathSum b (fun k => ∑ ω, p ω * f ω k) j := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · rfl
    · simp only [pathSum, mul_add, Finset.sum_add_distrib, ihl]
    · simp only [pathSum, mul_add, Finset.sum_add_distrib, ihr]

variable {C : Type v} [Fintype C]
  (Ω : I → C → Type w) [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  (enc : ∀ i c t, Option (M i c t))

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
theorem missing_path_eq (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    (if successAt Ω M left right enc b ω c j = none then (1:ℝ) else 0) =
      pathSum b (fun k => if abortAt Ω M left right enc b ω c k = some true then 1 else 0) j := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · cases he : enc i c (ω.1 c) <;>
        simp [successAt, abortAt, observe, probe, pathSum, he]
    · cases he : enc i c (ω.1 c) with
      | none => simp [successAt, abortAt, observe, probe, pathSum, he, pathSum_zero]
      | some m =>
          convert ihl ω.2.1 (left i c (ω.1 c) m) j using 1 <;>
            simp [successAt, abortAt, observe, probe, pathSum, he]
          all_goals rfl
    · cases he : enc i c (ω.1 c) with
      | none => simp [successAt, abortAt, observe, probe, pathSum, he, pathSum_zero]
      | some m =>
          convert ihr ω.2.2 (right i c (ω.1 c) m) j using 1 <;>
            simp [successAt, abortAt, observe, probe, pathSum, he]
          all_goals rfl

lemma missing_mass_path (b : BinaryTree I) (p : Law (Tape Ω b)) (c : C) (j : Address b) :
    eventMass p (Finset.univ.filter (fun ω => successAt Ω M left right enc b ω c j = none)) =
      pathSum b (fun k => eventMass p (Finset.univ.filter
        (fun ω => abortAt Ω M left right enc b ω c k = some true))) j := by
  have h := mean_pathSum p b
    (fun ω k => if abortAt Ω M left right enc b ω c k = some true then (1:ℝ) else 0) j
  simp_rw [← missing_path_eq Ω M left right enc b _ c j] at h
  simpa only [eventMass, Finset.sum_filter, mul_ite, mul_one, mul_zero] using h

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

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α : Type*} [Fintype α]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]

lemma originalLevelLaw_cross_mean (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (j : J) (f : A i → B j → ℝ) :
    (∑ z, originalLevelLaw μ ν z * f (z.1 i) (z.2 j)) =
      ∑ a, ∑ b, μ i a * ν j b * f a b := by
  rw [originalLevelLaw, sum_adaptive]
  simp_rw [piLaw_eval_expectation ν j]
  rw [piLaw_eval_expectation μ i (fun a => ∑ b, ν j b * f a b)]
  simp only [Finset.mul_sum, mul_assoc]

lemma originalLevelLaw_cross_domination {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (j : J) (R : X → Y → Prop) (s : A i → Finset X) (t : B j → Finset Y)
    (p : Law X) (q : Law Y) (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ x, (∑ a, μ i a * uniformWeight (s a) x) ≤ L * p x)
    (ht : ∀ y, (∑ b, ν j b * uniformWeight (t b) y) ≤ L * q y) :
    (∑ z, originalLevelLaw μ ν z *
      relationMass R (uniformWeight (s (z.1 i))) (uniformWeight (t (z.2 j)))) ≤
        L^2 * relationMass R p q := by
  rw [originalLevelLaw_cross_mean μ ν i j (fun a b => relationMass R (uniformWeight (s a)) (uniformWeight (t b)))]
  exact independent_support_domination R p q (μ i) (ν j) s t L hL hs ht

end SharpRamseyFive.FiniteEntropy
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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LevelDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma scaled_uniform_density_iff (R : α → β → Prop) (X : Finset α) (Y : Finset β)
    (hX : X.Nonempty) (hY : Y.Nonempty) (Q τ : ℝ) :
    Q * (((X×ˢY).filter (fun z => R z.1 z.2)).card : ℝ) ≤ τ * X.card * Y.card ↔
      Q * relationMass R (uniformWeight X) (uniformWeight Y) ≤ τ := by
  have hx : (0:ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hy : (0:ℝ) < Y.card := by exact_mod_cast hY.card_pos
  rw [relationMass_uniform, ← mul_div_assoc, div_le_iff₀ (mul_pos hx hy)]
  rw [mul_assoc]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]

theorem original_level_density_rejection
    (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j)) (i : I) (j : J)
    (R : α → β → Prop) (X : A i → Finset α) (Y : B j → Finset β)
    (p : Law α) (q : Law β) (L : ℝ) (hL : 0≤L)
    (hs : ∀ x, (∑ a, μ i a * uniformWeight (X a) x) ≤ L*p x)
    (ht : ∀ y, (∑ b, ν j b * uniformWeight (Y b) y) ≤ L*q y)
    (Q τ : ℝ) (hQ : 0≤Q) (hτ : 0<τ) :
    eventMass (originalLevelLaw μ ν) (Finset.univ.filter (fun z =>
      τ < Q*relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j))))) ≤
        (Q/τ)*L^2*relationMass R p q := by
  have hm := event_markov (originalLevelLaw μ ν)
    (fun z => Q*relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j))))
    (fun z => mul_nonneg hQ (relationMass_nonneg R _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _)))
    τ (Finset.univ.filter (fun z =>
      τ < Q*relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j)))))
    (fun z hz => (Finset.mem_filter.mp hz).2.le)
  have he : (∑ z, originalLevelLaw μ ν z *
      (Q*relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j))))) =
      Q*(∑ z, originalLevelLaw μ ν z *
        relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he] at hm
  have hd := originalLevelLaw_cross_domination μ ν i j R X Y p q L hL hs ht
  have hh := hm.trans (mul_le_mul_of_nonneg_left hd hQ)
  calc
    _ ≤ (Q*(L^2*relationMass R p q))/τ := (le_div_iff₀ hτ).mpr (by simpa only [mul_comm τ] using hh)
    _ = _ := by ring
end SharpRamseyFive.FiniteEntropy

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

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_level_point_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ L*p i a)
    (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ L*q i b)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧
        ((X (label tree j) (z.1 (label tree j)) ∩ C.1).card : ℝ) <
          (9/10:ℝ)*(X (label tree j) (z.1 (label tree j))).card))) ≤
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p (label tree j)) (q i)) (fun _ => 0) tree j := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) i => C₀ * relationMass Incident
    (uniformWeight (X (label tree j) (z.1 (label tree j)))) (uniformWeight (Y i (z.2 i)))
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) := oriented_original_point_trim f r σ hσ hq hd hq3
    (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
    c δ τ P hc hc9 hδ hτ (X (label tree j) (z.1 (label tree j))) tree j
  simp_rw [relationMass_swap] at hpoint
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z * (10*pathBudget (ρ z) (fun _ => 0) tree j) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint z) ((originalLevelLaw μ ν).nonneg z)
    _ = 10 * pathBudget (fun i => ∑ z, originalLevelLaw μ ν z * ρ z i) (fun _ => 0) tree j := by
      have he := mean_pathBudget (originalLevelLaw μ ν) ρ (fun _ _ => 0) tree j
      simp only [mul_zero, Finset.sum_const_zero] at he
      rw [← he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pathBudget_mono
      · intro i
        have hs := originalLevelLaw_cross_domination μ ν (label tree j) i Incident
          (X (label tree j)) (Y i) (p (label tree j)) (q i) L hL (hμ _) (hν _)
        calc
          _ = C₀*(∑ z, originalLevelLaw μ ν z * relationMass Incident
              (uniformWeight (X (label tree j) (z.1 (label tree j)))) (uniformWeight (Y i (z.2 i)))) := by
            simp only [ρ, Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
          _ ≤ C₀*(L^2*relationMass Incident (p (label tree j)) (q i)) := mul_le_mul_of_nonneg_left hs hC₀
          _ = _ := by dsimp only [C₀]; ring
      · intro i; rfl

theorem oriented_level_dual_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ L*p i a)
    (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ L*q i b)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧
        ((Y (label tree j) (z.2 (label tree j)) ∩ C.2).card : ℝ) <
          (9/10:ℝ)*(Y (label tree j) (z.2 (label tree j))).card))) ≤
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p i) (q (label tree j))) tree j := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) i => C₀ * relationMass Incident
    (uniformWeight (X i (z.1 i))) (uniformWeight (Y (label tree j) (z.2 (label tree j))))
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) := oriented_original_dual_trim f r σ hσ hq hd hq3
    (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
    c δ τ P hc hc9 hδ hτ (Y (label tree j) (z.2 (label tree j))) tree j
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z * (10*pathBudget (fun _ => 0) (ρ z) tree j) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint z) ((originalLevelLaw μ ν).nonneg z)
    _ = 10 * pathBudget (fun _ => 0) (fun i => ∑ z, originalLevelLaw μ ν z * ρ z i) tree j := by
      have he := mean_pathBudget (originalLevelLaw μ ν) (fun _ _ => 0) ρ tree j
      simp only [mul_zero, Finset.sum_const_zero] at he
      rw [← he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pathBudget_mono
      · intro i; rfl
      · intro i
        have hs := originalLevelLaw_cross_domination μ ν i (label tree j) Incident
          (X i) (Y (label tree j)) (p i) (q (label tree j)) L hL (hμ _) (hν _)
        calc
          _ = C₀*(∑ z, originalLevelLaw μ ν z * relationMass Incident
              (uniformWeight (X i (z.1 i))) (uniformWeight (Y (label tree j) (z.2 (label tree j))))) := by
            simp only [ρ, Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
          _ ≤ C₀*(L^2*relationMass Incident (p i) (q (label tree j))) := mul_le_mul_of_nonneg_left hs hC₀
          _ = _ := by dsimp only [C₀]; ring
end SharpRamseyFive.ProjectiveIncidence

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_ReachedFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
noncomputable section
universe u v w z
variable {I : Type u} {C : Type v} [Fintype C]
  (Ω : I → C → Type w) [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  (enc : ∀ i c t, Option (M i c t))

local instance (priority := high) allPropDecidable_rdc30dc_1 (P : Prop) : Decidable P := Classical.propDecidable P
omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
lemma flagAt_mono (P Q : ∀ i c, Ω i c → Prop)
    (h : ∀ i c t, P i c t → Q i c t) (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    flagAt Ω M left right enc P b ω c j = some () →
      flagAt Ω M left right enc Q b ω c j = some () := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · by_cases hp : P i c (ω.1 c) <;> by_cases hq : Q i c (ω.1 c) <;> simp_all [flagAt, flagTest, probe]
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, probe, he]
      | some m => simpa only [flagAt, probe, he, Option.map_some, Option.elim_some] using ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, probe, he]
      | some m => simpa only [flagAt, probe, he, Option.map_some, Option.elim_some] using ihr ω.2.2 (right i c (ω.1 c) m) j

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
lemma flagAt_or (P Q : ∀ i c, Ω i c → Prop)
    (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    flagAt Ω M left right enc (fun i c t => P i c t ∨ Q i c t) b ω c j = some () ↔
      flagAt Ω M left right enc P b ω c j = some () ∨
      flagAt Ω M left right enc Q b ω c j = some () := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · by_cases hp : P i c (ω.1 c) <;> by_cases hq : Q i c (ω.1 c) <;> simp [flagAt, flagTest, probe, hp, hq]
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, probe, he]
      | some m => simpa only [flagAt, probe, he, Option.map_some, Option.elim_some] using ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, probe, he]
      | some m => simpa only [flagAt, probe, he, Option.map_some, Option.elim_some] using ihr ω.2.2 (right i c (ω.1 c) m) j

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
lemma flagAt_context (P : I → C → Prop)
    (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    flagAt Ω M left right enc (fun i c _ => P i c) b ω c j = some () ↔
      ∃ c', contextAt Ω M left right enc b ω c j = some c' ∧ P (label b j) c' := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · simp [flagAt, flagTest, contextAt, probe, label]
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, contextAt, probe, he]
      | some m => simpa only [flagAt, contextAt, probe, he, Option.map_some, Option.elim_some, label] using ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, contextAt, probe, he]
      | some m => simpa only [flagAt, contextAt, probe, he, Option.map_some, Option.elim_some, label] using ihr ω.2.2 (right i c (ω.1 c) m) j

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
lemma flagAt_abort (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    flagAt Ω M left right enc (fun i c t => enc i c t = none) b ω c j = some () ↔
      abortAt Ω M left right enc b ω c j = some true := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · cases he : enc i c (ω.1 c) <;> simp [flagAt, flagTest, abortAt, probe, he]
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, abortAt, probe, he]
      | some m => simpa only [flagAt, abortAt, probe, he, Option.map_some, Option.elim_some] using ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp [flagAt, abortAt, probe, he]
      | some m => simpa only [flagAt, abortAt, probe, he, Option.map_some, Option.elim_some] using ihr ω.2.2 (right i c (ω.1 c) m) j

lemma flagAt_bound (p : ∀ i c, Law (Ω i c)) (P : ∀ i c, Ω i c → Prop)
    (ε : I → ℝ) (hε : ∀ i, 0≤ε i)
    (hlocal : ∀ i c, eventMass (p i c) (Finset.univ.filter (P i c)) ≤ ε i)
    (b : BinaryTree I) (c : C) (j : Address b) :
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
      flagAt Ω M left right enc P b ω c j = some ())) ≤ ε (label b j) := by
  have h := probe_event_bound Ω M left right p enc (flagTest Ω P) (fun x => x = some ())
    (by simp) ε hε ?_ b c j
  · rw [eventMass_map_filter] at h
    convert h using 1; congr 2
  · intro i c
    rw [eventMass_map_filter]
    simpa [flagTest] using hlocal i c

theorem reached_abort_bound (p : ∀ i c, Law (Ω i c)) (ready : I → C → Prop)
    (ε : I → ℝ) (hε : ∀ i, 0≤ε i)
    (hlocal : ∀ i c, ready i c →
      eventMass (p i c) (Finset.univ.filter (fun t => enc i c t = none)) ≤ ε i)
    (b : BinaryTree I) (c : C) (j : Address b) :
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
      abortAt Ω M left right enc b ω c j = some true)) ≤
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω => ∃ c',
      contextAt Ω M left right enc b ω c j = some c' ∧ ¬ready (label b j) c')) + ε (label b j) := by
  let P := fun i c (_ : Ω i c) => ¬ ready i c
  let Q := fun i c (t : Ω i c) => ready i c ∧ enc i c t = none
  have hs (ω : Tape Ω b) : abortAt Ω M left right enc b ω c j = some true →
      (∃ c', contextAt Ω M left right enc b ω c j = some c' ∧ ¬ ready (label b j) c') ∨
      flagAt Ω M left right enc Q b ω c j = some () := by
    intro hh
    have h := (flagAt_abort Ω M left right enc b ω c j).mpr hh
    have h' := flagAt_mono Ω M left right enc _ (fun i c t => P i c t ∨ Q i c t)
      (fun i c t ht => by by_cases hr : ready i c; exact Or.inr ⟨hr, ht⟩; exact Or.inl hr) b ω c j h
    rw [flagAt_or] at h'
    exact h'.imp (fun ha => (flagAt_context Ω M left right enc (fun i c => ¬ready i c) b ω c j).mp ha) id
  have hg : eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
      flagAt Ω M left right enc Q b ω c j = some ())) ≤ ε (label b j) := by
    apply flagAt_bound Ω M left right enc p Q ε hε
    intro i c
    by_cases hr : ready i c
    · simpa [Q, hr] using hlocal i c hr
    · simpa [Q, hr, eventMass] using hε i
  calc
    _ ≤ eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
        (∃ c', contextAt Ω M left right enc b ω c j = some c' ∧ ¬ready (label b j) c') ∨
        flagAt Ω M left right enc Q b ω c j = some ())) := eventMass_filter_mono _ _ _ hs
    _ ≤ _ := by
      have hu := eventMass_filter_union (tapeLaw Ω p b)
        (fun ω => ∃ c', contextAt Ω M left right enc b ω c j = some c' ∧ ¬ready (label b j) c')
        (fun ω => flagAt Ω M left right enc Q b ω c j = some ())
      convert hu.trans (add_le_add le_rfl hg) using 1 <;> first | rfl | congr
end
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MeanTreeFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
noncomputable section
universe u v w z s
variable {I : Type u} {C : Type v} [Fintype C]
  (Ω : I → C → Type w) [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  {Z : Type s} [Fintype Z] (μ : Law Z)
  (enc : Z → ∀ i c t, Option (M i c t))

local instance (priority := high) meanTreePropDecidable_rdc30dc_1 (P : Prop) : Decidable P := Classical.propDecidable P
lemma mean_reached_abort (p : ∀ i c, Law (Ω i c)) (ready : Z → I → C → Prop)
    (ε : I → ℝ) (hε : ∀ i, 0≤ε i)
    (hlocal : ∀ z i c, ready z i c →
      eventMass (p i c) (Finset.univ.filter (fun t => enc z i c t = none)) ≤ ε i)
    (b : BinaryTree I) (c : C) (j : Address b) :
    (∑ z, μ z * eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω =>
      abortAt Ω M left right (enc z) b ω c j = some true))) ≤
    (∑ z, μ z * eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω => ∃ c',
      contextAt Ω M left right (enc z) b ω c j = some c' ∧ ¬ready z (label b j) c'))) + ε (label b j) := by
  have h := Finset.sum_le_sum (fun z (_ : z∈(Finset.univ : Finset Z)) =>
    mul_le_mul_of_nonneg_left (reached_abort_bound Ω M left right (enc z) p (ready z) ε hε (hlocal z) b c j) (μ.nonneg z))
  simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, μ.sum_one, one_mul] using h

lemma mean_missing_mass (b : BinaryTree I) (p : Law (Tape Ω b)) (c : C) (j : Address b) :
    (∑ z, μ z * eventMass p (Finset.univ.filter (fun ω =>
      successAt Ω M left right (enc z) b ω c j = none))) =
    pathSum b (fun k => ∑ z, μ z * eventMass p (Finset.univ.filter (fun ω =>
      abortAt Ω M left right (enc z) b ω c k = some true))) j := by
  have h (z : Z) := missing_mass_path Ω M left right (enc z) b p c j
  have hh := mean_pathSum μ b (fun z k => eventMass p (Finset.univ.filter (fun ω =>
    abortAt Ω M left right (enc z) b ω c k = some true))) j
  calc
    _ = ∑ z, μ z * pathSum b (fun k => eventMass p (Finset.univ.filter (fun ω =>
        abortAt Ω M left right (enc z) b ω c k = some true))) j := by
      apply Finset.sum_congr rfl
      intro z _
      convert congrArg (fun a : ℝ => μ z*a) (h z) using 1 <;> congr
      funext k
      congr 1
      ext ω
      simp only [Finset.mem_filter]
    _ = _ := hh

lemma mean_missing_mass_le (b : BinaryTree I) (p : Law (Tape Ω b)) (c : C)
    (B : Address b → ℝ)
    (h : ∀ k, (∑ z, μ z*eventMass p (Finset.univ.filter (fun ω =>
      abortAt Ω M left right (enc z) b ω c k = some true))) ≤ B k)
    (j : Address b) :
    (∑ z, μ z*eventMass p (Finset.univ.filter (fun ω =>
      successAt Ω M left right (enc z) b ω c j = none))) ≤ pathSum b B j := by
  rw [mean_missing_mass]
  exact pathSum_mono b _ _ h j
end
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OriginalReadiness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) allPropDecidable_rdc30dc_2 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma not_original_ready_iff (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA : A₀.Nonempty) (hB : B₀.Nonempty) (δ τ : ℝ) :
    ¬OriginalNodeReady A₀ UA B₀ UB δ τ ↔
      ((A₀∩UA).card:ℝ) < δ*A₀.card ∨ ((B₀∩UB).card:ℝ) < δ*B₀.card ∨
        τ < (Nat.card K:ℝ)*relationMass Incident (uniformWeight A₀) (uniformWeight B₀) := by
  rw [OriginalNodeReady, incidences, scaled_uniform_density_iff Incident A₀ B₀ hA hB]
  simp only [not_and_or, not_le]

theorem original_not_ready_mass {W : Type*} [Fintype W] (p : Law W)
    (A₀ : Finset (ℙ K V)) (B₀ : Finset (ℙ K (Dual K V)))
    (hA : A₀.Nonempty) (hB : B₀.Nonempty) (δ τ : ℝ)
    (ctx : W → Option (PivotContext K V)) :
    eventMass p (Finset.univ.filter (fun ω => ∃ C,
      ctx ω = some C ∧ ¬OriginalNodeReady A₀ C.1 B₀ C.2 δ τ)) ≤
      eventMass p (Finset.univ.filter (fun ω => ∃ C,
        ctx ω = some C ∧ ((A₀∩C.1).card:ℝ) < δ*A₀.card)) +
      eventMass p (Finset.univ.filter (fun ω => ∃ C,
        ctx ω = some C ∧ ((B₀∩C.2).card:ℝ) < δ*B₀.card)) +
      if τ < (Nat.card K:ℝ)*relationMass Incident (uniformWeight A₀) (uniformWeight B₀) then 1 else 0 := by
  let P := fun ω => ∃ C, ctx ω = some C ∧ ((A₀∩C.1).card:ℝ) < δ*A₀.card
  let Q := fun ω => ∃ C, ctx ω = some C ∧ ((B₀∩C.2).card:ℝ) < δ*B₀.card
  let E := τ < (Nat.card K:ℝ)*relationMass Incident (uniformWeight A₀) (uniformWeight B₀)
  have hd : eventMass p (Finset.univ.filter (fun _ : W => E)) = if E then 1 else 0 := by
    by_cases h : E <;> simp [h, eventMass, p.sum_one]
  have hs : ∀ ω, (∃ C, ctx ω = some C ∧ ¬OriginalNodeReady A₀ C.1 B₀ C.2 δ τ) → (P ω ∨ Q ω) ∨ E := by
    rintro ω ⟨C,hC,hr⟩
    rcases (not_original_ready_iff A₀ C.1 B₀ C.2 hA hB δ τ).mp hr with ha | hb | he
    · exact Or.inl (Or.inl ⟨C,hC,ha⟩)
    · exact Or.inl (Or.inr ⟨C,hC,hb⟩)
    · exact Or.inr he
  calc
    _ ≤ eventMass p (Finset.univ.filter (fun ω => (P ω ∨ Q ω) ∨ E)) := eventMass_filter_mono _ _ _ hs
    _ ≤ eventMass p (Finset.univ.filter (fun ω => P ω ∨ Q ω)) + eventMass p (Finset.univ.filter (fun _ : W => E)) := by
      convert eventMass_filter_union p (fun ω => P ω ∨ Q ω) (fun _ : W => E) using 1 <;> first | rfl | congr
    _ ≤ _ := by rw [hd]; convert add_le_add (eventMass_filter_union p P Q) (le_refl (if E then (1:ℝ) else 0)) using 1 <;> first | rfl | congr
end
end

open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) levelReadinessPropDecidable_rdc30dc_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_level_not_ready
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ L*p i a)
    (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ L*q i b)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2) (hτpos : 0<τ)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧
        ¬OriginalNodeReady (X (label tree j) (z.1 (label tree j))) C.1
          (Y (label tree j) (z.2 (label tree j))) C.2 (9/10) τ))) ≤
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p (label tree j)) (q i)) (fun _ => 0) tree j +
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p i) (q (label tree j))) tree j +
      ((Nat.card K:ℝ)/τ)*L^2*relationMass Incident (p (label tree j)) (q (label tree j)) := by
  let i := label tree j
  let ctx := fun (z : (∀ i, A i) × (∀ i, B i)) (ω : OrientedPivotTreeTape f r tree) =>
    orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
      (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j
  let EA := fun (z : (∀ i, A i) × (∀ i, B i)) => eventMass (orientedPivotTreeLaw f r tree)
    (Finset.univ.filter (fun ω => ∃ C, ctx z ω = some C ∧ ((X i (z.1 i)∩C.1).card:ℝ) < (9/10:ℝ)*(X i (z.1 i)).card))
  let EB := fun (z : (∀ i, A i) × (∀ i, B i)) => eventMass (orientedPivotTreeLaw f r tree)
    (Finset.univ.filter (fun ω => ∃ C, ctx z ω = some C ∧ ((Y i (z.2 i)∩C.2).card:ℝ) < (9/10:ℝ)*(Y i (z.2 i)).card))
  let ED := fun (z : (∀ i, A i) × (∀ i, B i)) =>
    τ < (Nat.card K:ℝ)*relationMass Incident (uniformWeight (X i (z.1 i))) (uniformWeight (Y i (z.2 i)))
  have ha := oriented_level_point_trim f r σ hσ hq hd hq3 μ ν X Y hX hY p q L hL hμ hν c δ τ P hc hc9 hδ hτ tree j
  have hb := oriented_level_dual_trim f r σ hσ hq hd hq3 μ ν X Y hX hY p q L hL hμ hν c δ τ P hc hc9 hδ hτ tree j
  have hdens := original_level_density_rejection μ ν i i Incident (X i) (Y i) (p i) (q i) L hL (hμ i) (hν i)
    (Nat.card K) τ (Nat.cast_nonneg _) hτpos
  have he : (∑ z, originalLevelLaw μ ν z * (if ED z then 1 else 0)) = eventMass (originalLevelLaw μ ν) (Finset.univ.filter ED) := by
    simp only [eventMass, Finset.sum_filter, mul_ite, mul_one, mul_zero]
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z * (EA z + EB z + if ED z then 1 else 0) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (original_not_ready_mass (orientedPivotTreeLaw f r tree)
        (X i (z.1 i)) (Y i (z.2 i)) (hX i _) (hY i _) (9/10) τ (ctx z)) ((originalLevelLaw μ ν).nonneg z)
    _ = (∑ z, originalLevelLaw μ ν z * EA z) + (∑ z, originalLevelLaw μ ν z * EB z) +
        eventMass (originalLevelLaw μ ν) (Finset.univ.filter ED) := by simp_rw [mul_add, Finset.sum_add_distrib]; rw [he]
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add
        · refine le_trans (le_of_eq (Finset.sum_congr rfl (fun z _ => ?_))) ha
          dsimp only [EA,ctx,i]
          congr 2
          ext ω
          simp [Finset.mem_filter]
        · refine le_trans (le_of_eq (Finset.sum_congr rfl (fun z _ => ?_))) hb
          dsimp only [EB,ctx,i]
          congr 2
          ext ω
          simp [Finset.mem_filter]
      · convert hdens using 1
        all_goals try with_reducible_and_instances rfl
end

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TreeFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTreeFailurePropDecidable_rdc30dc_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_original_tree_missing
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ L*p i a)
    (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ L*q i b)
    (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2) (hτpos : 0<τ)
    (ε : I → ℝ) (hε : ∀ i, 0≤ε i)
    (hlocal : ∀ i a b C, OriginalNodeReady (X i a) C.1 (Y i b) C.2 (9/10) τ →
      eventMass (orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K))
        (Finset.univ.filter (fun t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
          (X i a) C.1 (Y i b) C.2 (hX i a) (hY i b) c δ τ P hδ t = none)) ≤ ε i)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω =>
        orientedPivotSuccessAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = none))) ≤
    pathSum tree (fun k =>
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p (label tree k)) (q i)) (fun _ => 0) tree k +
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p i) (q (label tree k))) tree k +
      ((Nat.card K:ℝ)/τ)*L^2*relationMass Incident (p (label tree k)) (q (label tree k)) + ε (label tree k)) j := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let l := fun _ : I => orientedPivotLeft f r
  let rt := fun _ : I => orientedPivotRight f r
  let tape := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let enc := fun (z : (∀ i, A i) × (∀ i, B i)) i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (X i (z.1 i)) C.1 (Y i (z.2 i)) C.2 (hX i _) (hY i _) c δ τ P hδ t
  let ready := fun (z : (∀ i, A i) × (∀ i, B i)) i (C : PivotContext K V) =>
    OriginalNodeReady (X i (z.1 i)) C.1 (Y i (z.2 i)) C.2 (9/10) τ
  apply mean_missing_mass_le Ω M l rt (originalLevelLaw μ ν) enc tree
  intro k
  have hh := mean_reached_abort Ω M l rt (originalLevelLaw μ ν) enc tape ready ε hε
    (fun z i C h => hlocal i (z.1 i) (z.2 i) C h) tree (Finset.univ,Finset.univ) k
  have hr := oriented_level_not_ready f r σ hσ hq hd hq3 μ ν X Y hX hY p q L hL hμ hν
    c δ τ P hc hc9 hδ hτ hτpos tree k
  exact hh.trans (add_le_add_left hr _)
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FiniteTreeFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section

local instance (priority := high) actualFiniteFailurePropDecidable_rdc30dc_1 (P : Prop) : Decidable P := Classical.propDecidable P
theorem eventually_actual_tree_missing {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (I : Type) [Fintype I] [DecidableEq I]
      (A B : I → Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
      (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
      (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
      (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
      (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
      (F : ℝ) (hF : 0≤F)
      (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ F*p i a)
      (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ F*q i b)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      (∀ i a d, (Nat.card K:ℝ)^5*Real.exp (-b)≤((X i a).card:ℝ)*(Y i d).card) →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I) (j : Address tree),
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω =>
        orientedPivotSuccessAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω (Finset.univ,Finset.univ) j = none))) ≤
    pathSum tree (fun k =>
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10)))) * F^2 *
        relationMass Incident (p (label tree k)) (q i)) (fun _ => 0) tree k +
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10)))) * F^2 *
        relationMass Incident (p i) (q (label tree k))) tree k +
      ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*relationMass Incident (p (label tree k)) (q (label tree k)) + 5*Real.exp (-(Nat.card K:ℝ))) j := by
  have ht : ∀ᶠ σ : ℝ in atTop, σ^(-1000*beta η) ≤ ((9/100000:ℝ)*(9/10)^2)/1000 := by
    have hp : 0<1000*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<((9/100000:ℝ)*(9/10)^2)/1000)).mono (fun σ h=>by simpa only [neg_mul] using h.le)
  filter_upwards [eventually_oriented_ready_encoded_failure hη hη' Cb hCb,ht] with σ hn ht
  intro D b R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 I _ _ A B _ _ μ ν X Y hX hY p q F hF hμ hν hσ hq hcard hr hL hb hbhi hprod
  dsimp only
  intro tree j
  let f := fun C : PivotContext K V =>
    fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun C : PivotContext K V =>
    fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
      (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
  refine oriented_original_tree_missing f r σ hσ hq hd hq3 μ ν X Y hX hY p q F hF hμ hν
    (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_ (fun _ => 5*Real.exp (-(Nat.card K:ℝ))) (fun _ => by positivity) ?_ tree j
  · nlinarith only [ht]
  · exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hσ) _
  · intro i a d C hready
    exact hn D b R L₀ q₀ K V hd (X i a) C.1 (Y i d) C.2 (hX i a) (hY i d)
      hσ hq hcard hr hL hb hbhi hready (hprod i a d)
end
end SharpRamseyFive.ProjectiveIncidence

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

lemma directed_failure_budget (tree : BinaryTree I) (hord : Ordered tree)
    (ρ : I → I → ℝ) (ε C Q E : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hρ : ∀ i j,i ≤ j → ρ i j ≤ ε) (j : Address tree) :
    pathSum tree (fun k=>10*pathBudget (fun i=>C*ρ (label tree k) i) (fun _=>0) tree k+
      10*pathBudget (fun _=>0) (fun i=>C*ρ i (label tree k)) tree k+
      Q*ρ (label tree k) (label tree k)+E) j  ≤
      tree.height*(20*tree.height*C*ε+Q*ε+E) := by
  have hcap : ∀ k : Address tree,
      10*pathBudget (fun i=>C*ρ (label tree k) i) (fun _=>0) tree k+
      10*pathBudget (fun _=>0) (fun i=>C*ρ i (label tree k)) tree k+
      Q*ρ (label tree k) (label tree k)+E  ≤  20*tree.height*C*ε+Q*ε+E := by
    intro k
    have hh:=mul_nonneg hC hε
    have h1:=ordered_pathBudget_bound tree hord k (fun i=>C*ρ (label tree k) i)
      (fun _=>0) (C*ε) hh
      (fun i hi=>mul_le_mul_of_nonneg_left (hρ _ _ hi) hC) (fun _ _=>hh)
    have h2:=ordered_pathBudget_bound tree hord k (fun _=>0)
      (fun i=>C*ρ i (label tree k)) (C*ε) hh
      (fun _ _=>hh) (fun i hi=>mul_le_mul_of_nonneg_left (hρ _ _ hi) hC)
    have h3:=mul_le_mul_of_nonneg_left (hρ (label tree k) (label tree k) le_rfl) hQ
    linarith
  exact (pathSum_mono tree _ _ hcap j).trans (pathSum_const_le_height tree j _ (by positivity))

end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section

local instance (priority := high) orderedRetentionPropDecidable_rdc30dc_1 (P : Prop) : Decidable P := Classical.propDecidable P
theorem eventually_ordered_tree_missing_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
      (A B : I  →  Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
      (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
      (X : ∀ i, A i  →  Finset (ℙ K V)) (Y : ∀ i, B i  →  Finset (ℙ K (Dual K V)))
      (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
      (p : I  →  Law (ℙ K V)) (q : I  →  Law (ℙ K (Dual K V)))
      (F ε : ℝ) (hF : 0 ≤ F) (hε : 0 ≤ ε)
      (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a)  ≤  F*p i a)
      (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b)  ≤  F*q i b)
      (hsparse : ∀ i j,i ≤ j → relationMass Incident (p i) (q j) ≤ ε)
      (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀  →  Range η σ D R  →  (L₀:ℝ)=L η σ D  →
      0 ≤ b  →  b ≤ Cb*D*σ^(6*beta η)  →
      (∀ i a d, (Nat.card K:ℝ)^5*Real.exp (-b) ≤ ((X i a).card:ℝ)*(Y i d).card)  →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree),
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω =>
        orientedPivotSuccessAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω (Finset.univ,Finset.univ) j = none)))  ≤
      tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2*ε+
        ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*ε+5*Real.exp (-(Nat.card K:ℝ))) := by
  filter_upwards [eventually_actual_tree_missing hη hη' Cb hCb] with σ hh
  intro D b R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 I _ _ _ A B _ _ μ ν X Y hX hY p q F ε hF hε hμ hν hsparse hσ hq hcard hr hL hb hbhi hprod
  dsimp only
  intro tree hord j
  have h:=hh D b R L₀ q₀ K V hd hq3 I A B μ ν X Y hX hY p q F hF hμ hν hσ hq hcard hr hL hb hbhi hprod tree j
  apply h.trans
  have hn:=directed_failure_budget tree hord (fun i j=>relationMass Incident (p i) (q j)) ε
    ((50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2)
    (((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2)
    (5*Real.exp (-(Nat.card K:ℝ))) hε (by positivity) (by positivity) (by positivity) hsparse j
  simpa only [mul_assoc] using hn
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing_oai := @OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing_oai
