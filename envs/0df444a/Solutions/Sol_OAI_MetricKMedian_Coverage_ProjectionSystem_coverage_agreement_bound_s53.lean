-- Prove2me | solution 1 for OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:07:22.863857+00:00
-- url     : https://prove2.me/submissions/76a2bed8-bd62-46b0-bc56-0bd6dd4695cb

import Mathlib
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K006
import Theorems.Thm_OAI_MetricKMedian_Coverage_ProjectionSystem_coverage_bound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Projection
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv _root_.OAI.MetricKMedian.Coverage.ProjectionSystem.mem_agreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

namespace ProjectionSystem
variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

theorem labels_sum (S : Finset (U × A)) : ∑ u, (labels S u).card = S.card := by
  simp only [labels, card_eq_sum_ones, sum_filter]
  rw [← Fintype.sum_prod_type (fun p : U × A => if p ∈ S then (1 : ℕ) else 0)]
  simp

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem regular_sum {d : ℕ} (hreg : G.LeftRegular d) (f : U → ℕ) :
    (∑ v, ∑ i, f (G.neighbor v i)) = d * ∑ u, f u := by
  rw [← Fintype.sum_prod_type (fun p : V × I => f (G.neighbor p.1 p.2))]
  have he (p : V × I) : f (G.neighbor p.1 p.2) =
      ∑ u, if G.neighbor p.1 p.2 = u then f u else 0 := by simp
  simp_rw [he]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro u _
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, hreg u, Nat.cast_id]

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem regular_degrees {d : ℕ} (hreg : G.LeftRegular d) :
    d * Fintype.card U = Fintype.card I * Fintype.card V := by
  have hh := G.regular_sum hreg (fun _ => 1)
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] at hh
  simpa only [mul_comm] using hh.symm

end ProjectionSystem
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_TwoChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

theorem card_two_constraints {U : Type} [Fintype U] [DecidableEq U]
    (C : U → Type) [∀ u, Fintype (C u)] [∀ u, DecidableEq (C u)] (u v : U) (huv : u ≠ v)
    (a : C u) (b : C v) :
    Fintype.card (∀ w, C w) ≤ Fintype.card (C u) * Fintype.card (C v) *
      Fintype.card {f : ∀ w, C w // f u = a ∧ f v = b} := by
  classical
  let fill (f : ∀ w, C w) := Function.update (Function.update f u a) v b
  have hf (f : ∀ w, C w) : fill f u = a ∧ fill f v = b := by
    simp [fill, Function.update_of_ne huv]
  let enc (f : ∀ w, C w) : (C u × C v) × {f : ∀ w, C w // f u = a ∧ f v = b} :=
    ((f u,f v),⟨fill f,hf f⟩)
  have hinj : Function.Injective enc := by
    intro f g h
    have hu : f u = g u := congrArg (fun z => z.1.1) h
    have hv : f v = g v := congrArg (fun z => z.1.2) h
    have hh : fill f = fill g := congrArg (fun z => z.2.val) h
    funext w
    by_cases hw : w = u
    · subst w; exact hu
    by_cases hw' : w = v
    · subst w; exact hv
    have he := congrFun hh w
    simpa [fill,Function.update_of_ne hw,Function.update_of_ne hw'] using he
  have hh := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_prod] using hh

theorem two_choice_event_count {U V : Type} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (C : U → Type) [∀u, Fintype (C u)]
    (t : ℕ) (hsize : ∀ u, Fintype.card (C u) ≤ t)
    (events : (∀u, C u) → Finset V) (charged : Finset V)
    (hcharge : ∀ v ∈ charged, ∃ u w : U, u ≠ w ∧ ∃ a : C u, ∃ b : C w,
      ∀ f : ∀u, C u, f u = a → f w = b → v ∈ events f) :
    charged.card * Fintype.card (∀u, C u) ≤ t^2 * ∑ f, (events f).card := by
  classical
  have hpoint (v : V) (hv : v ∈ charged) :
      Fintype.card (∀u, C u) ≤ t^2 * (univ.filter (fun f : ∀u, C u => v ∈ events f)).card := by
    obtain ⟨u,w,huw,a,b,h⟩ := hcharge v hv
    have hc := card_two_constraints C u w huw a b
    have hsub : Fintype.card {f : ∀u, C u // f u = a ∧ f w = b} ≤
        Fintype.card {f : ∀u, C u // v ∈ events f} := by
      exact Fintype.card_le_of_injective
        (fun f => ⟨f.val,h f.val f.property.1 f.property.2⟩)
        (fun f g hh => Subtype.ext
          (congrArg (fun z : {f : ∀u, C u // v ∈ events f} => z.val) hh))
    have hm : Fintype.card (C u)*Fintype.card (C w) ≤ t^2 := by
      simpa only [pow_two] using Nat.mul_le_mul (hsize u) (hsize w)
    calc
      _ ≤ _ := hc
      _ ≤ t^2 * Fintype.card {f : ∀u, C u // v ∈ events f} := Nat.mul_le_mul hm hsub
      _ = _ := by rw [Fintype.card_subtype]
  have hd : (∑ v, (univ.filter (fun f : ∀u, C u => v ∈ events f)).card) =
      ∑ f, (events f).card := by
    simp only [card_filter]
    rw [sum_comm]
    simp only [sum_boole,filter_mem_eq_inter,univ_inter,Nat.cast_id]
  calc
    _ = ∑ v ∈ charged, Fintype.card (∀u, C u) := by simp
    _ ≤ ∑ v ∈ charged, t^2*(univ.filter (fun f : ∀u, C u => v ∈ events f)).card :=
      sum_le_sum hpoint
    _ = t^2 * ∑ v ∈ charged, (univ.filter (fun f : ∀u, C u => v ∈ events f)).card := by
      rw [mul_sum]
    _ ≤ t^2 * ∑ v, (univ.filter (fun f : ∀u, C u => v ∈ events f)).card := by
      exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset (subset_univ _))
    _ = _ := by rw [hd]

theorem two_choice_event_bound {U V : Type} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (C : U → Type) [∀u, Fintype (C u)]
    [∀u, Nonempty (C u)] (t : ℕ) (hsize : ∀ u, Fintype.card (C u) ≤ t)
    (events : (∀u, C u) → Finset V) (charged : Finset V)
    (hcharge : ∀ v ∈ charged, ∃ u w : U, u ≠ w ∧ ∃ a : C u, ∃ b : C w,
      ∀ f : ∀u, C u, f u = a → f w = b → v ∈ events f)
    (γ : ℝ) (hsound : ∀ f, ((events f).card:ℝ) ≤ γ * Fintype.card V) :
    (charged.card:ℝ) ≤ (t:ℝ)^2 * γ * Fintype.card V := by
  classical
  have hc := two_choice_event_count C t hsize events charged hcharge
  have hr : (charged.card:ℝ) * Fintype.card (∀u, C u) ≤
      (t:ℝ)^2 * ∑ f, ((events f).card:ℝ) := by exact_mod_cast hc
  have hs := sum_le_sum (s := (univ : Finset (∀u, C u))) (fun f _ => hsound f)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (t:ℝ))
  have hp : (0:ℝ) < Fintype.card (∀u, C u) := by
    exact_mod_cast Fintype.card_pos
  nlinarith

theorem two_choice_or_trivial_event_bound {U V : Type} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (C : U → Type) [∀u, Fintype (C u)]
    [∀u, Nonempty (C u)] {t : ℕ} (ht : 1 ≤ t)
    (hsize : ∀ u, Fintype.card (C u) ≤ t)
    (events : (∀u, C u) → Finset V) (charged : Finset V)
    (hcharge : ∀ v ∈ charged, (∀ f, v ∈ events f) ∨
      ∃ u w : U, u ≠ w ∧ ∃ a : C u, ∃ b : C w,
        ∀ f : ∀u, C u, f u = a → f w = b → v ∈ events f)
    (γ : ℝ) (hsound : ∀ f, ((events f).card:ℝ) ≤ γ * Fintype.card V) :
    (charged.card:ℝ) ≤ (t:ℝ)^2 * γ * Fintype.card V := by
  classical
  let D : U ⊕ Bool → Type := Sum.elim C (fun _ => Unit)
  let (u : U ⊕ Bool) : Fintype (D u) := by cases u <;> dsimp [D] <;> infer_instance
  let (u : U ⊕ Bool) : Nonempty (D u) := by cases u <;> dsimp [D] <;> infer_instance
  have hD (u : U ⊕ Bool) : Fintype.card (D u) ≤ t := by
    cases u with
    | inl u => exact hsize u
    | inr b => simpa [D] using ht
  let ev (f : ∀u, D u) := events (fun u => f (Sum.inl u))
  apply two_choice_event_bound D t hD ev charged _ γ (fun f => hsound _)
  intro v hv
  rcases hcharge v hv with h | ⟨u,w,huw,a,b,h⟩
  · refine ⟨Sum.inr false,Sum.inr true,by simp,(),(),?_⟩
    intro f _ _
    exact h _
  · refine ⟨Sum.inl u,Sum.inl w,(fun hh => huw (Sum.inl.inj hh)),a,b,?_⟩
    intro f hf hg
    exact h (fun u => f (Sum.inl u)) hf hg

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Lists
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.ProjectionSystem
open Finset

variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

omit [Fintype B] [DecidableEq I] [DecidableEq B] in
theorem heavy_bound {d : ℕ} (hreg : G.LeftRegular d)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) (t : ℕ) :
    t * (G.heavyHit S t).card ≤ Fintype.card I * Fintype.card V := by
  have hp (v : V) : (if v ∈ G.heavyHit S t then t else 0) ≤
      ∑ i, (labels S (G.neighbor v i)).card := by
    split_ifs with hv
    · obtain ⟨i,hi⟩ := (show ∃ i, t < (labels S (G.neighbor v i)).card by
        simpa only [heavyHit,mem_filter,mem_univ,true_and] using hv)
      exact hi.le.trans (single_le_sum (f := fun i => (labels S (G.neighbor v i)).card)
        (fun _ _ => Nat.zero_le _) (mem_univ i))
    · exact Nat.zero_le _
  have hh := sum_le_sum (s := (univ : Finset V)) (fun v _ => hp v)
  have he : (∑ v, if v ∈ G.heavyHit S t then t else 0) = t*(G.heavyHit S t).card := by
    rw [← sum_filter]
    simp [mul_comm]
  rw [he,G.regular_sum hreg (fun u => (labels S u).card),labels_sum] at hh
  exact hh.trans ((Nat.mul_le_mul_left d hS).trans_eq (G.regular_degrees hreg))

omit [Fintype U] in
theorem capped_nonempty (S : Finset (U × A)) (t : ℕ) (default : A) (u : U) :
    (cappedLabels S t default u).Nonempty := by
  unfold cappedLabels
  split_ifs with h
  · exact h.2
  · exact singleton_nonempty _

omit [Fintype U] in
theorem capped_card (S : Finset (U × A)) {t : ℕ} (ht : 1 ≤ t) (default : A) (u : U) :
    (cappedLabels S t default u).card ≤ t := by
  unfold cappedLabels
  split_ifs with h
  · exact h.1
  · simpa only [card_singleton] using ht

omit [Fintype U] in
theorem mem_capped (S : Finset (U × A)) {t : ℕ} (default : A) {u : U} {a : A}
    (hsmall : (labels S u).card ≤ t) (ha : (u,a) ∈ S) :
    a ∈ cappedLabels S t default u := by
  have hm : a ∈ labels S u := (mem_labels S u a).mpr ha
  rw [cappedLabels,ite_eq_left ⟨hsmall,⟨a,hm⟩⟩]
  exact hm

theorem lowBad_bound (hdup : G.DuplicateConsistent)
    (S : Finset (U × A)) {t : ℕ} (ht : 1 ≤ t) (default : A)
    (γ : ℝ) (hsound : ∀ left, ((G.agreement left).card:ℝ) ≤ γ*Fintype.card V) :
    ((G.lowBad S t).card:ℝ) ≤ (t:ℝ)^2*γ*Fintype.card V := by
  classical
  let C (u : U) := {a : A // a ∈ cappedLabels S t default u}
  have hc (u : U) : Fintype.card (C u) ≤ t := by
    simpa only [C,Fintype.card_coe] using capped_card S ht default u
  let (u : U) : Nonempty (C u) :=
    let ⟨a,ha⟩ := capped_nonempty S t default u
    ⟨⟨a,ha⟩⟩
  let events (f : ∀u, C u) := G.agreement (fun u => (f u).val)
  apply two_choice_or_trivial_event_bound C ht hc events (G.lowBad S t) _ γ (fun f => hsound _)
  intro v hv
  have hbad : v ∈ G.bad S := (mem_sdiff.mp hv).1
  have hlow : v ∉ G.heavyHit S t := (mem_sdiff.mp hv).2
  have hsmall : ∀ i, (labels S (G.neighbor v i)).card ≤ t := by
    simpa only [heavyHit,mem_filter,mem_univ,true_and,not_exists,not_lt] using hlow
  obtain ⟨b,hb⟩ := (show ∃ b, 1 < (G.parts S v b).card by
    simpa only [bad,mem_filter,mem_univ,true_and] using hbad)
  obtain ⟨i,hi,j,hj,hij⟩ := one_lt_card.mp hb
  obtain ⟨a,ha,hpa⟩ := (G.mem_parts S v b i).mp hi
  obtain ⟨a',ha',hpa'⟩ := (G.mem_parts S v b j).mp hj
  let aC : C (G.neighbor v i) := ⟨a,mem_capped S default (hsmall i) ha⟩
  let bC : C (G.neighbor v j) := ⟨a',mem_capped S default (hsmall j) ha'⟩
  by_cases hsame : G.neighbor v i = G.neighbor v j
  · left
    intro f
    apply (G.mem_agreement _ v).mpr
    refine ⟨i,j,hij,?_⟩
    rw [hdup v i j hsame,hsame]
  · right
    refine ⟨G.neighbor v i,G.neighbor v j,hsame,aC,bC,?_⟩
    intro f hf hg
    change v ∈ G.agreement (fun u => (f u).val)
    apply (G.mem_agreement _ v).mpr
    refine ⟨i,j,hij,?_⟩
    rw [hf,hg]
    exact hpa.trans hpa'.symm

theorem bad_bound {d : ℕ} (hreg : G.LeftRegular d)
    (hdup : G.DuplicateConsistent)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U)
    {t : ℕ} (ht : 1 ≤ t) (default : A)
    (γ : ℝ) (hsound : ∀ left, ((G.agreement left).card:ℝ) ≤ γ*Fintype.card V) :
    ((G.bad S).card:ℝ) ≤ ((Fintype.card I:ℝ)/t+(t:ℝ)^2*γ)*Fintype.card V := by
  have hl := G.lowBad_bound hdup S ht default γ hsound
  have hh := G.heavy_bound hreg S hS t
  have hr : (t:ℝ)*((G.heavyHit S t).card:ℝ) ≤
      (Fintype.card I:ℝ)*Fintype.card V := by exact_mod_cast hh
  have hc : (G.bad S).card ≤ (G.lowBad S t).card+(G.heavyHit S t).card := by
    have he : G.bad S ⊆ G.lowBad S t ∪ G.heavyHit S t := by
      intro v hv
      by_cases hh : v ∈ G.heavyHit S t
      · exact mem_union_right _ hh
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,hh⟩)
    exact (card_le_card he).trans (card_union_le _ _)
  have hcr : ((G.bad S).card:ℝ) ≤ (G.lowBad S t).card+(G.heavyHit S t).card := by
    exact_mod_cast hc
  have ht0 : (0:ℝ) < t := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  have hheavy : ((G.heavyHit S t).card:ℝ) ≤
      (Fintype.card I:ℝ)/t*Fintype.card V := by
    calc
      _ ≤ ((Fintype.card I:ℝ)*Fintype.card V)/t :=
        (le_div_iff₀ ht0).mpr (by nlinarith [hr])
      _ = _ := by ring
  nlinarith

theorem coverage_agreement_bound_s53_oai {d : ℕ} (hreg : G.LeftRegular d)
    (hI : 1 < Fintype.card I) (hdup : G.DuplicateConsistent)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U)
    {t : ℕ} (ht : 1 ≤ t) (default : A)
    (γ : ℝ) (hsound : ∀ left, ((G.agreement left).card:ℝ) ≤ γ*Fintype.card V) :
    ((G.covered S).card:ℝ) ≤
      (1-(1-1/(Fintype.card I:ℝ))^Fintype.card I+
        (Fintype.card I:ℝ)/t+(t:ℝ)^2*γ) *
        ((Fintype.card V:ℝ)*(Fintype.card I:ℝ)^Fintype.card B) := by
  have hc := G.coverage_bound_s53 hreg hI S hS
  have hb := G.bad_bound hreg hdup S hS ht default γ hsound
  have hm := mul_le_mul_of_nonneg_left hb
    (pow_nonneg (Nat.cast_nonneg (Fintype.card I)) (Fintype.card B) :
      (0:ℝ) ≤ (Fintype.card I:ℝ)^Fintype.card B)
  nlinarith

end MetricKMedian.Coverage.ProjectionSystem

end Inline_PCPInherited

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound_s53_oai := @OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound_s53_oai
