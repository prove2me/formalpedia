-- Prove2me | solution 1 for OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:44:52.160668+00:00
-- url     : https://prove2.me/submissions/bf6857c5-5296-4e33-914e-b0244c9b6362

import Mathlib
import Definitions.Def_OAIQ045S002

section
-- module Solutions.OAIQ045_SR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem event_transfer (p q : Law α) (hab : p.AbsolutelyContinuous q) (E : Finset α) :
    q.event E ≤ 2*(divergence p q+p.event E) := by
  have hlog2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have pointwise (a : α) : p.mass a-q.mass a + (if a ∈ E then q.mass a/2 else 0) ≤
      p.mass a*Real.log (p.mass a/q.mass a)+(if a ∈ E then p.mass a*Real.log 2 else 0) := by
    by_cases ha : a ∈ E
    · simp only [ite_eq_left ha]
      have h := mul_log_div_ge (p.nonneg a) (div_nonneg (q.nonneg a) (by norm_num : (0:ℝ) ≤ 2))
        (fun h => hab a (by linarith))
      by_cases hp : p.mass a = 0
      · simp only [hp,zero_mul,zero_sub] at h ⊢; linarith
      have hp0 := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      have hq : q.mass a ≠ 0 := fun h => hp (hab a h)
      have he : Real.log (p.mass a/(q.mass a/2)) =
          Real.log (p.mass a/q.mass a)+Real.log 2 := by
        rw [div_div_eq_mul_div, mul_div_right_comm,
          Real.log_mul (div_ne_zero hp hq) (by norm_num)]
      rw [he] at h
      nlinarith
    · simpa only [ite_eq_right ha,add_zero] using mul_log_div_ge (p.nonneg a) (q.nonneg a) (hab a)
  have h := sum_le_sum (fun a (_ : a ∈ univ) => pointwise a)
  simp only [sum_add_distrib, sum_sub_distrib, p.total, q.total, sub_self, zero_add,
    ← sum_filter, filter_mem_eq_inter, univ_inter] at h
  rw [← sum_div, ← sum_mul] at h
  change q.event E/2 ≤ divergence p q+p.event E*Real.log 2 at h
  have hh := mul_le_mul_of_nonneg_left hlog2 (p.event_nonneg E)
  nlinarith

theorem mutualInfo_event_transfer (p : Law (α × β)) (E : Finset (α × β)) :
    (p.fst.prod p.snd).event E ≤ 2*(mutualInfo p+p.event E) := by
  rw [mutualInfo_eq_divergence]
  exact event_transfer p _ p.absContinuous_prod E

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem Law.le_map (p : Law α) (f : α → β) (a : α) :
    p.mass a ≤ (p.map f).mass (f a) := by
  apply single_le_sum (fun b hb => p.nonneg b)
  simp

theorem Law.snd_mul_condFst (p : Law (α × β)) (a : α) (b : β) :
    p.snd.mass b*(p.condFst b).mass a = p.mass (a,b) := by
  by_cases h : p.snd.mass b = 0
  · rw [h,zero_mul]
    exact (le_antisymm (by simpa [h] using p.le_snd a b) (p.nonneg _)).symm
  · rw [p.condFst_mass b h a]
    field_simp

theorem entropy_chain (p : Law (α × β)) :
    entropy p = entropy p.snd+∑ b, p.snd.mass b*entropy (p.condFst b) := by
  have pointwise (a : α) (b : β) :
      p.mass (a,b)*Real.log (p.mass (a,b)) =
      p.mass (a,b)*Real.log (p.snd.mass b)+
      p.snd.mass b*((p.condFst b).mass a*Real.log ((p.condFst b).mass a)) := by
    by_cases hp : p.mass (a,b) = 0
    · have hh := p.snd_mul_condFst a b
      rw [hp] at hh
      simp only [hp,zero_mul,zero_add]
      rw [← mul_assoc,hh,zero_mul]
    have hs : 0 < p.snd.mass b := (lt_of_le_of_ne (p.nonneg (a,b)) (Ne.symm hp)).trans_le (p.le_snd a b)
    rw [p.condFst_mass b hs.ne', Real.log_div hp hs.ne']
    field_simp
    ring
  unfold entropy
  rw [Fintype.sum_prod_type, sum_comm]
  simp_rw [pointwise, sum_add_distrib, ← mul_sum, ← sum_mul]
  change -((∑ b, p.snd.mass b*Real.log (p.snd.mass b))+
    ∑ b, p.snd.mass b*∑ a, (p.condFst b).mass a*Real.log ((p.condFst b).mass a)) = _
  simp only [mul_neg, sum_neg_distrib]
  ring

end SharpLogRamsey.Selection
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β B X ι : Type*} [Fintype β] [Fintype B] [Fintype X] [Fintype ι]
  [DecidableEq B] [DecidableEq ι]

omit [Fintype X] in
lemma not_badIndices (p : Law (ι→β)) (e : B×X ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) (f : B→X) (i : ι) :
    i∉badIndices p e own c J D a f ↔
      J-entropy (p.marginal i)≤D ∧
      ∀ j∈otherRepresentatives e own f i,(pairInformation p i j:ℝ)+(c i j:ℝ)≤a := by
  simp [badIndices]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

theorem Law.small_atoms (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) {c : ℝ} (hc : 0 ≤ c) :
    p.event (univ.filter (fun a => p.mass a < c)) ≤ S.card*c := by
  have h (a : α) : (if p.mass a < c then p.mass a else 0) ≤
      if a ∈ S then c else 0 := by
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha]; split_ifs <;> linarith
    · rw [ite_eq_right ha,hs a ha]; split_ifs <;> rfl
  have hh := sum_le_sum fun a (_ : a ∈ univ) => h a
  simpa [Law.event, sum_filter] using hh

theorem negative_log_part (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) :
    (∑ a, p.mass a*max (-(Real.log (p.mass a)+L)) 0) ≤ S.card*Real.exp (-L) := by
  have pointwise (a : α) : p.mass a*max (-(Real.log (p.mass a)+L)) 0 ≤
      if a ∈ S then Real.exp (-L) else 0 := by
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha]
      by_cases hp : p.mass a = 0
      · simp [hp,Real.exp_nonneg]
      have hp0 : 0 < p.mass a := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      by_cases hz : 0 ≤ -(Real.log (p.mass a)+L)
      · rw [max_eq_left hz]
        have hh := mul_log_div_ge (p.nonneg a) (Real.exp_nonneg (-L))
          (fun h => False.elim ((Real.exp_ne_zero _) h))
        rw [Real.log_div hp (Real.exp_ne_zero _),Real.log_exp] at hh
        nlinarith
      · rw [max_eq_right (le_of_not_ge hz),mul_zero]
        exact Real.exp_nonneg _
    · rw [ite_eq_right ha,hs a ha,zero_mul]
  have h := sum_le_sum fun a (_ : a ∈ univ) => pointwise a
  simpa using h

theorem positive_log_part (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) :
    (∑ a, p.mass a*max (Real.log (p.mass a)+L) 0) ≤
      L-entropy p+S.card*Real.exp (-L) := by
  have pointwise (a : α) : p.mass a*max (Real.log (p.mass a)+L) 0 =
      p.mass a*(Real.log (p.mass a)+L)+
      p.mass a*max (-(Real.log (p.mass a)+L)) 0 := by
    by_cases h : 0 ≤ Real.log (p.mass a)+L
    · rw [max_eq_left h,max_eq_right (by linarith)]; ring
    · rw [max_eq_right (le_of_not_ge h),max_eq_left (by linarith)]; ring
  simp_rw [pointwise,sum_add_distrib,mul_add,sum_add_distrib,← sum_mul,p.total,one_mul]
  have h := negative_log_part p S hs L
  unfold entropy
  linarith

theorem Law.heavy_atoms (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) {K : ℝ} (hK : 0 < K) :
    p.event (univ.filter (fun a => Real.exp (K-L) < p.mass a)) ≤
      (L-entropy p+S.card*Real.exp (-L))/K := by
  apply (le_div_iff₀ hK).mpr
  have h (a : α) : (if Real.exp (K-L) < p.mass a then p.mass a else 0)*K ≤
      p.mass a*max (Real.log (p.mass a)+L) 0 := by
    by_cases ha : Real.exp (K-L) < p.mass a
    · rw [ite_eq_left ha]
      have hp : 0 < p.mass a := (Real.exp_pos _).trans ha
      have hh := Real.log_lt_log (Real.exp_pos (K-L)) ha
      rw [Real.log_exp] at hh
      have hle : K ≤ max (Real.log (p.mass a)+L) 0 :=
        (by linarith : K ≤ Real.log (p.mass a)+L).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left hle (p.nonneg a)
    · rw [ite_eq_right ha,zero_mul]
      exact mul_nonneg (p.nonneg _) (le_max_right _ _)
  have hh := (sum_le_sum fun a (_ : a ∈ univ) => h a).trans (positive_log_part p S hs L)
  simpa only [Law.event,sum_filter,sum_mul] using hh

theorem Law.bad_conditional_mass (p : Law (α × β)) (E : Finset (α × β))
    {ρ : ℝ} (hρ : 0 < ρ) :
    p.snd.event (univ.filter (fun b =>
      ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E)))) ≤ p.event E/ρ := by
  apply (le_div_iff₀ hρ).mpr
  have hh (b : β) :
      (if ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E))
        then p.snd.mass b else 0)*ρ ≤ ∑ a, if (a,b) ∈ E then p.mass (a,b) else 0 := by
    have he : p.snd.mass b*((p.condFst b).event (univ.filter (fun a => (a,b) ∈ E))) =
        ∑ a, if (a,b) ∈ E then p.mass (a,b) else 0 := by
      simp only [Law.event,sum_filter,mul_sum,mul_ite,mul_zero,p.snd_mul_condFst]
    rw [← he]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left h.le (p.snd.nonneg b)
    · rw [zero_mul]
      exact mul_nonneg (p.snd.nonneg b) ((p.condFst b).event_nonneg _)
  have h := sum_le_sum fun b (_ : b ∈ univ) => hh b
  have he : (∑ z, if z ∈ E then p.mass z else 0) = p.event E := by
    rw [← sum_filter]
    simp [Law.event]
  change (∑ b with ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E)), p.snd.mass b)*ρ ≤ _
  rw [sum_filter,sum_mul,← he,Fintype.sum_prod_type,sum_comm]
  exact h

end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma Law.fst_mul_condSnd (p : Law (A × B)) (a : A) (b : B) :
    p.fst.mass a*(p.condSnd a).mass b = p.mass (a,b) := by
  have h := p.cond_map_weight Prod.fst Prod.snd a b
  rw [Law.map_fst] at h
  change p.fst.mass a*((p.cond Prod.fst a).map Prod.snd).mass b = _
  rw [h]
  simp [Law.map, Fintype.sum_prod_type, sum_filter, Prod.mk.injEq, and_comm, ite_and]

lemma Law.condSnd_mass (p : Law (A × B)) (a : A) (ha : p.fst.mass a ≠ 0) (b : B) :
    (p.condSnd a).mass b = p.mass (a,b)/p.fst.mass a := by
  apply (eq_div_iff ha).mpr
  rw [mul_comm, p.fst_mul_condSnd]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_EndpointCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.event_union_le (p : Law α) (E F : Finset α) :
    p.event (E ∪ F) ≤ p.event E+p.event F := by
  unfold Law.event
  have h : ∀ x, (if x ∈ E ∪ F then p.mass x else 0) ≤
      (if x ∈ E then p.mass x else 0)+(if x ∈ F then p.mass x else 0) := by
    intro x
    by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> simp [he,hf,p.nonneg]
  simpa only [sum_add_distrib, sum_ite_mem_eq] using
    (sum_le_sum (fun x (_ : x ∈ (univ : Finset α)) => h x))

lemma Law.event_mono (p : Law α) {E F : Finset α} (h : E ⊆ F) : p.event E ≤ p.event F :=
  sum_le_sum_of_subset_of_nonneg h (fun x _ _ => p.nonneg x)

theorem badSecond_mass (p : Law (α × β)) (S : Finset (α × β))
    (hs : ∀ x, x ∉ S → p.mass x = 0) (D : Finset β)
    (hD : ∀ b, b ∉ D → p.snd.mass b = 0)
    (M L K ρ : ℝ) (hM : 0 < M) (hcard : (D.card:ℝ) ≤ M)
    (hK : 0 < K) (hρ : 0 < ρ) :
    p.snd.event (univ.filter (fun b => ¬goodSecond p M L K ρ b)) ≤
      Real.exp (-K)+(L-entropy p+S.card*Real.exp (-L))/(K*ρ) := by
  have hsub : univ.filter (fun b => ¬goodSecond p M L K ρ b) ⊆
      univ.filter (fun b => p.snd.mass b < Real.exp (-K)/M) ∪
      univ.filter (fun b => ρ < conditionalHeavy p L K b) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and,goodSecond,not_and_or,not_le,mem_union] at hb ⊢
    exact hb
  have hsmall := p.snd.small_atoms D hD (c := Real.exp (-K)/M) (by positivity)
  have hs2 : D.card*(Real.exp (-K)/M) ≤ Real.exp (-K) := by
    calc
      _ ≤ M*(Real.exp (-K)/M) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp
  have hheavy := p.bad_conditional_mass (univ.filter (fun x => Real.exp (K-L) < p.mass x)) hρ
  have hheavy' : p.snd.event (univ.filter (fun b => ρ < conditionalHeavy p L K b)) ≤
      (L-entropy p+S.card*Real.exp (-L))/(K*ρ) := by
    have he := p.heavy_atoms S hs L hK
    have hh := hheavy.trans (div_le_div_of_nonneg_right he hρ.le)
    convert hh using 1 <;> try rfl
    · simp only [conditionalHeavy,mem_filter,mem_univ,true_and]
      with_unfolding_all rfl
    · rw [div_div]
  exact (p.snd.event_mono hsub).trans ((p.snd.event_union_le _ _).trans
    (add_le_add (hsmall.trans hs2) hheavy'))

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_AuxiliaryLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped Classical BigOperators

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.onEvent_mean (p : Law α) (E : Finset α) (hE : 0<p.event E) (f : α→ℝ) :
    ∑ a : E, (p.onEvent E hE).mass a*f a = (∑ a∈E, p.mass a*f a)/p.event E := by
  simp only [Law.onEvent,div_mul_eq_mul_div,←sum_div]
  congr 1
  exact sum_coe_sort E (fun a => p.mass a*f a)

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_EndpointSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

lemma Law.swap_eq_map (p : Law (A × B)) : p.swap = p.map Prod.swap := by
  ext ⟨b,a⟩
  exact (p.map_mass_injective Prod.swap Prod.swap_injective (a,b)).symm

@[simp] lemma entropy_swap (p : Law (A × B)) : entropy p.swap = entropy p := by
  rw [Law.swap_eq_map]
  exact entropy_map_eq_of_injective p Prod.swap Prod.swap_injective

lemma Law.swap_condFst (p : Law (A × B)) (a : A) (ha : p.fst.mass a ≠ 0) :
    p.swap.condFst a = p.condSnd a := by
  ext endpoint
  exact (p.swap.condFst_mass a ha endpoint).trans (p.condSnd_mass a ha endpoint).symm

lemma goodSecond_swap (p : Law (A × B)) {M : ℝ} (hM : 0 < M)
    (L κ ε : ℝ) (a : A) : goodSecond p.swap M L κ ε a ↔ goodFirst p M L κ ε a := by
  unfold goodSecond goodFirst conditionalHeavy
  simp only [Law.swap_snd]
  constructor <;> intro h
  · have ha : p.fst.mass a ≠ 0 := (lt_of_lt_of_le (by positivity) h.1).ne'
    rw [Law.swap_condFst p a ha] at h
    exact h
  · have ha : p.fst.mass a ≠ 0 := (lt_of_lt_of_le (by positivity) h.1).ne'
    rw [Law.swap_condFst p a ha]
    exact h

theorem badFirst_mass (p : Law (A × B)) (S : Finset (A × B))
    (hs : ∀ x, x ∉ S → p.mass x = 0) (D : Finset A)
    (hD : ∀ a, a ∉ D → p.fst.mass a = 0)
    (M L κ ε : ℝ) (hM : 0 < M) (hcard : (D.card:ℝ) ≤ M)
    (hκ : 0 < κ) (hε : 0 < ε) :
    p.fst.event (univ.filter (fun a => ¬goodFirst p M L κ ε a)) ≤
      exp (-κ) + (L - entropy p + S.card * exp (-L)) / (κ * ε) := by
  have hs' : ∀ x, x ∉ S.image Prod.swap → p.swap.mass x = 0 := by
    rintro ⟨b,a⟩ hx
    rw [Law.swap_mass]
    apply hs
    intro h
    exact hx (mem_image.mpr ⟨(a,b),h,rfl⟩)
  have H := badSecond_mass p.swap (S.image Prod.swap) hs' D
    hD M L κ ε hM hcard hκ hε
  have he : (S.image Prod.swap).card = S.card := card_image_of_injective S Prod.swap_injective
  simpa only [Law.swap_snd, goodSecond_swap p hM L κ ε, entropy_swap, he] using H

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FiniteSamplingBounds
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

theorem rowLower_highRank (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (E : Finset Ω) (h T : ℕ) (q : ℝ) (hq : 0 < q)
    (hE : 2/(5*q) ≤ ∑ x ∈ E, w x) (hT : (T:ℝ) ≤ (h:ℝ)/(10*q)+1) :
    rowLower w E h T ≤ Real.exp (1-(h:ℝ)/(10*q)) := by
  apply (rowLower_exp w hw ht E h T).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ (h:ℝ)/2 by positivity)
  have he : ((h:ℝ)/2)*(2/(5*q)) = 2*((h:ℝ)/(10*q)) := by field_simp; ring
  rw [he] at hh
  nlinarith

end
end SharpLogRamsey.FiniteSamplingBounds

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_EndpointScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section

lemma endpoint_error_scale {x b κ δ H L S C₀ : ℝ}
    (hx : 1≤x) (hb : 0≤b) (hC₀ : 0≤C₀)
    (hκ : x^(4*b)≤κ) (hδ : δ≤κ*x^(-2*b))
    (hH : L-H≤δ) (hS : S*exp (-L)≤C₀) :
    exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))≤
      (51+50*C₀)*x^(-2*b) := by
  have hx0 : 0<x := by linarith
  have hp : 0<x^(2*b) := rpow_pos_of_pos hx0 _
  have hk : x^(2*b)≤κ := (rpow_le_rpow_of_exponent_le hx (by linarith)).trans hκ
  have hk0 : 0<κ := hp.trans_le hk
  have hi : 1/κ≤x^(-2*b) := by
    have hh:=one_div_le_one_div_of_le hp hk
    simpa only [neg_mul,rpow_neg hx0.le,one_div] using hh
  have he : exp (-κ)≤1/κ := by
    rw [exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le hk0
      (show κ≤exp κ by linarith [add_one_le_exp κ]))
  have hd : δ/κ≤x^(-2*b) := (div_le_iff₀ hk0).mpr (by simpa only [mul_comm κ] using hδ)
  have hsn : (L-H+S*exp (-L))/(κ*(1/50))≤50*(δ/κ)+50*C₀*(1/κ) := by
    calc
      _ ≤ (δ+C₀)/(κ*(1/50)) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ x^(-2*b)+(50*(δ/κ)+50*C₀*(1/κ)) := add_le_add (he.trans hi) hsn
    _ ≤ x^(-2*b)+(50*x^(-2*b)+50*C₀*x^(-2*b)) := by gcongr
    _ = _ := by ring

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
section

namespace SharpLogRamsey
namespace RichUnion

noncomputable section

open Module MvPolynomial

section LinearAlgebra
variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

theorem rank_le_of_ker_le (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (h : LinearMap.ker f ≤ LinearMap.ker g) :
    finrank K (LinearMap.range g) ≤ finrank K (LinearMap.range f) := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hk := Submodule.finrank_mono h
  omega

theorem finrank_finset_sup_le {ι : Type*} [FiniteDimensional K B]
    (S : Finset ι) (W : ι → Submodule K B) :
    finrank K (S.sup W : Submodule K B) ≤ ∑ i ∈ S, finrank K (W i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

end LinearAlgebra

section Evaluation
variable {K : Type*} [Field K] {n : ℕ}

theorem evalSpace_full [Fintype K] (Z : Finset (Fin n → K)) :
    evalSpace Z (Fintype.card K - 1) = ⊤ := by
  classical
  apply top_unique
  intro f _
  let g : (Fin n → K) → K := fun v => if hv : v ∈ Z then f ⟨v, hv⟩ else 0
  have hg : g ∈ (MvPolynomial.restrictDegree (Fin n) K (Fintype.card K - 1)).map
      (MvPolynomial.evalₗ K (Fin n)) := by
    rw [MvPolynomial.map_restrict_dom_evalₗ]
    trivial
  rcases hg with ⟨p, hp, he⟩
  refine ⟨p, hp, ?_⟩
  ext z
  have hz := congrFun he z.1
  simpa [g, z.property] using hz

theorem evalSpace_box_partition (Z : Finset (Fin n → K)) (a c q : ℕ)
    (ha : 0 < a) (hq : 0 < q) (hqc : q ≤ a*c) :
    evalSpace Z (q-1) ≤
      Finset.univ.sup (fun b : Fin n → Fin c =>
        (evalSpace Z (a-1)).map (diagonal Z
          (Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)))) := by
  classical
  rw [evalSpace, MvPolynomial.restrictDegree, MvPolynomial.restrictSupport_eq_span,
    Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  let b : Fin n → Fin c := fun i => ⟨s i / a, by
    apply (Nat.div_lt_iff_lt_mul ha).mpr
    have hi := hs i
    rw [mul_comm]
    omega⟩
  let v : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)
  let r : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => s i % a)
  have hsr : s = v + r := by
    ext i
    change s i = a * (s i / a) + s i % a
    simpa [Nat.add_comm] using (Nat.mod_add_div (s i) a).symm
  have hinc : (evalSpace Z (a-1)).map (diagonal Z v) ≤
      Finset.univ.sup (fun b : Fin n → Fin c =>
        (evalSpace Z (a-1)).map (diagonal Z
          (Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)))) :=
    Finset.le_sup (f := fun b : Fin n → Fin c =>
      (evalSpace Z (a-1)).map (diagonal Z
        (Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)))) (Finset.mem_univ b)
  apply hinc
  refine Submodule.mem_map.mpr ⟨evalOn Z (MvPolynomial.monomial r 1), ?_, ?_⟩
  · refine Submodule.mem_map.mpr ⟨MvPolynomial.monomial r 1, ?_, rfl⟩
    rw [MvPolynomial.restrictDegree, MvPolynomial.monomial_mem_restrictSupport]
    left
    intro i
    have := Nat.mod_lt (s i) ha
    change s i % a ≤ a-1
    omega
  · ext z
    simp only [diagonal, LinearMap.coe_mk, AddHom.coe_mk, evalOn_apply]
    rw [hsr, ← MvPolynomial.eval_mul, MvPolynomial.monomial_mul_monomial]
    simp

theorem card_le_boxes_mul_eval_rank [Fintype K] (Z : Finset (Fin n → K))
    (a c : ℕ) (ha : 0 < a) (hqc : Fintype.card K ≤ a*c) :
    Z.card ≤ c^n * finrank K (evalSpace Z (a-1)) := by
  classical
  let W : (Fin n → Fin c) → Submodule K (Z → K) := fun b =>
    (evalSpace Z (a-1)).map (diagonal Z
      (Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)))
  have htop : (⊤ : Submodule K (Z → K)) ≤ Finset.univ.sup W := by
    rw [← evalSpace_full Z]
    exact evalSpace_box_partition Z a c (Fintype.card K) ha Fintype.card_pos hqc
  have hdim := Submodule.finrank_mono htop
  have hsum := finrank_finset_sup_le Finset.univ W
  have hle : (∑ b : Fin n → Fin c, finrank K (W b)) ≤
      c^n * finrank K (evalSpace Z (a-1)) := by
    calc
      _ ≤ ∑ _b : Fin n → Fin c, finrank K (evalSpace Z (a-1)) :=
        Finset.sum_le_sum (fun b _ => Submodule.finrank_map_le _ _)
      _ = _ := by simp
  simpa using hdim.trans (hsum.trans hle)

theorem totalDegree_aeval_linear {r : ℕ}
    (φ : Fin n → MvPolynomial (Fin r) K)
    (hφ : ∀ i, (φ i).totalDegree ≤ 1) (p : MvPolynomial (Fin n) K) :
    (MvPolynomial.aeval φ p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  rw [MvPolynomial.aeval_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ s.support, ((φ i) ^ s i).totalDegree
        ≤ ∑ i ∈ s.support, s i := by
          apply Finset.sum_le_sum
          intro i hi
          exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hφ i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hs

theorem totalDegree_linearCoordinates {r : ℕ}
    (f : (Fin r → K) →ₗ[K] (Fin n → K)) (j : Fin n) :
    (linearCoordinates f j).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  simpa using MvPolynomial.totalDegree_mul
    (MvPolynomial.C (f (Pi.single i 1) j)) (MvPolynomial.X i)

theorem eval_linearCoordinates {r : ℕ}
    (f : (Fin r → K) →ₗ[K] (Fin n → K)) (x : Fin r → K) (j : Fin n) :
    MvPolynomial.eval x (linearCoordinates f j) = f x j := by
  classical
  have hx : x = ∑ i : Fin r, x i • Pi.single i (1 : K) := by
    ext j
    simp [Pi.single_apply]
  simp only [linearCoordinates, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem eval_aeval_linearCoordinates {r : ℕ}
    (f : (Fin r → K) →ₗ[K] (Fin n → K)) (x : Fin r → K)
    (p : MvPolynomial (Fin n) K) :
    MvPolynomial.eval x (MvPolynomial.aeval (linearCoordinates f) p) =
      MvPolynomial.eval (f x) p := by
  apply MvPolynomial.induction_on p
  · intro a
    simp
  · intro a b ha hb
    simp only [map_add, ha, hb]
  · intro p i hp
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp, eval_linearCoordinates]

theorem totalDegree_le_of_restrictDegree (p : MvPolynomial (Fin n) K) (m : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree (Fin n) K m) :
    p.totalDegree ≤ n*m := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro s hs
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    ∑ i : Fin n, s i ≤ ∑ _i : Fin n, m :=
      Finset.sum_le_sum (fun i _ => (MvPolynomial.mem_restrictDegree _ _ _).mp hp s hs i)
    _ = n*m := by simp

theorem card_roots_mul_le [Fintype K] [DecidableEq K] {r : ℕ} (p : MvPolynomial (Fin r) K)
    (hp : p ≠ 0) :
    (Finset.univ.filter (fun x : Fin r → K => MvPolynomial.eval x p = 0)).card *
      Fintype.card K ≤ p.totalDegree * (Fintype.card K)^r := by
  classical
  have h := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  simp only [Finset.card_univ] at h
  simp at h
  have hq : (0 : ℚ≥0) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have h' := (div_le_div_iff₀ (pow_pos hq r) hq).mp h
  exact_mod_cast h'

theorem vanish_on_rich_subspace [Fintype K]
    (X : Finset (Fin n → K)) (W : Submodule K (Fin n → K)) (m : ℕ)
    (hrich : n*m * Nat.card W < (inSubspace X W).card * Fintype.card K)
    (p : MvPolynomial (Fin n) K) (hp : p ∈ MvPolynomial.restrictDegree (Fin n) K m)
    (hx : ∀ x ∈ X, MvPolynomial.eval x p = 0) :
    ∀ y ∈ W, MvPolynomial.eval y p = 0 := by
  classical
  let r := finrank K W
  let e : (Fin r → K) ≃ₗ[K] W := (Module.finBasis K W).equivFun.symm
  let f : (Fin r → K) →ₗ[K] (Fin n → K) := W.subtype.comp e.toLinearMap
  let P := MvPolynomial.aeval (linearCoordinates f) p
  have hPdeg : P.totalDegree ≤ n*m :=
    (totalDegree_aeval_linear _ (totalDegree_linearCoordinates f) p).trans
      (totalDegree_le_of_restrictDegree p m hp)
  have hcard : Nat.card W = Fintype.card K ^ r := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := W)]
  have hcount : (Finset.univ.filter (fun v : Fin r → K => f v ∈ X)).card =
      (inSubspace X W).card := by
    apply Finset.card_bij (fun v _ => f v)
    · intro v hv
      exact (mem_inSubspace _ _ _).mpr ⟨(Finset.mem_filter.mp hv).2, (e v).property⟩
    · intro v hv w hw h
      exact e.injective (Subtype.ext h)
    · intro y hy
      rcases (mem_inSubspace _ _ _).mp hy with ⟨hyX, hyW⟩
      refine ⟨e.symm ⟨y, hyW⟩, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [f] using hyX
      · simp [f]
  have hP : P = 0 := by
    by_contra hne
    have hSZ := card_roots_mul_le P hne
    have hsub : Finset.univ.filter (fun v : Fin r → K => f v ∈ X) ⊆
        Finset.univ.filter (fun v : Fin r → K => MvPolynomial.eval v P = 0) := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change MvPolynomial.eval v (MvPolynomial.aeval (linearCoordinates f) p) = 0
      rw [eval_aeval_linearCoordinates]
      exact hx (f v) (Finset.mem_filter.mp hv).2
    have hle := (Nat.mul_le_mul_right (Fintype.card K) (Finset.card_le_card hsub)).trans
      (hSZ.trans (Nat.mul_le_mul_right _ hPdeg))
    rw [hcount, ← hcard] at hle
    exact (not_lt_of_ge hle) hrich
  intro y hy
  have he : f (e.symm ⟨y, hy⟩) = y := by simp [f]
  have hz := eval_aeval_linearCoordinates f (e.symm ⟨y, hy⟩) p
  rw [he] at hz
  rw [← hz]
  change MvPolynomial.eval _ P = 0
  rw [hP, map_zero]

theorem evalSpace_rank_le_of_rich [Fintype K]
    (X Y : Finset (Fin n → K)) (𝓥 : Set (Submodule K (Fin n → K))) (m : ℕ)
    (hrich : ∀ W ∈ 𝓥, n*m * Nat.card W <
      (inSubspace X W).card * Fintype.card K)
    (hcover : ∀ y ∈ Y, ∃ W ∈ 𝓥, y ∈ W) :
    finrank K (evalSpace Y m) ≤ X.card := by
  classical
  let A := MvPolynomial.restrictDegree (Fin n) K m
  let f := (evalOn X).domRestrict A
  let g := (evalOn Y).domRestrict A
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    ext y
    change MvPolynomial.eval y.1 p.1 = 0
    obtain ⟨W, hW, hy⟩ := hcover y.1 y.property
    apply vanish_on_rich_subspace X W m (hrich W hW) p.1 p.property _ y.1 hy
    intro x hx
    exact congrFun hp ⟨x, hx⟩
  have h := rank_le_of_ker_le f g hker
  have hf : finrank K (LinearMap.range f) ≤ X.card := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  apply (le_trans ?_ hf)
  rw [show evalSpace Y m = LinearMap.range g from
    (LinearMap.range_domRestrict A (evalOn Y)).symm]
  exact h

theorem card_union_le_boxes [Fintype K]
    (X Y : Finset (Fin n → K)) (𝓥 : Set (Submodule K (Fin n → K)))
    (a c : ℕ) (ha : 0 < a) (hqc : Fintype.card K ≤ a*c)
    (hrich : ∀ W ∈ 𝓥, n*(a-1) * Nat.card W <
      (inSubspace X W).card * Fintype.card K)
    (hcover : ∀ y ∈ Y, ∃ W ∈ 𝓥, y ∈ W) :
    Y.card ≤ c^n * X.card :=
  (card_le_boxes_mul_eval_rank Y a c ha hqc).trans
    (Nat.mul_le_mul_left _ (evalSpace_rank_le_of_rich X Y 𝓥 (a-1) hrich hcover))

theorem exists_box_parameters (n q : ℕ) (hn : 0 < n) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ a c : ℕ, 0 < a ∧ q ≤ a*c ∧
      (n*(a-1) : ℕ) ≤ δ*q/4 ∧ (c : ℝ) ≤ 5*n/δ := by
  let a := ⌊δ*q/(4*n)⌋₊ + 1
  let c := ⌊4*n/δ⌋₊ + 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 4*n := by positivity
  have ha : 0 < a := Nat.succ_pos _
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hat : δ*q < (4*n)*(a : ℝ) := by
    have h := Nat.lt_floor_add_one (δ*q/(4*n))
    have h : δ*q/(4*n) < (a : ℝ) := by simpa [a] using h
    nlinarith [(div_lt_iff₀ hden).mp h]
  have hct : 4*(n : ℝ) < δ*c := by
    have h := Nat.lt_floor_add_one (4*n/δ)
    have h : 4*n/δ < (c : ℝ) := by simpa [c] using h
    nlinarith [(div_lt_iff₀ hδ).mp h]
  have hqc : q ≤ a*c := by
    have hmul := mul_lt_mul_of_pos_left hct haR
    have h : (q : ℝ) < (a : ℝ)*(c : ℝ) := by nlinarith
    exact_mod_cast h.le
  have had : (n*(a-1) : ℕ) ≤ δ*q/4 := by
    have h := Nat.floor_le (show 0 ≤ δ*(q : ℝ)/(4*n) by positivity)
    have := (le_div_iff₀ hden).mp h
    simp only [a, Nat.add_sub_cancel, Nat.cast_mul]
    nlinarith
  have hc : (c : ℝ) ≤ 5*n/δ := by
    have h := Nat.floor_le (show 0 ≤ 4*(n : ℝ)/δ by positivity)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [c, Nat.cast_add, Nat.cast_one]
    apply (le_div_iff₀ hδ).mpr
    have := (le_div_iff₀ hδ).mp h
    nlinarith
  exact ⟨a, c, ha, hqc, had, hc⟩

theorem rich_union_vector [Fintype K] (hn : 0 < n)
    (X Y : Finset (Fin n → K)) (𝓥 : Set (Submodule K (Fin n → K)))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hne : ∀ W ∈ 𝓥, W ≠ ⊥)
    (hrich : ∀ W ∈ 𝓥, δ*((Nat.card W : ℝ)-1) ≤ (inSubspace X W).card)
    (hcover : ∀ y ∈ Y, ∃ W ∈ 𝓥, y ∈ W) :
    (Y.card : ℝ) ≤ (5*n/δ)^n * X.card := by
  classical
  obtain ⟨a, c, ha, hqc, hdeg, hc⟩ := exists_box_parameters n (Fintype.card K) hn δ hδ hδ1
  have hrich' : ∀ W ∈ 𝓥, n*(a-1) * Nat.card W <
      (inSubspace X W).card * Fintype.card K := by
    intro W hW
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr (hne W hW)
    have hN : (2 : ℝ) ≤ Nat.card W := by
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast Fintype.one_lt_card (α := W)
    have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
    have hlow := hrich W hW
    have hmul := mul_le_mul_of_nonneg_right hlow hq.le
    have hupper := mul_le_mul_of_nonneg_right hdeg (show (0 : ℝ) ≤ Nat.card W by positivity)
    have hstrict : ((n*(a-1) : ℕ) : ℝ) * Nat.card W <
        ((inSubspace X W).card : ℝ) * Fintype.card K := by
      have hpos : 0 < δ*(Fintype.card K : ℝ) := mul_pos hδ hq
      nlinarith
    exact_mod_cast hstrict
  have h := card_union_le_boxes X Y 𝓥 a c ha hqc hrich' hcover
  have hR : (Y.card : ℝ) ≤ (c : ℝ)^n * X.card := by exact_mod_cast h
  exact hR.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc n) (by positivity))

end Evaluation
end
end RichUnion
end SharpLogRamsey

end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_CardVectorLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
section
namespace SharpLogRamsey.RichUnion
noncomputable section
open Module
section ProjectiveLifts
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}
theorem card_vectorLifts (X : Finset (Projectivization K (Fin n → K))) :
    (vectorLifts X).card = X.card * (Fintype.card K - 1) := by
  classical
  let e₁ := (Projectivization.nonZeroEquivProjectivizationProdUnits K (Fin n → K)).subtypeEquiv
    (p := fun v => Projectivization.mk K v.1 v.2 ∈ X)
    (q := fun z => z.1 ∈ X) (fun _ => Iff.rfl)
  let e₂ : {z : Projectivization K (Fin n → K) × Kˣ // z.1 ∈ X} ≃ X × Kˣ :=
    { toFun := fun z => (⟨z.1.1, z.2⟩, z.1.2)
      invFun := fun z => ⟨(z.1.1, z.2), z.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Fintype.card_congr (e₁.trans e₂)
  simpa [vectorLifts, Fintype.card_units, Fintype.card_subtype] using h

theorem vectorLifts_projectiveIn (X : Finset (Projectivization K (Fin n → K)))
    (W : Submodule K (Fin n → K)) :
    vectorLifts (projectiveIn X W) = inSubspace (vectorLifts X) W := by
  ext v
  simp only [mem_vectorLifts, mem_projectiveIn, Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem, mem_inSubspace]
  exact exists_and_right

theorem card_projectivePoints (W : Submodule K (Fin n → K)) :
    (projectivePoints W).card = Nat.card (Projectivization K W) := by
  classical
  let := Fintype.ofFinite (Projectivization K (Fin n → K))
  rw [Nat.card_congr (projectiveSubmoduleEquiv W), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  rfl

theorem card_projectivePoints_mul (W : Submodule K (Fin n → K)) :
    (projectivePoints W).card * (Fintype.card K - 1) = Nat.card W - 1 := by
  rw [card_projectivePoints, ← Nat.card_eq_fintype_card]
  exact (Projectivization.card K W).symm

theorem rich_union_projective (hn : 0 < n)
    (X : Finset (Projectivization K (Fin n → K)))
    (𝓥 : Set (Submodule K (Fin n → K))) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hne : ∀ W ∈ 𝓥, W ≠ ⊥)
    (hrich : ∀ W ∈ 𝓥, δ*(projectivePoints W).card ≤ (projectiveIn X W).card) :
    ((projectiveUnion 𝓥).card : ℝ) ≤ (5*n/δ)^n * X.card := by
  classical
  have hq : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hqR : (0 : ℝ) < (Fintype.card K - 1 : ℕ) := by exact_mod_cast hq
  have hv : ∀ W ∈ 𝓥, δ*((Nat.card W : ℝ)-1) ≤
      (inSubspace (vectorLifts X) W).card := by
    intro W hW
    rw [← vectorLifts_projectiveIn, card_vectorLifts]
    have hN : 1 ≤ Nat.card W := Nat.card_pos
    have hcard := card_projectivePoints_mul W
    have hcardR : ((projectivePoints W).card : ℝ)*(Fintype.card K-1 : ℕ) =
        (Nat.card W : ℝ)-1 := by
      exact_mod_cast hcard
    rw [Nat.cast_mul, ← hcardR]
    nlinarith [mul_le_mul_of_nonneg_right (hrich W hW) hqR.le]
  have hcover : ∀ y ∈ vectorLifts (projectiveUnion 𝓥), ∃ W ∈ 𝓥, y ∈ W := by
    intro y hy
    obtain ⟨hy0, hY⟩ := (mem_vectorLifts _ _).mp hy
    obtain ⟨W, hW, hyW⟩ := (mem_projectiveUnion _ _).mp hY
    rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem] at hyW
    exact ⟨W, hW, hyW⟩
  have h := rich_union_vector hn (vectorLifts X) (vectorLifts (projectiveUnion 𝓥))
    𝓥 δ hδ hδ1 hne hv hcover
  rw [card_vectorLifts, card_vectorLifts, Nat.cast_mul, Nat.cast_mul] at h
  exact (mul_le_mul_iff_left₀ hqR).mp (by simpa [mul_assoc] using h)

end ProjectiveLifts
end
end SharpLogRamsey.RichUnion
end
section

namespace SharpLogRamsey.HighRankGeometry
open scoped BigOperators
open SharpLogRamsey.RichUnion
noncomputable section
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

lemma sum_powers_le_twice {q : ℝ} (hq : 2 ≤ q) {r : ℕ} (hr : 0 < r) :
    ∑ i ∈ Finset.range r, q^i ≤ 2*q^(r-1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one]
  clear hr
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hqm : 0 ≤ q^m := pow_nonneg (by linarith) _
    have hmul : 2*q^m ≤ q^(m+1) := by rw [pow_succ]; nlinarith
    simp only [Nat.succ_eq_add_one] at ih
    linarith

lemma projective_card_le (W : Submodule K (Fin n → K)) {r : ℕ}
    (hr : 0 < r) (hdim : Module.finrank K W = r) :
    ((projectivePoints W).card : ℝ) ≤ 2*(Fintype.card K : ℝ)^(r-1) := by
  rw [card_projectivePoints, Projectivization.card_of_finrank K W hdim]
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.card_eq_fintype_card]
  exact sum_powers_le_twice (by exact_mod_cast Fintype.one_lt_card (α := K)) hr

lemma subspace_mass_le (mass : Projectivization K (Fin n → K) → ℝ)
    (X : Finset (Projectivization K (Fin n → K)))
    (hsupport : ∀ x, x ∉ X → mass x = 0) (M : ℝ)
    (hcap : ∀ x ∈ X, mass x ≤ M) (W : Submodule K (Fin n → K)) :
    ∑ x ∈ projectivePoints W, mass x ≤ M*(projectiveIn X W).card := by
  classical
  have hsub : projectiveIn X W ⊆ projectivePoints W := by
    intro x hx
    exact (mem_projectivePoints W x).mpr ((mem_projectiveIn _ _ _).mp hx).2
  have he : ∑ x ∈ projectiveIn X W, mass x = ∑ x ∈ projectivePoints W, mass x := by
    apply Finset.sum_subset hsub
    intro x hx hnot
    apply hsupport x
    intro hxX
    exact hnot ((mem_projectiveIn X W x).mpr ⟨hxX, (mem_projectivePoints W x).mp hx⟩)
  rw [← he]
  calc
    _ ≤ ∑ _x ∈ projectiveIn X W, M := Finset.sum_le_sum (fun x hx =>
      hcap x ((mem_projectiveIn _ _ _).mp hx).1)
    _ = _ := by simp [mul_comm]

theorem threshold_rich (mass : Projectivization K (Fin n → K) → ℝ)
    (X : Finset (Projectivization K (Fin n → K)))
    (hsupport : ∀ x, x ∉ X → mass x = 0)
    (A u : ℝ) (hA : 0 < A) (hu : 0 < u)
    (r : ℕ) (hr : 0 < r)
    (hcap : ∀ x ∈ X, mass x ≤ A/(Fintype.card K : ℝ)^r)
    (W : Submodule K (Fin n → K)) (hrank : Module.finrank K W = r)
    (hhit : u ≤ (Fintype.card K : ℝ)*∑ x ∈ projectivePoints W, mass x) :
    (u/(2*A))*((projectivePoints W).card : ℝ) ≤ (projectiveIn X W).card := by
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hp : (0 : ℝ) < (Fintype.card K : ℝ)^(r-1) := pow_pos hq _
  have hr' : r = (r-1)+1 := by omega
  have hm := mul_le_mul_of_nonneg_left (subspace_mass_le mass X hsupport _ hcap W) hq.le
  have hm' : u*(Fintype.card K : ℝ)^(r-1) ≤ A*(projectiveIn X W).card := by
    have hu' := hhit.trans hm
    rw [hr', pow_succ] at hu'
    have he : (Fintype.card K : ℝ)*(A/((Fintype.card K : ℝ)^(r-1)*(Fintype.card K : ℝ))*
        (projectiveIn X W).card) = (A*(projectiveIn X W).card)/(Fintype.card K : ℝ)^(r-1) := by
      have algebra (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
          a*(c/(b*a)*d) = c*d/b := by field_simp
      exact algebra _ _ _ _ (ne_of_gt hq) (ne_of_gt hp)
    rw [he] at hu'
    exact (le_div_iff₀ hp).mp hu'
  have hc := projective_card_le W hr hrank
  apply (mul_le_mul_iff_right₀ (show 0 < 2*A by positivity)).mp
  calc
    (2*A)*((u/(2*A))*((projectivePoints W).card : ℝ)) = u*(projectivePoints W).card := by
      have algebra (a b c : ℝ) (ha : a ≠ 0) : a*(b/a*c) = b*c := by
        rw [← mul_assoc, mul_div_cancel₀ _ ha]
      exact algebra _ _ _ (ne_of_gt (show 0 < 2*A by positivity))
    _ ≤ u*(2*(Fintype.card K : ℝ)^(r-1)) := mul_le_mul_of_nonneg_left hc hu.le
    _ ≤ (2*A)*(projectiveIn X W).card := by nlinarith

theorem high_rank_tail (hn : 0 < n)
    (mass : Projectivization K (Fin n → K) → ℝ)
    (X Y : Finset (Projectivization K (Fin n → K)))
    (hsupport : ∀ x, x ∉ X → mass x = 0)
    (A u : ℝ) (hA : 0 < A) (hu : 0 < u) (huA : u ≤ 2*A)
    (r : ℕ) (hr : 0 < r)
    (hcap : ∀ x ∈ X, mass x ≤ A/(Fintype.card K : ℝ)^r)
    (W : Projectivization K (Fin n → K) → Submodule K (Fin n → K))
    (hrank : ∀ y ∈ Y, Module.finrank K (W y) = r)
    (hy : ∀ y ∈ Y, y.submodule ≤ W y)
    (hhit : ∀ y ∈ Y, u ≤ (Fintype.card K : ℝ)*∑ x ∈ projectivePoints (W y), mass x) :
    (Y.card : ℝ) ≤ (10*(n : ℝ)*A/u)^n*X.card := by
  classical
  let 𝓥 : Set (Submodule K (Fin n → K)) := W '' (Y : Set _)
  have hδ : 0 < u/(2*A) := by positivity
  have hδ1 : u/(2*A) ≤ 1 := (div_le_one (by positivity)).mpr huA
  have hne : ∀ U ∈ 𝓥, U ≠ ⊥ := by
    rintro U ⟨y, hyY, rfl⟩ hz
    have h := hrank y hyY
    rw [hz, finrank_bot] at h
    omega
  have hrich : ∀ U ∈ 𝓥, (u/(2*A))*((projectivePoints U).card : ℝ) ≤
      (projectiveIn X U).card := by
    rintro U ⟨y, hyY, rfl⟩
    exact threshold_rich mass X hsupport A u hA hu r hr hcap (W y) (hrank y hyY) (hhit y hyY)
  have hh := rich_union_projective hn X 𝓥 (u/(2*A)) hδ hδ1 hne hrich
  have hsub : Y ⊆ projectiveUnion 𝓥 := by
    intro y hyY
    exact (mem_projectiveUnion 𝓥 y).mpr ⟨W y, ⟨y, hyY, rfl⟩, hy y hyY⟩
  calc
    _ ≤ ((projectiveUnion 𝓥).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (5*(n : ℝ)/(u/(2*A)))^n*X.card := hh
    _ = _ := by congr 2; field_simp; ring

end
end SharpLogRamsey.HighRankGeometry
end

section

namespace SharpLogRamsey.FiniteSamplingBounds
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

lemma rowTail_le_one (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (E : Finset Ω) (h T : ℕ) : rowTail w E h T ≤ 1 := by
  rw [← rowWeight_total w ht h]
  apply Finset.sum_le_sum
  intro z _
  split_ifs <;> try rfl
  exact rowWeight_nonneg w hw z

lemma rowTail_moment (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ht : ∑ x, w x = 1) (E : Finset Ω) (h T : ℕ) (b : ℝ) (hb : 1 ≤ b) :
    b^T*rowTail w E h T ≤ (1+(b-1)*(∑ x ∈ E, w x))^h := by
  classical
  rw [← rowMoment w ht E h b, rowTail, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  split_ifs with hz
  · rw [mul_comm (b^T)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb hz) (rowWeight_nonneg w hw z)
  · simp only [mul_zero]
    exact mul_nonneg (rowWeight_nonneg w hw z) (pow_nonneg (by linarith) _)

theorem rowTail_small (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ht : ∑ x, w x = 1) (E : Finset Ω) (h T : ℕ)
    (q a : ℝ) (hq : 0 < q) (ha : 0 < a) (ha1 : a ≤ 1/20)
    (hp : ∑ x ∈ E, w x ≤ a/q) (hT : (h : ℝ)/(10*q) ≤ T) :
    rowTail w E h T ≤ (20*Real.exp (1/2)*a)^T := by
  let b : ℝ := 1/(20*a)
  have hb : 1 ≤ b := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hb0 : 0 < b := by linarith
  have hp0 : 0 ≤ ∑ x ∈ E, w x := Finset.sum_nonneg (fun x _ => hw x)
  have hv0 : 0 ≤ (b-1)*(∑ x ∈ E, w x) := mul_nonneg (by linarith) hp0
  have hM := rowTail_moment w hw ht E h T b hb
  have hExp : (1+(b-1)*(∑ x ∈ E, w x))^h ≤
      Real.exp ((h : ℝ)*((b-1)*(∑ x ∈ E, w x))) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (show 0 ≤ 1+(b-1)*(∑ x ∈ E, w x) by linarith)
    simpa only [add_comm] using Real.add_one_le_exp ((b-1)*(∑ x ∈ E, w x))
  have he : (h : ℝ)*((b-1)*(∑ x ∈ E, w x)) ≤ (T : ℝ)/2 := by
    have h1 : (b-1)*(∑ x ∈ E, w x) ≤ b*(a/q) := by
      exact mul_le_mul (by linarith) hp hp0 hb0.le
    have h2 : b*(a/q) = 1/(20*q) := by dsimp [b]; field_simp
    rw [h2] at h1
    have hh := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg h)
    have ht' : (h : ℝ)/(20*q) ≤ (T : ℝ)/2 := by
      have heq : (h : ℝ)/(20*q) = ((h : ℝ)/(10*q))/2 := by ring
      rw [heq]
      exact div_le_div_of_nonneg_right hT (by norm_num)
    have hh' : (h : ℝ)*((b-1)*(∑ x ∈ E, w x)) ≤ (h : ℝ)/(20*q) := by
      simpa only [mul_one_div] using hh
    exact hh'.trans ht'
  have hM' : b^T*rowTail w E h T ≤ Real.exp ((T : ℝ)/2) :=
    hM.trans (hExp.trans (Real.exp_le_exp.mpr he))
  have hdiv : rowTail w E h T ≤ Real.exp ((T : ℝ)/2)/b^T :=
    (le_div_iff₀ (pow_pos hb0 T)).mpr (by simpa only [mul_comm] using hM')
  convert hdiv using 1
  all_goals try with_reducible_and_instances rfl
  have hexp : Real.exp ((T : ℝ)/2) = (Real.exp (1/2))^T := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp, ← div_pow]
  congr 1
  dsimp [b]
  field_simp

lemma rowTail_zero (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (E : Finset Ω)
    (h T : ℕ) (hT : 0 < T) (hp : ∑ x ∈ E, w x = 0) :
    rowTail w E h T = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z _
  split_ifs with hz
  · have hc : 0 < (univ.filter (fun i => z i ∈ E)).card := by
      change 0 < hitCount E z
      omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hc
    have hxi : z i ∈ E := (mem_filter.mp hi).2
    have hwi : w (z i) = 0 := by
      apply le_antisymm _ (hw _)
      rw [← hp]
      exact Finset.single_le_sum (fun x _ => hw x) hxi
    exact Finset.prod_eq_zero (mem_univ i) hwi
  · rfl

end
end SharpLogRamsey.FiniteSamplingBounds
end

section

namespace SharpLogRamsey.DyadicTail
open scoped BigOperators
open Finset Classical
noncomputable section

lemma exists_band {a u : ℝ} (ha : 0 < a) (hu : 0 < u) (hau : a ≤ u) :
    ∃ j : ℕ, u*(1/2 : ℝ)^(j+1) < a ∧ a ≤ u*(1/2 : ℝ)^j := by
  have hex : ∃ j : ℕ, u*(1/2 : ℝ)^j < a := by
    obtain ⟨j,hj⟩ := exists_pow_lt_of_lt_one (div_pos ha hu) (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨j,(by simpa only [mul_comm] using (lt_div_iff₀ hu).mp hj)⟩
  have hn : Nat.find hex ≠ 0 := by
    intro hz
    have hh := Nat.find_spec hex
    rw [hz, pow_zero, mul_one] at hh
    exact (not_lt_of_ge hau) hh
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨j, ?_, ?_⟩
  · simpa only [hj, Nat.succ_eq_add_one] using Nat.find_spec hex
  · exact le_of_not_gt (fun h => by have hh := Nat.find_min' hex h; omega)

lemma finite_geometric (J : Finset ℕ) : ∑ j ∈ J, (1/2 : ℝ)^j ≤ 2 := by
  have hs : Summable (fun j : ℕ => (1/2 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hh := hs.sum_le_tsum J (fun j _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) j)
  simpa only [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1), show (1-(1/2 : ℝ))⁻¹ = 2 by norm_num] using hh

variable {Y : Type*} [Fintype Y]

theorem small_tail_sum (a w : Y → ℝ) (u C M : ℝ) (n T : ℕ)
    (hu : 0 < u) (hC : 0 ≤ C) (hM : 0 ≤ M) (hCu : C*u ≤ 1)
    (ha : ∀ x, 0 < a x ∧ a x ≤ u) (hw : ∀ x, w x ≤ (C*a x)^T)
    (hT : n+1 ≤ T)
    (htail : ∀ v, 0 < v → v ≤ u →
      ((univ.filter (fun x : Y => v ≤ a x)).card : ℝ) ≤ M*(u/v)^n) :
    ∑ x, w x ≤ M*2^(n+1) := by
  classical
  choose level hlower hupper using fun x => exists_band (ha x).1 hu (ha x).2
  let J : Finset ℕ := univ.image level
  have hband (j : ℕ) :
      ∑ x ∈ univ.filter (fun x : Y => level x = j), w x ≤ M*2^n*(1/2 : ℝ)^j := by
    let δ : ℝ := (1/2 : ℝ)^j
    have hδ : 0 < δ := pow_pos (by norm_num) _
    have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hv : 0 < u*δ/2 := by positivity
    have hvu : u*δ/2 ≤ u := by nlinarith
    have hcnt := htail (u*δ/2) hv hvu
    have hsub : univ.filter (fun x : Y => level x = j) ⊆
        univ.filter (fun x : Y => u*δ/2 ≤ a x) := by
      intro x hx
      have hh := hlower x
      rw [(mem_filter.mp hx).2, pow_succ] at hh
      exact mem_filter.mpr ⟨mem_univ _, by dsimp [δ]; linarith⟩
    have hc' : ((univ.filter (fun x : Y => level x = j)).card : ℝ) ≤
        ((univ.filter (fun x : Y => u*δ/2 ≤ a x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hc := hc'.trans hcnt
    have hweight : ∀ x ∈ univ.filter (fun x : Y => level x = j), w x ≤ δ^(n+1) := by
      intro x hx
      have ha' : a x ≤ u*δ := by simpa only [(mem_filter.mp hx).2] using hupper x
      have hca : C*a x ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left ha' hC]
      exact (hw x).trans ((pow_le_pow_left₀ (mul_nonneg hC (ha x).1.le) hca T).trans
        (pow_le_pow_of_le_one hδ.le hδ1 hT))
    calc
      _ ≤ ∑ _x ∈ univ.filter (fun x : Y => level x = j), δ^(n+1) :=
        Finset.sum_le_sum hweight
      _ = ((univ.filter (fun x : Y => level x = j)).card : ℝ)*δ^(n+1) := by simp
      _ ≤ (M*(u/(u*δ/2))^n)*δ^(n+1) := mul_le_mul_of_nonneg_right hc (pow_nonneg hδ.le _)
      _ = M*2^n*δ := by
        have he : u/(u*δ/2) = 2/δ := by field_simp
        rw [he, div_pow, pow_succ]
        field_simp
      _ = _ := rfl
  have hsum : ∑ x, w x = ∑ j ∈ J, ∑ x ∈ univ.filter (fun x : Y => level x = j), w x := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x _ => mem_image.mpr ⟨x, mem_univ _, rfl⟩) w
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ J, M*2^n*(1/2 : ℝ)^j := Finset.sum_le_sum (fun j _ => hband j)
    _ = M*2^n*(∑ j ∈ J, (1/2 : ℝ)^j) := by rw [Finset.mul_sum]
    _ ≤ M*2^n*2 := mul_le_mul_of_nonneg_left (finite_geometric J) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end
end SharpLogRamsey.DyadicTail
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TailSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
section
namespace SharpLogRamsey.DyadicTail
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Y : Type*} [Fintype Y]
theorem tail_sum (a w : Y → ℝ) (u C M : ℝ) (n T : ℕ)
    (hu : 0 < u) (hC : 0 ≤ C) (hM : 0 ≤ M) (hCu : C*u ≤ 1)
    (ha : ∀ x, 0 ≤ a x) (hw1 : ∀ x, w x ≤ 1)
    (hzero : ∀ x, a x = 0 → w x = 0)
    (hw : ∀ x, 0 < a x → a x ≤ u → w x ≤ (C*a x)^T)
    (hT : n+1 ≤ T)
    (htail : ∀ v, 0 < v → v ≤ u →
      ((univ.filter (fun x : Y => v ≤ a x)).card : ℝ) ≤ M*(u/v)^n) :
    ∑ x, w x ≤ M*(1+2^(n+1)) := by
  classical
  let H : Finset Y := univ.filter (fun x => u ≤ a x)
  let L : Finset Y := univ.filter (fun x => 0 < a x ∧ a x < u)
  have hH : ∑ x ∈ H, w x ≤ M := by
    calc
      _ ≤ ∑ _x ∈ H, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hw1 x)
      _ = (H.card : ℝ) := by simp
      _ ≤ M := by simpa [H, ne_of_gt hu] using htail u hu le_rfl
  have htailL : ∀ v, 0 < v → v ≤ u →
      ((univ.filter (fun x : L => v ≤ a x)).card : ℝ) ≤ M*(u/v)^n := by
    intro v hv hvu
    have hc : (univ.filter (fun x : L => v ≤ a x)).card ≤
        (univ.filter (fun x : Y => v ≤ a x)).card := by
      apply Finset.card_le_card_of_injOn (fun x : L => x.val)
      · intro x hx
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
      · intro x _ y _ hh
        exact Subtype.ext hh
    exact (by exact_mod_cast hc :
      ((univ.filter (fun x : L => v ≤ a x)).card : ℝ) ≤
        ((univ.filter (fun x : Y => v ≤ a x)).card : ℝ)).trans (htail v hv hvu)
  have hL : ∑ x ∈ L, w x ≤ M*2^(n+1) := by
    have hh := small_tail_sum (fun x : L => a x) (fun x : L => w x) u C M n T
      hu hC hM hCu (fun x => ⟨(mem_filter.mp x.2).2.1, (mem_filter.mp x.2).2.2.le⟩)
      (fun x => hw x (mem_filter.mp x.2).2.1 (mem_filter.mp x.2).2.2.le) hT htailL
    simpa only [Finset.sum_coe_sort] using hh
  have he : ∑ x, w x = (∑ x ∈ H, w x)+(∑ x ∈ L, w x) := by
    dsimp [H,L]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hh : u ≤ a x
    · simp [hh, not_lt_of_ge hh]
    · have hxu : a x < u := lt_of_not_ge hh
      by_cases hz : a x = 0
      · simp [hz, hzero x hz]
      · have hx0 : 0 < a x := lt_of_le_of_ne (ha x) (Ne.symm hz)
        simp [hh, hx0, hxu]
  rw [he]
  nlinarith

end
end SharpLogRamsey.DyadicTail
end

section

namespace SharpLogRamsey.HighRankSampling
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.RichUnion SharpLogRamsey.HighRankGeometry
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

attribute [local instance] OAI.SharpLogRamsey.HighRankSampling.flat_JoinedHighRankAssembly_1
theorem high_rank_expected (hn : 0 < n)
    (mass : Projectivization K (Fin n → K) → ℝ)
    (hmass : ∀ x, 0 ≤ mass x) (htotal : ∑ x, mass x = 1)
    (X Y : Finset (Projectivization K (Fin n → K)))
    (hsupport : ∀ x, x ∉ X → mass x = 0)
    (A u : ℝ) (hA : 0 < A) (hu : 0 < u) (huA : u ≤ 2*A)
    (hu20 : u ≤ 1/20) (hCu : 20*Real.exp (1/2)*u ≤ 1)
    (r : ℕ) (hr : 0 < r)
    (hcap : ∀ x ∈ X, mass x ≤ A/(Fintype.card K : ℝ)^r)
    (W : Projectivization K (Fin n → K) → Submodule K (Fin n → K))
    (hrank : ∀ y ∈ Y, Module.finrank K (W y) = r)
    (hy : ∀ y ∈ Y, y.submodule ≤ W y)
    (h T : ℕ) (hT : (h : ℝ)/(10*(Fintype.card K : ℝ)) ≤ T) (hTn : n+1 ≤ T) :
    (∑ y ∈ Y, rowTail mass (projectivePoints (W y)) h T) ≤
      (10*(n : ℝ)*A/u)^n*X.card*(1+2^(n+1)) := by
  classical
  let q : ℝ := Fintype.card K
  let a (y : Y) : ℝ := q * ∑ x ∈ projectivePoints (W y), mass x
  let w (y : Y) : ℝ := rowTail mass (projectivePoints (W y)) h T
  let M : ℝ := (10*(n : ℝ)*A/u)^n*X.card
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ha : ∀ y, 0 ≤ a y := fun y =>
    mul_nonneg hq.le (Finset.sum_nonneg (fun x _ => hmass x))
  have hzero : ∀ y, a y = 0 → w y = 0 := by
    intro y hay
    apply rowTail_zero mass hmass _ h T (by omega)
    exact (mul_eq_zero.mp hay).resolve_left (ne_of_gt hq)
  have hw : ∀ y, 0 < a y → a y ≤ u → w y ≤ (20*Real.exp (1/2)*a y)^T := by
    intro y hay hayu
    apply rowTail_small mass hmass htotal _ h T q (a y) hq hay (hayu.trans hu20) _ hT
    dsimp [a]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hq)]
  have htail : ∀ v, 0 < v → v ≤ u →
      ((univ.filter (fun y : Y => v ≤ a y)).card : ℝ) ≤ M*(u/v)^n := by
    intro v hv hvu
    let Z := Y.filter (fun y => v ≤ q * ∑ x ∈ projectivePoints (W y), mass x)
    have hc : (univ.filter (fun y : Y => v ≤ a y)).card = Z.card := by
      apply Finset.card_bij (fun y _ => y.val)
      · intro y hyy
        exact mem_filter.mpr ⟨y.2, (mem_filter.mp hyy).2⟩
      · intro y _ z _ hzz
        exact Subtype.ext hzz
      · intro y hyy
        exact ⟨⟨y,(mem_filter.mp hyy).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hyy).2⟩,rfl⟩
    rw [hc]
    have hb := high_rank_tail hn mass X Z hsupport A v hA hv (hvu.trans huA) r hr hcap W
      (fun y hyy => hrank y (mem_filter.mp hyy).1)
      (fun y hyy => hy y (mem_filter.mp hyy).1)
      (fun y hyy => (mem_filter.mp hyy).2)
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [M]
    rw [mul_right_comm _ (X.card : ℝ), ← mul_pow]
    congr 2
    field_simp
  have H := DyadicTail.tail_sum a w u (20*Real.exp (1/2)) M n T hu (by positivity)
    hM hCu ha (fun y => rowTail_le_one mass hmass htotal _ h T) hzero hw hTn htail
  change (∑ y : Y, rowTail mass (projectivePoints (W y)) h T) ≤ _ at H
  rw [Finset.sum_coe_sort Y (fun y => rowTail mass (projectivePoints (W y)) h T)] at H
  exact H

lemma mean_admitted_eq
    (mass : Projectivization K (Fin n → K) → ℝ)
    (Y : Finset (Projectivization K (Fin n → K)))
    (W : Projectivization K (Fin n → K) → Submodule K (Fin n → K)) (h T : ℕ) :
    (∑ z : Fin h → Projectivization K (Fin n → K),
      rowWeight mass z * ((Y.filter (fun y => T ≤ hitCount (projectivePoints (W y)) z)).card : ℝ)) =
      ∑ y ∈ Y, rowTail mass (projectivePoints (W y)) h T := by
  classical
  simp_rw [← Finset.sum_boole, Finset.mul_sum, rowTail]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

end
end SharpLogRamsey.HighRankSampling
end

namespace SharpLogRamsey.HighRankDecoder
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma center_le {h : ℕ} (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Fin h → Ω) : y.submodule ≤ hitSpan a b y z := le_sup_left

lemma hit_le {h : ℕ} (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Fin h → Ω) (i : Fin h) (hi : a (z i) y.rep = 0) :
    (b (z i)).submodule ≤ hitSpan a b y z := by
  apply le_trans _ le_sup_right
  have H := le_iSup (fun j => if a (z j) y.rep = 0 then (b (z j)).submodule else ⊥) i
  rwa [ite_eq_left hi] at H

lemma line_le_ker (b : Projectivization K V) (c : Module.Dual K V) :
    b.submodule ≤ LinearMap.ker c ↔ c b.rep = 0 := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
  rfl

lemma annihilates_hitSpan {h : ℕ} (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Fin h → Ω) (c : Module.Dual K V)
    (hcy : c y.rep = 0)
    (hconflict : ∀ i, a (z i) y.rep = 0 → c (b (z i)).rep = 0) :
    hitSpan a b y z ≤ LinearMap.ker c := by
  apply sup_le ((line_le_ker y c).mpr hcy)
  apply iSup_le
  intro i
  split_ifs with hi
  · exact (line_le_ker _ c).mpr (hconflict i hi)
  · exact bot_le

theorem coverage [FiniteDimensional K V] {h : ℕ}
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (z₁ z₂ : Fin h → Ω) (r T : ℕ)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V))
    (hcy : c.rep y.rep = 0)
    (hconflict₁ : ∀ i, a (z₁ i) y.rep = 0 → c.rep (b (z₁ i)).rep = 0)
    (hconflict₂ : ∀ i, a (z₂ i) y.rep = 0 → c.rep (b (z₂ i)).rep = 0)
    (hreach : r ≤ Module.finrank K (hitSpan a b y z₁))
    (hexcess : ¬ (r < Module.finrank K (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ∧
      hitSpan a b y z₁ ⊔ hitSpan a b y z₂ ≤ LinearMap.ker c.rep))
    (hhits : T ≤ (univ.filter (fun i => a (z₂ i) y.rep = 0)).card) :
    Admitted a b z₁ z₂ r T y c := by
  have ha₁ := annihilates_hitSpan a b y z₁ c.rep hcy hconflict₁
  have ha₂ := annihilates_hitSpan a b y z₂ c.rep hcy hconflict₂
  have hcombined : Module.finrank K (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ≤ r := by
    by_contra hn
    exact hexcess ⟨Nat.lt_of_not_ge hn, sup_le ha₁ ha₂⟩
  have hle := Submodule.finrank_mono
    (show hitSpan a b y z₁ ≤ hitSpan a b y z₁ ⊔ hitSpan a b y z₂ from le_sup_left)
  have hrank : Module.finrank K (hitSpan a b y z₁) = r := by omega
  have heq : hitSpan a b y z₁ = hitSpan a b y z₁ ⊔ hitSpan a b y z₂ := by
    apply Submodule.eq_of_le_of_finrank_eq le_sup_left
    omega
  refine ⟨hrank, ha₁, hhits.trans (card_le_card ?_)⟩
  intro i hi
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  rw [heq]
  exact (hit_le a b y z₂ i (mem_filter.mp hi).2).trans le_sup_right

end
end SharpLogRamsey.HighRankDecoder

namespace SharpLogRamsey.HighRankExcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card (W : Submodule K V) :
    (univ.filter (fun b : Projectivization K V => b.submodule ≤ W)).card =
      ∑ i ∈ range (Module.finrank K W), Nat.card K^i := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K] in
lemma geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

omit [Fintype (Projectivization K (Module.Dual K V))] [FiniteDimensional K V] in
lemma small_span_card (r : ℕ) (hr : 1 ≤ r) (W : Submodule K V)
    (hW : Module.finrank K W ≤ r) :
    ((univ.filter (fun b : Projectivization K V => b.submodule ≤ W)).card : ℝ) ≤
      2*(Nat.card K:ℝ)^(r-1) := by
  rw [projective_card, Nat.cast_sum]
  push_cast
  calc
    _ ≤ ∑ i ∈ range ((r-1)+1), (Nat.card K:ℝ)^i := by
      apply sum_le_sum_of_subset_of_nonneg
      · apply range_mono
        omega
      · intro _ _ _; positivity
    _ ≤ _ := geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)) _

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma partners_eq (W : Submodule K V) :
    partners W = univ.filter (fun a => a.submodule ≤ W.dualAnnihilator) := by
  ext a
  simp only [partners, mem_filter, mem_univ, true_and,
    Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  rfl

omit [Fintype (Projectivization K V)] in
lemma excess_partners_card {d r : ℕ} (hdim : Module.finrank K V = d+1)
    (hr : r < d) (W : Submodule K V) (hW : r < Module.finrank K W) :
    ((partners W).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-r-1) := by
  rw [partners_eq]
  apply small_span_card (d-r) (by omega)
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

omit [Finite K] [Fintype (Projectivization K V)] in
lemma full_rank_no_partners {d : ℕ} (hdim : Module.finrank K V = d+1)
    (W : Submodule K V) (hW : d < Module.finrank K W) : partners W = ∅ := by
  have htop : W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hm := Submodule.finrank_le W
    omega
  subst W
  apply filter_eq_empty_iff.mpr
  intro a _ ha
  exact a.rep_nonzero (LinearMap.ker_eq_top.mp (top_unique ha))

omit [Fintype (Projectivization K V)] in
lemma excessCarrier_card {d r : ℕ} (hdim : Module.finrank K V = d+1) (hr : r < d)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V) :
    ((excessCarrier U W r).card:ℝ) ≤ U.card*(2*(Nat.card K:ℝ)^(d-r-1)) := by
  have he : excessCarrier U W r =
      U.biUnion (fun y => if r < Module.finrank K (W y) then
        (partners (W y)).image (Prod.mk y) else ∅) := by
    ext z
    simp only [excessCarrier, mem_filter, mem_product, mem_univ, and_true, mem_biUnion]
    constructor
    · rintro ⟨hy, hr, hc⟩
      refine ⟨z.1, hy, ?_⟩
      rw [ite_eq_left hr]
      apply mem_image.mpr
      exact ⟨z.2, mem_filter.mpr ⟨mem_univ _, hc⟩, Prod.eta z⟩
    · rintro ⟨y, hy, hz⟩
      split_ifs at hz with hr
      · obtain ⟨c, hc, rfl⟩ := mem_image.mp hz
        exact ⟨hy, hr, (mem_filter.mp hc).2⟩
      · simp at hz
  rw [he]
  calc
    _ ≤ ∑ y ∈ U, ((if r < Module.finrank K (W y) then
        (partners (W y)).image (Prod.mk y) else ∅).card:ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ _y ∈ U, 2*(Nat.card K:ℝ)^(d-r-1) := by
      apply sum_le_sum
      intro y _
      split_ifs with hW
      · rw [card_image_of_injective _ (by intro a b h; exact Prod.mk.inj h |>.2)]
        exact excess_partners_card hdim hr (W y) hW
      · simp
    _ = _ := by simp

omit [Fintype (Projectivization K V)] in
theorem target_excess_mass {d r : ℕ} (hdim : Module.finrank K V = d+1) (hr : r < d)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (M : ℝ) (hM : 0 ≤ M) :
    (∑ z ∈ excessCarrier U W r, p z) ≤
      (∑ z ∈ U ×ˢ univ, if M < p z then p z else 0) +
        U.card*(2*(Nat.card K:ℝ)^(d-r-1))*M := by
  have hsplit : (∑ z ∈ excessCarrier U W r, p z) ≤
      (∑ z ∈ excessCarrier U W r, if M < p z then p z else 0) +
        (excessCarrier U W r).card * M := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
    apply sum_le_sum
    intro z _
    split_ifs with hz
    · linarith
    · simpa only [zero_add] using le_of_not_gt hz
  have hlarge : (∑ z ∈ excessCarrier U W r, if M < p z then p z else 0) ≤
      ∑ z ∈ U ×ˢ univ, if M < p z then p z else 0 := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro z _ _
    split_ifs <;> first | exact hp z | rfl
  have hc := mul_le_mul_of_nonneg_right (excessCarrier_card hdim hr U W) hM
  linarith

omit [Finite K] [Fintype (Projectivization K V)] in
lemma excessCarrier_full_rank {d : ℕ} (hdim : Module.finrank K V = d+1)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V) :
    excessCarrier U W d = ∅ := by
  apply filter_eq_empty_iff.mpr
  intro z _ hz
  have hm : z.2 ∈ partners (W z.1) := mem_filter.mpr ⟨mem_univ _, hz.2⟩
  rw [full_rank_no_partners hdim (W z.1) hz.1] at hm
  simp at hm

end
end SharpLogRamsey.HighRankExcess
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TargetEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankExcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma target_event_eq (U : Finset (Projectivization K V))
    (W : Projectivization K V → Submodule K V) (r : ℕ)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hsupp : ∀ z, p z≠0 → z.1 ∈ U) :
    (∑ z, p z*(if r < Module.finrank K (W z.1) ∧ W z.1 ≤ LinearMap.ker z.2.rep
      then 1 else 0)) = ∑ z ∈ excessCarrier U W r, p z := by
  let E (z : Projectivization K V × Projectivization K (Module.Dual K V)) :=
    r < Module.finrank K (W z.1) ∧ W z.1 ≤ LinearMap.ker z.2.rep
  have he (z : Projectivization K V × Projectivization K (Module.Dual K V)) :
      p z*(if E z then 1 else 0) =
      if z ∈ U ×ˢ univ then (if E z then p z else 0) else 0 := by
    by_cases hpz : p z=0
    · simp [hpz]
    · simp [hsupp z hpz, mul_ite]
  change (∑ z, p z*(if E z then 1 else 0)) = _
  simp_rw [he]
  rw [excessCarrier, sum_filter]
  rw [← sum_filter]
  simp only [filter_mem_eq_inter, univ_inter]
  rfl

omit [Fintype (Projectivization K V)] in
lemma target_excess_mass_sharp {d r : ℕ} (hdim : Module.finrank K V = d+1) (hr : r ≤ d)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (M : ℝ) (hM : 0 ≤ M) :
    (∑ z ∈ excessCarrier U W r, p z) ≤
      (∑ z ∈ U ×ˢ univ, if M < p z then p z else 0) +
        (if r<d then U.card*(2*(Nat.card K:ℝ)^(d-r-1))*M else 0) := by
  obtain hrd | rfl := hr.lt_or_eq
  · rw [ite_eq_left hrd]
    exact target_excess_mass hdim hrd U W p hp M hM
  · rw [ite_eq_right (lt_irrefl _), add_zero, excessCarrier_full_rank hdim, sum_empty]
    apply sum_nonneg
    intro z _
    split_ifs <;> first | exact hp _ | rfl

end
end SharpLogRamsey.HighRankExcess

namespace SharpLogRamsey.ProductLaw
open scoped BigOperators
open Finset Classical
noncomputable section
variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [Fintype Ω]

omit [Fintype κ] in
lemma total (w : Ω → ℝ) (ht : ∑ x, w x = 1) : ∑ z : ι → Ω, weight w z = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [ht]

omit [Fintype κ] [Fintype Ω] in
lemma nonneg (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (z : ι → Ω) : 0 ≤ weight w z :=
  prod_nonneg (fun i _ => hw (z i))

lemma reindex (w : Ω → ℝ) (e : ι ≃ κ) (f : (κ → Ω) → ℝ) :
    (∑ z : ι → Ω, weight w z*f (z ∘ e.symm)) = ∑ z : κ → Ω, weight w z*f z := by
  let E : (κ → Ω) ≃ (ι → Ω) := Equiv.arrowCongr e.symm (Equiv.refl Ω)
  rw [← E.sum_comp]
  apply sum_congr rfl
  intro z _
  have hfun : E z ∘ e.symm = z := by funext i; simp [E]
  rw [hfun]
  congr 1
  unfold weight
  simpa [E] using e.prod_comp (fun i => w (z i))

omit [Fintype κ] in
lemma restriction (w : Ω → ℝ) (ht : ∑ x, w x = 1)
    (P : ι → Prop) (f : ({i // P i} → Ω) → ℝ) :
    (∑ z : ι → Ω, weight w z*f (fun i => z i)) =
      ∑ z : {i // P i} → Ω, weight w z*f z := by
  let E := Equiv.piEquivPiSubtypeProd P (fun _ : ι => Ω)
  rw [← E.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hsplit (z : {i // P i} → Ω) (z' : {i // ¬P i} → Ω) :
      weight w (E.symm (z,z')) = weight w z*weight w z' := by
    unfold weight
    rw [← Fintype.prod_subtype_mul_prod_subtype P]
    congr 1
    · apply prod_congr rfl
      intro i _
      simp [E, i.property]
    · apply prod_congr rfl
      intro i _
      simp [E, i.property]
  have hres (z : {i // P i} → Ω) (z' : {i // ¬P i} → Ω) :
      (fun i : {i // P i} => E.symm (z,z') i) = z := by
    funext i
    simp [E, i.property]
  simp_rw [hsplit, hres]
  apply sum_congr rfl
  intro z _
  calc
    _ = weight w z*f z*(∑ z' : {i // ¬P i} → Ω, weight w z') := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z' _
      ring
    _ = _ := by
      have hz : (∑ z' : {i // ¬P i} → Ω, weight w z') = 1 := by
        unfold weight
        rw [← Fintype.prod_sum]
        simp [ht]
      rw [hz, mul_one]

lemma marginal (w : Ω → ℝ) (ht : ∑ x, w x = 1) (e : κ ↪ ι)
    (f : (κ → Ω) → ℝ) :
    (∑ z : ι → Ω, weight w z*f (z ∘ e)) = ∑ z : κ → Ω, weight w z*f z := by
  let E : κ ≃ {i // i ∈ Set.range e} := Equiv.ofInjective e e.injective
  have h := restriction w ht (fun i => i ∈ Set.range e)
    (fun z => f (z ∘ E))
  change (∑ z : ι → Ω, weight w z*f (z ∘ e)) = _ at h
  rw [h]
  convert reindex w E.symm f using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Equiv.symm_symm]
  congr!

omit [Fintype κ] in
lemma coordinate_mean (w : Ω → ℝ) (ht : ∑ x, w x = 1)
    (i : ι) (f : Ω → ℝ) :
    (∑ z : ι → Ω, weight w z*f (z i)) = ∑ x, w x*f x := by
  have hi (z : ι → Ω) : weight w z*f (z i) =
      ∏ j, w (z j)*(if j=i then f (z j) else 1) := by
    rw [prod_mul_distrib]
    simp [weight]
  simp_rw [hi]
  rw [← Fintype.prod_sum (fun j x => w x*(if j=i then f x else 1))]
  have he (j : ι) : (∑ x, w x*(if j=i then f x else 1)) =
      if j=i then ∑ x, w x*f x else 1 := by
    split_ifs <;> simp_all
  simp_rw [he]
  simp

omit [Fintype κ] in

lemma row_exists_le (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ht : ∑ x, w x = 1) (E : Ω → Prop) :
    (∑ z : ι → Ω, weight w z*(if ∃ i, E (z i) then 1 else 0)) ≤
      (Fintype.card ι:ℝ)*(∑ x, w x*(if E x then 1 else 0)) := by
  calc
    _ ≤ ∑ z : ι → Ω, weight w z*(∑ i : ι, if E (z i) then 1 else 0) := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (nonneg w hw z)
      split_ifs with h
      · obtain ⟨i,hi⟩ := h
        have H := single_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
          show (0:ℝ) ≤ if E (z j) then 1 else 0 by split_ifs <;> norm_num) (mem_univ i)
        simpa only [ite_eq_left hi] using H
      · apply sum_nonneg
        intro i _
        split_ifs <;> norm_num
    _ = ∑ i : ι, ∑ z : ι → Ω, weight w z*(if E (z i) then 1 else 0) := by
      simp_rw [mul_sum]
      exact sum_comm
    _ = ∑ _i : ι, (∑ x, w x*(if E x then 1 else 0)) := by
      apply sum_congr rfl
      intro i _
      exact coordinate_mean w ht i (fun x => if E x then 1 else 0)
    _ = _ := by simp

end
end SharpLogRamsey.ProductLaw

namespace SharpLogRamsey.FiniteMarginals
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]

omit [Fintype ι] in
lemma sum_marginal (w : Ω → ℝ) (f : Ω → Y) (g : Y → ℝ) :
    (∑ y, marginal w f y*g y) = ∑ z, w z*g (f z) := by
  unfold marginal
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  simp

omit [Fintype ι] in
lemma marginal_total (w : Ω → ℝ) (f : Ω → Y) : ∑ y, marginal w f y=∑ z, w z := by
  simpa using sum_marginal w f (fun _ => 1)

omit [Fintype Y] [Fintype ι] in
lemma marginal_nonneg (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (f : Ω → Y) (y : Y) :
    0 ≤ marginal w f y := by
  apply sum_nonneg
  intro z _
  split_ifs
  · exact hw z
  · exact le_rfl

omit [Fintype Y] in
lemma row_mass (w : Ω → ℝ) (f : Ω → Y) (u : ι → Y) :
    ProductLaw.weight (marginal w f) u =
      ∑ z : ι → Ω, ProductLaw.weight w z*(if (fun i => f (z i))=u then 1 else 0) := by
  unfold ProductLaw.weight marginal
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro z _
  by_cases he : (fun i => f (z i))=u
  · have hp : ∀ i, f (z i)=u i := congrFun he
    simp [hp]
  · rw [ite_eq_right he, mul_zero]
    obtain ⟨i, hi⟩ : ∃ i, f (z i)≠u i := by
      by_contra hh
      push Not at hh
      exact he (funext hh)
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

lemma row_pushforward (w : Ω → ℝ) (f : Ω → Y) (F : (ι → Y) → ℝ) :
    (∑ z : ι → Ω, ProductLaw.weight w z*F (fun i => f (z i))) =
      ∑ u : ι → Y, ProductLaw.weight (marginal w f) u*F u := by
  simp_rw [row_mass, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  simp

end
end SharpLogRamsey.FiniteMarginals

namespace SharpLogRamsey.HighRankSize
open scoped BigOperators
open Finset Classical HighRankDecoder RichUnion FiniteMarginals
noncomputable section
variable {K Ω : Type*} [Field K] [Fintype K] [Fintype Ω] {n : ℕ}

attribute [local instance] OAI.SharpLogRamsey.HighRankSize.flat_JoinedHighRankAssembly_2
attribute [local instance] OAI.SharpLogRamsey.HighRankSize.flat_JoinedHighRankAssembly_4
omit [Fintype Ω] in
lemma partner_bound {r : ℕ} (hr : r<n) (W : Submodule K (Fin n → K))
    (hW : Module.finrank K W=r) :
    ((HighRankExcess.partners W).card:ℝ) ≤ 2*(Fintype.card K:ℝ)^(n-r-1) := by
  rw [HighRankExcess.partners_eq, ← (Nat.card_eq_fintype_card (α := K))]
  apply HighRankExcess.small_span_card (n-r) (by omega)
  have H := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at H
  omega

omit [Fintype Ω] in
lemma domain_card {h r : ℕ} (hr : r<n) (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ z₂ : Fin h → Ω) (T : ℕ) :
    ((domain a b z₁ z₂ r T).card:ℝ) ≤
      ((points a b z₁ z₂ r T).card:ℝ)*(2*(Fintype.card K:ℝ)^(n-r-1)) := by
  have he : domain a b z₁ z₂ r T =
      (points a b z₁ z₂ r T).biUnion (fun y =>
        (HighRankExcess.partners (hitSpan a b y z₁)).image (Prod.mk y)) := by
    ext t
    simp only [domain, points, rankPoints, HighRankExcess.partners]
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_image]
    change (Admitted a b z₁ z₂ r T t.1 t.2) ↔ _
    unfold Admitted
    constructor
    · rintro ⟨hR,hC,hT⟩
      exact ⟨t.1,⟨hR,hT⟩,t.2,hC,rfl⟩
    · rintro ⟨y,⟨hR,hT⟩,c,hC,he⟩
      cases he
      exact ⟨hR,hC,hT⟩
  rw [he]
  calc
    _ ≤ ∑ y ∈ points a b z₁ z₂ r T,
        (((HighRankExcess.partners (hitSpan a b y z₁)).image (Prod.mk y)).card:ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ _y ∈ points a b z₁ z₂ r T, 2*(Fintype.card K:ℝ)^(n-r-1) := by
      apply sum_le_sum
      intro y hy
      rw [card_image_of_injective _ (by intro c c' hh; exact (Prod.mk.inj hh).2)]
      exact partner_bound hr _ (mem_filter.mp (mem_filter.mp hy).1).2
    _ = _ := by simp

lemma mean_points {h : ℕ} (w : Ω → ℝ) (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ : Fin h → Ω) (r T : ℕ) :
    (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂*((points a b z₁ z₂ r T).card:ℝ)) =
      ∑ y ∈ rankPoints a b z₁ r, FiniteSamplingBounds.rowTail (marginal w b)
        (projectivePoints (hitSpan a b y z₁)) h T := by
  let F (z : Fin h → Projectivization K (Fin n → K)) : ℝ :=
    (((rankPoints a b z₁ r).filter (fun y => T ≤
      FiniteSamplingBounds.hitCount (projectivePoints (hitSpan a b y z₁)) z)).card:ℝ)
  have he : ∀ z₂, ((points a b z₁ z₂ r T).card:ℝ) = F (fun i => b (z₂ i)) := by
    intro z₂
    simp only [F, points, FiniteSamplingBounds.hitCount, mem_projectivePoints]
  simp_rw [he]
  have H := row_pushforward (ι := Fin h) w b F
  calc
    _ = ∑ z : Fin h → Projectivization K (Fin n → K),
        ProductLaw.weight (marginal w b) z*F z := by
      convert H using 1
      all_goals try with_reducible_and_instances rfl
      congr!
      · congr 1
        ext z
        simp
    _ = _ := by
      convert HighRankSampling.mean_admitted_eq (marginal w b)
        (rankPoints a b z₁ r) (fun y => hitSpan a b y z₁) h T using 1
      all_goals try with_reducible_and_instances rfl
      congr!

theorem expected_domain {h r T : ℕ} (hn : 0<n) (hr : 0 < r) (hrn : r<n)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z=1)
    (a : Ω → Module.Dual K (Fin n → K)) (b : Ω → Projectivization K (Fin n → K))
    (z₁ : Fin h → Ω) (X : Finset (Projectivization K (Fin n → K)))
    (hsupp : ∀ x, x∉X → marginal w b x=0)
    (A u : ℝ) (hA : 0<A) (hu : 0<u) (huA : u ≤ 2*A)
    (hu20 : u≤1/20) (hCu : 20*Real.exp (1/2)*u≤1)
    (hcap : ∀ x ∈ X, marginal w b x ≤ A/(Fintype.card K:ℝ)^r)
    (hT : (h:ℝ)/(10*(Fintype.card K:ℝ))≤T) (hTn : n+1≤T) :
    (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂*((domain a b z₁ z₂ r T).card:ℝ)) ≤
      (10*(n:ℝ)*A/u)^n*X.card*(1+2^(n+1))*(2*(Fintype.card K:ℝ)^(n-r-1)) := by
  have H := HighRankSampling.high_rank_expected hn (marginal w b)
    (marginal_nonneg w hw b) (by rw [marginal_total,ht]) X (rankPoints a b z₁ r)
    hsupp A u hA hu huA hu20 hCu r hr hcap (fun y => hitSpan a b y z₁)
    (fun y hy => (mem_filter.mp hy).2) (fun y _ => center_le a b y z₁) h T hT hTn
  calc
    _ ≤ ∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂*
        (((points a b z₁ z₂ r T).card:ℝ)*(2*(Fintype.card K:ℝ)^(n-r-1))) := by
      apply sum_le_sum
      intro z₂ _
      exact mul_le_mul_of_nonneg_left (domain_card hrn a b z₁ z₂ T) (ProductLaw.nonneg w hw z₂)
    _ = (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂*((points a b z₁ z₂ r T).card:ℝ))*
        (2*(Fintype.card K:ℝ)^(n-r-1)) := by simp only [← mul_assoc, sum_mul]
    _ ≤ _ := by
      rw [mean_points]
      exact mul_le_mul_of_nonneg_right H (by positivity)

end
end SharpLogRamsey.HighRankSize

namespace SharpLogRamsey.FiniteRowProcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω X : Type*} [Fintype Ω]

omit [Fintype Ω] in
lemma weight_nonneg (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) {n : ℕ} (z : Fin n → Ω) :
    0 ≤ weight w z := prod_nonneg (fun _ _ => hw _)

lemma weight_total (w : Ω → ℝ) (hw : ∑ a, w a = 1) (n : ℕ) :
    ∑ z : Fin n → Ω, weight w z = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [hw]

lemma expected_zero (w : Ω → ℝ) (step : X → Ω → X) (x : X) (f : X → ℝ) :
    expected w step 0 x f = f x := by simp [expected, weight, run]

lemma expected_succ (w : Ω → ℝ) (step : X → Ω → X) (n : ℕ) (x : X) (f : X → ℝ) :
    expected w step (n+1) x f = ∑ a, w a * expected w step n (step x a) f := by
  unfold expected
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Ω))
    (fun z => weight w z * f (run step (n+1) z x))]
  simp only [Fintype.sum_prod_type]
  change (∑ a, ∑ z, weight w (Fin.cons a z) * f (run step (n+1) (Fin.cons a z) x)) = _
  simp only [run, Fin.cons_zero, Fin.tail_cons, weight, Fin.prod_univ_succ, Fin.cons_succ]
  simp only [mul_assoc, mul_sum]

lemma expected_le_one (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (ht : ∑ a, w a = 1)
    (step : X → Ω → X) (n : ℕ) (x : X) (f : X → ℝ) (hf : ∀ x, f x ≤ 1) :
    expected w step n x f ≤ 1 := by
  rw [← weight_total w ht n]
  apply sum_le_sum
  intro z _
  exact mul_le_of_le_one_right (weight_nonneg w hw z) (hf _)

omit [Fintype Ω] in
lemma rank_run (step : X → Ω → X) (rank : X → ℕ)
    (hmono : ∀ x a, rank x ≤ rank (step x a)) (n : ℕ) (z : Fin n → Ω) (x : X) :
    rank x ≤ rank (run step n z x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact (hmono x (z 0)).trans (ih (Fin.tail z) _)

theorem rank_reached (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (ht : ∑ a, w a = 1)
    (step : X → Ω → X) (rank : X → ℕ) (r : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmono : ∀ x a, rank x ≤ rank (step x a))
    (hbad : ∀ x, rank x < r →
      (∑ a, w a * (if rank (step x a) ≤ rank x then 1 else 0)) ≤ δ)
    (n : ℕ) (x : X) (hx : r ≤ rank x+n) :
    expected w step n x (fun y => if rank y < r then 1 else 0) ≤ n*δ := by
  induction n generalizing x with
  | zero =>
    rw [expected_zero]
    simp only [Nat.add_zero] at hx
    simp [Nat.not_lt.mpr hx]
  | succ n ih =>
    by_cases hxr : r ≤ rank x
    · have hz : expected w step (n+1) x (fun y => if rank y < r then 1 else 0) = 0 := by
        apply sum_eq_zero
        intro z _
        simp [Nat.not_lt.mpr (hxr.trans (rank_run step rank hmono _ z x))]
      rw [hz]
      positivity
    · have hb := hbad x (Nat.lt_of_not_ge hxr)
      rw [expected_succ]
      calc
        _ ≤ ∑ a, w a * ((n:ℝ)*δ + if rank (step x a) ≤ rank x then 1 else 0) := by
          apply sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ (hw a)
          by_cases ha : rank (step x a) ≤ rank x
          · rw [ite_eq_left ha]
            exact (expected_le_one w hw ht step n (step x a) _ (by intro y; split_ifs <;> norm_num)).trans
              (by nlinarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n])
          · rw [ite_eq_right ha, add_zero]
            apply ih
            omega
        _ = (n:ℝ)*δ + ∑ a, w a * (if rank (step x a) ≤ rank x then 1 else 0) := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, ht, one_mul]
        _ ≤ (n:ℝ)*δ+δ := add_le_add_right hb _
        _ = (n+1:ℕ)*δ := by push_cast; ring

end
end SharpLogRamsey.FiniteRowProcess

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_RowSpan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankCoverage
open scoped BigOperators
open Finset Classical FiniteRowProcess
noncomputable section
variable {Ω K V : Type*} [Fintype Ω] [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma le_rowSpan (A : Ω → Submodule K V) {m : ℕ} (W : Submodule K V) (z : Fin m → Ω) :
    W ≤ rowSpan A W z := le_sup_left

omit [Fintype Ω] [FiniteDimensional K V] in
lemma rowSpan_eq (A : Ω → Submodule K V) {m : ℕ} (W : Submodule K V) (z : Fin m → Ω) :
    rowSpan A W z = W ↔ ∀ i, A (z i) ≤ W := by
  simp only [rowSpan, sup_eq_left, iSup_le_iff]

omit [Fintype Ω] in
lemma rowSpan_rank (A : Ω → Submodule K V) {m : ℕ} (W : Submodule K V) (z : Fin m → Ω) :
    Module.finrank K (rowSpan A W z) ≤ Module.finrank K W ↔ ∀ i, A (z i) ≤ W := by
  constructor
  · intro h
    apply (rowSpan_eq A W z).mp
    symm
    apply Submodule.eq_of_le_of_finrank_eq (le_rowSpan A W z)
    exact le_antisymm (Submodule.finrank_mono (le_rowSpan A W z)) h
  · intro h
    rw [(rowSpan_eq A W z).mpr h]

omit [Fintype Ω] [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma indicator_all {ι : Type*} [Fintype ι] (P : ι → Prop)
    [DecidablePred P] [Decidable (∀ i, P i)] :
    (if ∀ i, P i then (1:ℝ) else 0) = ∏ i, if P i then 1 else 0 := by
  by_cases h : ∀ i, P i
  · simp [h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [ite_eq_right (by intro hh; exact hi (hh i))]
    symm
    apply prod_eq_zero (mem_univ i)
    simp [hi]

theorem stagnation_mass (w : Ω → ℝ) (A : Ω → Submodule K V)
    (m : ℕ) (W : Submodule K V) :
    (∑ z : Fin m → Ω, weight w z *
      (if Module.finrank K (rowSpan A W z) ≤ Module.finrank K W then 1 else 0)) =
      (∑ a, w a * (if A a ≤ W then 1 else 0))^m := by
  simp_rw [rowSpan_rank]
  have hh (z : Fin m → Ω) :
      (if ∀ i, A (z i) ≤ W then (1:ℝ) else 0) =
        ∏ i, if A (z i) ≤ W then 1 else 0 := by
      simpa only using (indicator_all (fun i : Fin m => A (z i) ≤ W))
  simp_rw [hh, weight, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (a : Ω) => w a * (if A a ≤ W then 1 else 0))]
  simp

theorem span_growth (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (ht : ∑ a, w a = 1)
    (A : Ω → Submodule K V) (r m : ℕ) (p : ℝ) (hp : p ≤ 1)
    (hescape : ∀ W : Submodule K V, Module.finrank K W < r →
      p ≤ ∑ a, w a * (if ¬ A a ≤ W then 1 else 0))
    (W : Submodule K V) :
    expected (weight w : (Fin m → Ω) → ℝ) (rowSpan A) r W
      (fun U => if Module.finrank K U < r then 1 else 0) ≤ r*(1-p)^m := by
  apply rank_reached (weight w) (weight_nonneg w hw) (weight_total w ht m)
    (rowSpan A) (fun U => Module.finrank K U) r ((1-p)^m) (pow_nonneg (by linarith) _)
  · intro U z
    exact Submodule.finrank_mono (le_rowSpan A U z)
  · intro U hU
    rw [stagnation_mass]
    have hs : (∑ a, w a * (if A a ≤ U then 1 else 0)) +
        (∑ a, w a * (if ¬ A a ≤ U then 1 else 0)) = 1 := by
      rw [← sum_add_distrib]
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      apply sum_congr rfl
      intro a _
      by_cases ha : A a ≤ U <;> simp [ha]
    have h0 : 0 ≤ ∑ a, w a * (if A a ≤ U then 1 else 0) := by
      apply sum_nonneg
      intro a _
      split_ifs
      · simpa only [mul_one] using hw a
      · simp
    apply pow_le_pow_left₀ h0
    linarith [hescape U hU]
  · omega

variable [Finite K] [Fintype (Projectivization K V)]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma projective_card (W : Submodule K V) :
    (univ.filter (fun b : Projectivization K V => b.submodule ≤ W)).card =
      ∑ i ∈ range (Module.finrank K W), Nat.card K^i := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

omit [Fintype Ω] [Fintype (Projectivization K V)] [Field K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [Finite K] in
lemma geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma small_span_card (r : ℕ) (hr : 2 ≤ r) (W : Submodule K V)
    (hW : Module.finrank K W < r) :
    ((univ.filter (fun b : Projectivization K V => b.submodule ≤ W)).card : ℝ) ≤
      2*(Nat.card K:ℝ)^(r-2) := by
  rw [projective_card, Nat.cast_sum]
  push_cast
  calc
    _ ≤ ∑ i ∈ range ((r-2)+1), (Nat.card K:ℝ)^i := by
      apply sum_le_sum_of_subset_of_nonneg
      · apply range_mono
        omega
      · intro _ _ _; positivity
    _ ≤ _ := geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)) _

omit [Finite K] [FiniteDimensional K V] in
lemma marginal_mass (w : Ω → ℝ) (b : Ω → Projectivization K V) (W : Submodule K V) :
    (∑ a, w a * (if (b a).submodule ≤ W then 1 else 0)) =
      ∑ y ∈ univ.filter (fun y : Projectivization K V => y.submodule ≤ W),
        ∑ a ∈ univ.filter (fun a => b a = y), w a := by
  rw [sum_fiberwise_eq_sum_filter univ
    (univ.filter (fun y : Projectivization K V => y.submodule ≤ W)) b w]
  simp [sum_filter, mul_ite]

omit [Finite K] [FiniteDimensional K V] in
lemma marginal_cap (w : Ω → ℝ) (b : Ω → Projectivization K V) (M : ℝ)
    (hM : ∀ y, (∑ a ∈ univ.filter (fun a => b a = y), w a) ≤ M) (W : Submodule K V) :
    (∑ a, w a * (if (b a).submodule ≤ W then 1 else 0)) ≤
      M * (univ.filter (fun y : Projectivization K V => y.submodule ≤ W)).card := by
  rw [marginal_mass]
  calc
    _ ≤ ∑ _y ∈ univ.filter (fun y : Projectivization K V => y.submodule ≤ W), M := by
      apply sum_le_sum
      intro y _
      exact hM y
    _ = _ := by simp [mul_comm]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma escape_mass (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (W : Submodule K V) :
    (∑ z, w z * (if a z y.rep = 0 then 1 else 0)) -
      (∑ z, w z * (if (b z).submodule ≤ W then 1 else 0)) ≤
        ∑ z, w z * (if ¬ hitSpace a b y z ≤ W then 1 else 0) := by
  rw [sub_le_iff_le_add, ← sum_add_distrib]
  apply sum_le_sum
  intro z _
  by_cases hz : a z y.rep = 0 <;>
    by_cases hb : (b z).submodule ≤ W <;>
    simp [hitSpace, hz, hb, hw z]

theorem projective_span_growth (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (r m : ℕ) (hr : 2 ≤ r) (H M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u, (∑ z ∈ univ.filter (fun z => b z = u), w z) ≤ M)
    (hH : H ≤ ∑ z, w z * (if a z y.rep = 0 then 1 else 0))
    (hH1 : H ≤ 1) :
    expected (weight w : (Fin m → Ω) → ℝ) (rowSpan (hitSpace a b y)) r y.submodule
      (fun U => if Module.finrank K U < r then 1 else 0) ≤
        r*(1-(H-2*M*(Nat.card K:ℝ)^(r-2)))^m := by
  apply span_growth w hw ht (hitSpace a b y) r m _
  · have hnonneg : 0 ≤ 2*M*(Nat.card K:ℝ)^(r-2) := by positivity
    linarith
  · intro W hW
    have hcap := (marginal_cap w b M hM W).trans
      (mul_le_mul_of_nonneg_left (small_span_card r hr W hW) hM0)
    have hesc := escape_mass w hw a b y W
    linarith

end
end SharpLogRamsey.HighRankCoverage

namespace SharpLogRamsey.HighRankGrowth
open scoped BigOperators
open Finset Classical FiniteRowProcess HighRankCoverage HighRankDecoder
noncomputable section
variable {Ω K V : Type*} [Fintype Ω] [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma run_span_le (A : Ω → Submodule K V) (m n : ℕ)
    (z : Fin n → Fin m → Ω) (W U : Submodule K V)
    (hW : W ≤ U) (hA : ∀ i j, A (z i j) ≤ U) :
    run (rowSpan A) n z W ≤ U := by
  induction n generalizing W with
  | zero => exact hW
  | succ n ih =>
    apply ih (fun i => z i.succ) (rowSpan A W (z 0))
    · apply sup_le hW
      exact iSup_le (hA 0)
    · intro i j
      exact hA i.succ j

omit [Fintype Ω] [FiniteDimensional K V] in
lemma run_le_full {h r m : ℕ} (e : Fin r × Fin m ↪ Fin h)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Fin h → Ω) :
    run (rowSpan (HighRankCoverage.hitSpace a b y)) r
      (fun i j => z (e (i,j))) y.submodule ≤ hitSpan a b y z := by
  apply run_span_le
  · exact center_le a b y z
  · intro i j
    unfold HighRankCoverage.hitSpace
    split_ifs with hi
    · exact hit_le a b y z (e (i,j)) hi
    · exact bot_le

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma block_mean (w : Ω → ℝ) (ht : ∑ x, w x = 1) {h r m : ℕ}
    (e : Fin r × Fin m ↪ Fin h) (f : (Fin r → Fin m → Ω) → ℝ) :
    (∑ z : Fin h → Ω, ProductLaw.weight w z*f (fun i j => z (e (i,j)))) =
      ∑ z : Fin r → Fin m → Ω, weight (weight w : (Fin m → Ω) → ℝ) z*f z := by
  have H := ProductLaw.marginal w ht e (fun z => f (fun i j => z (i,j)))
  trans ∑ z : Fin r × Fin m → Ω, ProductLaw.weight w z*f (fun i j => z (i,j))
  · convert H using 1 <;> congr!
  rw [← (Equiv.curry (Fin r) (Fin m) Ω).symm.sum_comp]
  apply sum_congr rfl
  intro z _
  congr 1
  simp only [ProductLaw.weight, weight, Fintype.prod_prod_type, Equiv.curry_symm_apply, Function.uncurry]

variable [Finite K] [Fintype (Projectivization K V)]

theorem raw_row_span_growth (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (ht : ∑ z, w z = 1) (a : Ω → Module.Dual K V)
    (b : Ω → Projectivization K V) (y : Projectivization K V)
    (h r m : ℕ) (e : Fin r × Fin m ↪ Fin h) (hr : 2 ≤ r)
    (H M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u, (∑ z ∈ univ.filter (fun z => b z = u), w z) ≤ M)
    (hH : H ≤ ∑ z, w z * (if a z y.rep = 0 then 1 else 0)) (hH1 : H ≤ 1) :
    (∑ z : Fin h → Ω, ProductLaw.weight w z*
      (if Module.finrank K (hitSpan a b y z) < r then 1 else 0)) ≤
        r*(1-(H-2*M*(Nat.card K:ℝ)^(r-2)))^m := by
  let f (z : Fin r → Fin m → Ω) : ℝ :=
    if Module.finrank K (run (rowSpan (HighRankCoverage.hitSpace a b y)) r z y.submodule : Submodule K V) < r
      then 1 else 0
  calc
    _ ≤ ∑ z : Fin h → Ω, ProductLaw.weight w z*f (fun i j => z (e (i,j))) := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (ProductLaw.nonneg w hw z)
      dsimp [f]
      split_ifs with hfull hpart hpart
      · rfl
      · exact False.elim (hpart ((Submodule.finrank_mono (run_le_full e a b y z)).trans_lt hfull))
      · norm_num
      · rfl
    _ = _ := block_mean w ht e f
    _ ≤ _ := projective_span_growth w hw ht a b y r m hr H M hM0 hM hH hH1

end
end SharpLogRamsey.HighRankGrowth

namespace SharpLogRamsey.FiniteEventBounds
open scoped BigOperators
open Finset Classical
noncomputable section

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by unfold indicator; split_ifs <;> norm_num
lemma indicator_le_one (P : Prop) : indicator P ≤ 1 := by unfold indicator; split_ifs <;> norm_num
lemma indicator_mono {P Q : Prop} (H : P → Q) : indicator P ≤ indicator Q := by
  unfold indicator
  by_cases hp : P
  · simp only [hp, ite_eq_left]
    rw [ite_eq_left (H hp)]
  · simp only [hp, ite_false]
    split_ifs <;> norm_num
lemma indicator_or_le (P Q : Prop) : indicator (P ∨ Q) ≤ indicator P+indicator Q := by
  unfold indicator
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]
lemma indicator_or_five (A B C D E : Prop) :
    indicator (A ∨ B ∨ C ∨ D ∨ E) ≤
      indicator A+indicator B+indicator C+indicator D+indicator E := by
  have h₁ := indicator_or_le A (B ∨ C ∨ D ∨ E)
  have h₂ := indicator_or_le B (C ∨ D ∨ E)
  have h₃ := indicator_or_le C (D ∨ E)
  have h₄ := indicator_or_le D E
  linarith

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma mean2_nonneg (w : X → ℝ) (v : Y → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y) (f : X → Y → ℝ)
    (hf : ∀ x y, 0 ≤ f x y) : 0 ≤ mean2 w v f := by
  apply sum_nonneg
  intro x _
  apply mul_nonneg (hw x)
  apply sum_nonneg
  intro y _
  exact mul_nonneg (hv y) (hf x y)

lemma mean2_mono (w : X → ℝ) (v : Y → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y) {f g : X → Y → ℝ}
    (H : ∀ x y, f x y ≤ g x y) : mean2 w v f ≤ mean2 w v g := by
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hw x)
  apply sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (H x y) (hv y)

lemma mean2_add (w : X → ℝ) (v : Y → ℝ) (f g : X → Y → ℝ) :
    mean2 w v (fun x y => f x y+g x y) = mean2 w v f+mean2 w v g := by
  simp [mean2, mul_add, sum_add_distrib]

lemma mean2_const (w : X → ℝ) (v : Y → ℝ)
    (hw : ∑ x, w x=1) (hv : ∑ y, v y=1) (c : ℝ) :
    mean2 w v (fun _ _ => c) = c := by
  simp [mean2, ← sum_mul, hw, hv]

lemma mean2_left (w : X → ℝ) (v : Y → ℝ) (hv : ∑ y, v y=1) (f : X → ℝ) :
    mean2 w v (fun x _ => f x) = ∑ x, w x*f x := by
  simp [mean2, ← sum_mul, hv]

lemma mean2_right (w : X → ℝ) (v : Y → ℝ) (hw : ∑ x, w x=1) (f : Y → ℝ) :
    mean2 w v (fun _ y => f y) = ∑ y, v y*f y := by
  simp [mean2, ← sum_mul, hw]

lemma mean2_cover_five (w : X → ℝ) (v : Y → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (A : X → Prop) (B : Y → Prop) (C : X → Prop) (D : Y → Prop)
    (E J : X → Y → Prop)
    (H : ∀ x y, J x y → A x ∨ B y ∨ C x ∨ D y ∨ E x y) :
    mean2 w v (fun x y => indicator (J x y)) ≤
      mean2 w v (fun x _ => indicator (A x))+
      mean2 w v (fun _ y => indicator (B y))+
      mean2 w v (fun x _ => indicator (C x))+
      mean2 w v (fun _ y => indicator (D y))+
      mean2 w v (fun x y => indicator (E x y)) := by
  have hh := mean2_mono w v hw hv (fun x y =>
    (indicator_mono (H x y)).trans (indicator_or_five (A x) (B y) (C x) (D y) (E x y)))
  simpa only [mean2_add] using hh

variable {Z : Type*} [Fintype Z]

lemma mean2_sum (w : X → ℝ) (v : Y → ℝ) (p : Z → ℝ) (f : Z → X → Y → ℝ) :
    (∑ z, p z*mean2 w v (f z)) =
      mean2 w v (fun x y => ∑ z, p z*f z x y) := by
  unfold mean2
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  ring

omit [Fintype X] [Fintype Y] in
lemma average_with_exception (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z)
    (ht : ∑ z, p z=1) (G : Z → Prop) (f c : Z → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (hc : ∀ z, 0 ≤ c z) (hf : ∀ z, f z ≤ 1)
    (hgood : ∀ z, p z≠0 → G z → f z ≤ b+c z) :
    (∑ z, p z*f z) ≤ (∑ z, p z*indicator (¬G z))+b+∑ z, p z*c z := by
  calc
    _ ≤ ∑ z, p z*(indicator (¬G z)+b+c z) := by
      apply sum_le_sum
      intro z _
      by_cases hz : p z=0
      · simp [hz]
      apply mul_le_mul_of_nonneg_left _ (hp z)
      by_cases hG : G z
      · simpa [indicator, hG] using hgood z hz hG
      · simp only [indicator, hG, not_false_eq_true, ite_true]
        have H := hf z
        linarith [hc z]
    _ = _ := by simp [mul_add, sum_add_distrib, ← sum_mul, ht]

end
end SharpLogRamsey.FiniteEventBounds

namespace SharpLogRamsey.HighRankCoverageProbability
open scoped BigOperators
open Finset Classical FiniteEventBounds HighRankDecoder
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (Projectivization K V)] [Fintype Ω]

omit [Finite K] [Fintype (Projectivization K V)] in
theorem raw_coverage_union (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (ht : ∑ z, w z=1) (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V))
    (hcy : c.rep y.rep=0) (h r T : ℕ) :
    mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator (¬Admitted a b z₁ z₂ r T y c)) ≤
    (∑ z : Fin h → Ω, ProductLaw.weight w z*
       indicator (Module.finrank K (hitSpan a b y z) < r))+
    (∑ z : Fin h → Ω, ProductLaw.weight w z*
       indicator ((univ.filter (fun i => a (z i) y.rep=0)).card<T))+
    2*(∑ z : Fin h → Ω, ProductLaw.weight w z*
       indicator (∃ i, a (z i) y.rep=0 ∧ c.rep (b (z i)).rep≠0))+
    mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator
        (r < Module.finrank K (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ∧
         hitSpan a b y z₁ ⊔ hitSpan a b y z₂ ≤ LinearMap.ker c.rep)) := by
  have hnt : ∑ z : Fin h → Ω, ProductLaw.weight w z=1 := by
    convert ProductLaw.total (ι := Fin h) w ht using 1
    all_goals try with_reducible_and_instances rfl
    congr!
  have hnn := fun z : Fin h → Ω => ProductLaw.nonneg w hw z
  have H := mean2_cover_five (ProductLaw.weight w : (Fin h → Ω) → ℝ)
    (ProductLaw.weight w : (Fin h → Ω) → ℝ) hnn hnn
    (fun z => Module.finrank K (hitSpan a b y z) < r)
    (fun z => (univ.filter (fun i => a (z i) y.rep=0)).card < T)
    (fun z => ∃ i, a (z i) y.rep=0 ∧ c.rep (b (z i)).rep≠0)
    (fun z => ∃ i, a (z i) y.rep=0 ∧ c.rep (b (z i)).rep≠0)
    (fun z₁ z₂ => r < Module.finrank K
        (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ∧
      hitSpan a b y z₁ ⊔ hitSpan a b y z₂ ≤ LinearMap.ker c.rep)
    (fun z₁ z₂ => ¬Admitted a b z₁ z₂ r T y c) (by
      intro z₁ z₂ hJ
      by_contra hbad
      push Not at hbad
      apply hJ
      apply coverage a b z₁ z₂ r T y c hcy
      · exact hbad.2.2.1
      · exact hbad.2.2.2.1
      · exact hbad.1
      · rintro ⟨hrank,hann⟩
        exact hbad.2.2.2.2 hrank hann
      · exact hbad.2.1)
  rw [mean2_left _ _ hnt, mean2_right _ _ hnt,
    mean2_left _ _ hnt, mean2_right _ _ hnt] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] [Fintype (Projectivization K V)] in

end
end SharpLogRamsey.HighRankCoverageProbability
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_RawLowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankCoverageProbability
open scoped BigOperators
open Finset Classical FiniteEventBounds HighRankDecoder
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (Projectivization K V)] [Fintype Ω]
omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] [Fintype (Projectivization K V)] in
lemma raw_lower_tail (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (ht : ∑ z, w z=1) (Q : Ω → Prop) (q : ℝ) (hq : 0<q) (h T : ℕ)
    (hE : 2/(5*q) ≤ ∑ z ∈ univ.filter Q, w z)
    (hT : (T:ℝ) ≤ (h:ℝ)/(10*q)+1) :
    (∑ z : Fin h → Ω, ProductLaw.weight w z *
      indicator ((univ.filter (fun i => Q (z i))).card < T)) ≤
      Real.exp (1-(h:ℝ)/(10*q)) := by
  have hl := FiniteSamplingBounds.rowLower_highRank w hw ht (univ.filter Q) h T q hq hE hT
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  simp [FiniteSamplingBounds.rowLower, FiniteSamplingBounds.hitCount,
    FiniteSamplingBounds.rowWeight, ProductLaw.weight, indicator, mul_ite]

theorem fixed_query_bound (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (ht : ∑ z, w z=1) (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V))
    (hcy : c.rep y.rep=0) (h r m T : ℕ) (e : Fin r × Fin m ↪ Fin h) (hr : 2 ≤ r)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u, (∑ z ∈ univ.filter (fun z => b z=u), w z) ≤ M)
    (hE : 2/(5*(Nat.card K:ℝ)) ≤ ∑ z ∈ univ.filter (fun z => a z y.rep=0), w z)
    (hT : (T:ℝ) ≤ (h:ℝ)/(10*(Nat.card K:ℝ))+1) :
    mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ) (ProductLaw.weight w : (Fin h → Ω) → ℝ)
        (fun z₁ z₂ => indicator (¬Admitted a b z₁ z₂ r T y c)) ≤
      r*(1-(2/(5*(Nat.card K:ℝ))-2*M*(Nat.card K:ℝ)^(r-2)))^m+
      Real.exp (1-(h:ℝ)/(10*(Nat.card K:ℝ)))+2*h*conflictMass w a b y c+
      mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ) (ProductLaw.weight w : (Fin h → Ω) → ℝ)
        (fun z₁ z₂ => indicator
          (r < Module.finrank K (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ∧
           hitSpan a b y z₁ ⊔ hitSpan a b y z₂ ≤ LinearMap.ker c.rep)) := by
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast Nat.card_pos
  have hH : (∑ z ∈ univ.filter (fun z => a z y.rep=0), w z) =
      ∑ z, w z*(if a z y.rep=0 then 1 else 0) := by
    simp [sum_filter, mul_ite]
  have hH1 : 2/(5*(Nat.card K:ℝ)) ≤ 1 := by
    apply hE.trans
    rw [← ht]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; exact hw _)
  have hg := HighRankGrowth.raw_row_span_growth w hw ht a b y h r m e hr
    (2/(5*(Nat.card K:ℝ))) M hM0 hM (by rwa [← hH]) hH1
  have hl := raw_lower_tail w hw ht (fun z => a z y.rep=0) (Nat.card K:ℝ) hq h T hE hT
  have hc := ProductLaw.row_exists_le (ι := Fin h) w hw ht
    (fun z => a z y.rep=0 ∧ c.rep (b z).rep≠0)
  simp only [Fintype.card_fin] at hc
  apply (raw_coverage_union w hw ht a b y c hcy h r T).trans
  refine add_le_add ?_ le_rfl
  have hh := add_le_add (add_le_add hg hl) (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ 2))
  convert hh using 1 <;> simp only [indicator, conflictMass, mul_assoc]
  congr!

end
end SharpLogRamsey.HighRankCoverageProbability

namespace SharpLogRamsey.HighRankAveraged
open scoped BigOperators
open Finset Classical FiniteEventBounds HighRankDecoder HighRankCoverageProbability
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] [Fintype Ω]

theorem excess_average (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z=1)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (U : Finset (Projectivization K V))
    (hsupp : ∀ z, p z≠0 → z.1 ∈ U)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (h d r : ℕ) (hdim : Module.finrank K V=d+1) (hr : r ≤ d)
    (J : ℝ) (hJ : 0 ≤ J) :
    (∑ t, p t*mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator
        (r < Module.finrank K (hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ : Submodule K V) ∧
         hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ ≤ LinearMap.ker t.2.rep))) ≤
      (∑ t ∈ U ×ˢ univ, if J < p t then p t else 0)+
        (if r<d then U.card*(2*(Nat.card K:ℝ)^(d-r-1))*J else 0) := by
  rw [mean2_sum]
  have hnt : ∑ z : Fin h → Ω, ProductLaw.weight w z=1 := by
    convert ProductLaw.total (ι := Fin h) w ht using 1
    all_goals try with_reducible_and_instances rfl
    congr!
  have H : ∀ z₁ z₂ : Fin h → Ω,
      (∑ t, p t* indicator
        (r < Module.finrank K (hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ : Submodule K V) ∧
         hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ ≤ LinearMap.ker t.2.rep)) ≤
      (∑ t ∈ U ×ˢ univ, if J < p t then p t else 0)+
        (if r<d then U.card*(2*(Nat.card K:ℝ)^(d-r-1))*J else 0) := by
    intro z₁ z₂
    unfold indicator
    calc
      _ = ∑ t ∈ HighRankExcess.excessCarrier U
          (fun y => hitSpan a b y z₁ ⊔ hitSpan a b y z₂) r, p t := by
        convert HighRankExcess.target_event_eq U
          (fun y => hitSpan a b y z₁ ⊔ hitSpan a b y z₂) r p hsupp using 1
        all_goals try with_reducible_and_instances rfl
        congr!
      _ ≤ _ := HighRankExcess.target_excess_mass_sharp hdim hr U _ p hp J hJ
  apply (mean2_mono _ _ (fun z => ProductLaw.nonneg w hw z)
    (fun z => ProductLaw.nonneg w hw z) H).trans
  exact le_of_eq (mean2_const _ _ hnt hnt _)

theorem averaged_coverage (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z=1)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hpt : ∑ t, p t=1)
    (hincident : ∀ t, p t≠0 → t.2.rep t.1.rep=0)
    (U : Finset (Projectivization K V)) (hsupp : ∀ t, p t≠0 → t.1 ∈ U)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (h d r m T : ℕ) (hdim : Module.finrank K V=d+1) (hr : 2 ≤ r) (hrd : r ≤ d)
    (e : Fin r × Fin m ↪ Fin h) (M J : ℝ) (hM0 : 0 ≤ M) (hJ : 0 ≤ J)
    (hM : ∀ u, (∑ z ∈ univ.filter (fun z => b z=u), w z) ≤ M)
    (hT : (T:ℝ) ≤ (h:ℝ)/(10*(Nat.card K:ℝ))+1) :
    (∑ t, p t*mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator (¬Admitted a b z₁ z₂ r T t.1 t.2))) ≤
      (∑ t, p t*indicator
        ((∑ z ∈ univ.filter (fun z => a z t.1.rep=0), w z)<2/(5*(Nat.card K:ℝ))))+
      (r*(1-(2/(5*(Nat.card K:ℝ))-2*M*(Nat.card K:ℝ)^(r-2)))^m+
        Real.exp (1-(h:ℝ)/(10*(Nat.card K:ℝ))))+
      2*h*(∑ t, p t*conflictMass w a b t.1 t.2)+
      (∑ t ∈ U ×ˢ univ, if J < p t then p t else 0)+
      (if r<d then U.card*(2*(Nat.card K:ℝ)^(d-r-1))*J else 0) := by
  let G (t : Projectivization K V × Projectivization K (Module.Dual K V)) : Prop :=
    2/(5*(Nat.card K:ℝ)) ≤ ∑ z ∈ univ.filter (fun z => a z t.1.rep=0), w z
  let B : ℝ := r*(1-(2/(5*(Nat.card K:ℝ))-2*M*(Nat.card K:ℝ)^(r-2)))^m+
    Real.exp (1-(h:ℝ)/(10*(Nat.card K:ℝ)))
  let R : (Fin h → Ω) → ℝ := ProductLaw.weight w
  let X (t : Projectivization K V × Projectivization K (Module.Dual K V)) : ℝ :=
    mean2 R R (fun z₁ z₂ => indicator
      (r < Module.finrank K (hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ : Submodule K V) ∧
       hitSpan a b t.1 z₁ ⊔ hitSpan a b t.1 z₂ ≤ LinearMap.ker t.2.rep))
  let F (t : Projectivization K V × Projectivization K (Module.Dual K V)) : ℝ :=
    mean2 R R (fun z₁ z₂ => indicator (¬Admitted a b z₁ z₂ r T t.1 t.2))
  have hnt : ∑ z, R z=1 := by
    convert ProductLaw.total (ι := Fin h) w ht using 1
    all_goals try with_reducible_and_instances rfl
    congr!
  have hn : ∀ z, 0 ≤ R z := fun z => ProductLaw.nonneg w hw z
  have hX : ∀ t, 0 ≤ X t := fun t =>
    mean2_nonneg R R hn hn _ (fun _ _ => indicator_nonneg _)
  have hC : ∀ t : Projectivization K V × Projectivization K (Module.Dual K V), 0 ≤ conflictMass w a b t.1 t.2 := by
    intro t
    apply sum_nonneg
    intro z _
    exact mul_nonneg (hw z) (indicator_nonneg _)
  have hF : ∀ t, F t ≤ 1 := by
    intro t
    apply (mean2_mono R R hn hn (fun _ _ => indicator_le_one _)).trans
    exact le_of_eq (mean2_const R R hnt hnt 1)
  have hq : (2:ℝ) ≤ Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)
  have hH : 2/(5*(Nat.card K:ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    apply add_nonneg _ (Real.exp_pos _).le
    apply mul_nonneg (Nat.cast_nonneg r)
    apply pow_nonneg
    have hh : 0 ≤ 2*M*(Nat.card K:ℝ)^(r-2) := by positivity
    linarith
  have hh := average_with_exception p hp hpt G F
    (fun t => 2*h*conflictMass w a b t.1 t.2+X t) B hB
    (fun t => add_nonneg (mul_nonneg (by positivity) (hC t)) (hX t)) hF
    (by
      intro t hpt hG
      have H := fixed_query_bound w hw ht a b t.1 t.2 (hincident t hpt)
        h r m T e hr M hM0 hM hG hT
      dsimp [F, B, R, X]
      exact H.trans_eq (by ring))
  have he := excess_average w hw ht p hp U hsupp a b h d r hdim hrd J hJ
  have hsum : (∑ t, p t*(2*h*conflictMass w a b t.1 t.2+X t)) =
      2*h*(∑ t, p t*conflictMass w a b t.1 t.2)+∑ t, p t*X t := by
    simp_rw [mul_add, sum_add_distrib]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  rw [hsum] at hh
  have herr : (∑ t, p t*indicator (¬G t)) =
      ∑ t, p t*indicator
        ((∑ z ∈ univ.filter (fun z => a z t.1.rep=0), w z)<2/(5*(Nat.card K:ℝ))) := by
    simp only [G, not_le]
  rw [herr] at hh
  dsimp [F, B, X, R] at hh
  linarith

end
end SharpLogRamsey.HighRankAveraged

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
section Projective
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem low_incidence_target_mass {n : ℕ} (hdim : Module.finrank K V = n+3)
    (w : Projectivization K V → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (M : ℝ) (hM : ∀ x, w x ≤ M)
    (v : Projectivization K (Module.Dual K V) → ℝ) (N : ℝ)
    (hN0 : 0 ≤ N) (hN : ∀ y, v y ≤ N) :
    (∑ y ∈ univ.filter (fun y => weightedIncidences SharpLogRamsey.Incidence.Incident w y <
      2/(5*(Nat.card K:ℝ))), v y) ≤ 100*(Nat.card K:ℝ)^(n+3)*M*N := by
  let q : ℝ := Nat.card K
  let u : ℝ := ∑ i ∈ range (n+2), q^i
  let p : ℝ := u/(∑ i ∈ range (n+3), q^i)
  let B := univ.filter (fun y => weightedIncidences SharpLogRamsey.Incidence.Incident w y < 2/(5*q))
  have hq : 2 ≤ q := by
    change (2:ℝ) ≤ Nat.card K
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)
  have hq0 : 0 < q := by linarith
  have hu : 1 ≤ u := by
    have hs := single_le_sum (f := fun i => q^i)
      (fun i _ => pow_nonneg hq0.le i) (show 0 ∈ range (n+2) by simp)
    simpa [u] using hs
  have hvpos : 0 < ∑ i ∈ range (n+3), q^i := by
    rw [geom_sum_succ]
    change 0 < q*u+1
    positivity
  have hp : 1/(2*q) ≤ p := by
    change 1/(2*q) ≤ u/(∑ i ∈ range (n+3), q^i)
    apply (div_le_div_iff₀ (by positivity) hvpos).mpr
    rw [geom_sum_succ]
    change 1*(q*u+1) ≤ u*(2*q)
    nlinarith
  have hnorm : (∑ x, w x^2) ≤ M := by
    calc
      _ ≤ ∑ x, M*w x := by
        apply sum_le_sum
        intro x _
        nlinarith [mul_le_mul_of_nonneg_right (hM x) (hw x)]
      _ = M := by rw [← mul_sum, ht, mul_one]
  have hvar := (projective_variance_le hdim w).trans
    (mul_le_mul_of_nonneg_left hnorm (show 0 ≤ q^(n+1) by positivity))
  change (∑ y, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p*(∑ x, w x))^2) ≤ q^(n+1)*M at hvar
  rw [ht, mul_one] at hvar
  have hc : (B.card:ℝ)*(1/(10*q))^2 ≤ q^(n+1)*M := by
    calc
      _ = ∑ _y ∈ B, (1/(10*q))^2 := by simp
      _ ≤ ∑ y ∈ B, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p)^2 := by
        apply sum_le_sum
        intro y hy
        have hb : weightedIncidences SharpLogRamsey.Incidence.Incident w y < 2/(5*q) := (mem_filter.mp hy).2
        have hg : 1/(10*q) ≤ p-weightedIncidences SharpLogRamsey.Incidence.Incident w y := by
          have he : 1/(2*q)-2/(5*q) = 1/(10*q) := by field_simp; ring
          linarith
        have hi : 0 ≤ 1/(10*q) := by positivity
        nlinarith
      _ ≤ ∑ y, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p)^2 := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ B)
        intro y _ _
        positivity
      _ ≤ _ := hvar
  have hmult := mul_le_mul_of_nonneg_right hc (show 0 ≤ 100*q^2 by positivity)
  have hcancel : (B.card:ℝ)*(1/(10*q))^2*(100*q^2) = B.card := by
    field_simp
    ring
  rw [hcancel] at hmult
  have he : q^(n+1)*M*(100*q^2) = 100*q^(n+3)*M := by
    rw [show n+3 = (n+1)+2 by omega, pow_add]
    ring
  rw [he] at hmult
  change (∑ y ∈ B, v y) ≤ _
  calc
    _ ≤ ∑ _y ∈ B, N := by apply sum_le_sum; intro y _; exact hN y
    _ = (B.card:ℝ)*N := by simp
    _ ≤ (100*q^(n+3)*M)*N := mul_le_mul_of_nonneg_right hmult hN0

end Projective
end SharpLogRamsey.Incidence
namespace SharpLogRamsey.ProjectiveDuality
open SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Finite K]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

attribute [local instance] OAI.SharpLogRamsey.ProjectiveDuality.flat_JoinedHighRankAssembly_5
theorem low_incidence_dual_mass {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (ht : ∑ b, w b=1) (M : ℝ) (hM : ∀ b, w b ≤ M)
    (v : Projectivization K V → ℝ) (N : ℝ) (hN0 : 0 ≤ N) (hN : ∀ y, v y ≤ N) :
    (∑ y ∈ univ.filter (fun y => (∑ b, if SharpLogRamsey.Incidence.Incident y b then w b else 0)<
      2/(5*(Nat.card K:ℝ))), v y) ≤ 100*(Nat.card K:ℝ)^(n+3)*M*N := by
  have H := low_incidence_target_mass
    (show Module.finrank K (Module.Dual K V)=n+3 from Subspace.dual_finrank_eq.trans hdim)
    w hw ht M hM (fun y => v (bidual.symm y)) N hN0 (fun y => hN _)
  rw [sum_filter] at H ⊢
  have he : (∑ y : Projectivization K (Module.Dual K (Module.Dual K V)),
      if weightedIncidences SharpLogRamsey.Incidence.Incident w y < 2/(5*(Nat.card K:ℝ)) then v (bidual.symm y) else 0) =
      ∑ y : Projectivization K V,
        if (∑ b, if SharpLogRamsey.Incidence.Incident y b then w b else 0) < 2/(5*(Nat.card K:ℝ)) then v y else 0 := by
    rw [← (bidual (K := K) (V := V)).sum_comp]
    simp only [Equiv.symm_apply_apply, weightedIncidences, incident_bidual]
  rwa [he] at H
end
end SharpLogRamsey.ProjectiveDuality

namespace SharpLogRamsey.HighRankLowHit
open scoped BigOperators
open Finset Classical SharpLogRamsey.Incidence SharpLogRamsey.FiniteMarginals
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V] [Fintype Ω]
    [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma hit_mass (w : Ω → ℝ) (a : Ω → Projectivization K (Module.Dual K V))
    (y : Projectivization K V) :
    (∑ z ∈ univ.filter (fun z => (a z).rep y.rep=0), w z) =
      ∑ b, if SharpLogRamsey.Incidence.Incident y b then marginal w a b else 0 := by
  have H := sum_marginal w a (fun b => if SharpLogRamsey.Incidence.Incident y b then 1 else 0)
  rw [sum_filter]
  calc
    _ = ∑ z, w z*(if SharpLogRamsey.Incidence.Incident y (a z) then 1 else 0) := by
      apply sum_congr rfl
      intro z _
      by_cases hz : (a z).rep y.rep=0 <;> simp [SharpLogRamsey.Incidence.Incident, hz]
    _ = ∑ b, marginal w a b*(if SharpLogRamsey.Incidence.Incident y b then 1 else 0) := H.symm
    _ = _ := by
      apply sum_congr rfl
      intro b _
      split_ifs <;> simp

theorem low_hit_mass {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z=1)
    (a : Ω → Projectivization K (Module.Dual K V)) (M : ℝ)
    (hM : ∀ b, marginal w a b ≤ M)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (N : ℝ) (hN0 : 0 ≤ N) (hN : ∀ y, (∑ c, p (y,c)) ≤ N) :
    (∑ t, p t*(if (∑ z ∈ univ.filter (fun z => (a z).rep t.1.rep=0), w z)<
      2/(5*(Nat.card K:ℝ)) then 1 else 0)) ≤ 100*(Nat.card K:ℝ)^(n+3)*M*N := by
  have H := ProjectiveDuality.low_incidence_dual_mass hdim (marginal w a)
    (marginal_nonneg w hw a) (by rw [marginal_total, ht]) M hM
    (fun y => ∑ c, p (y,c)) N hN0 hN
  rw [sum_filter] at H
  simp_rw [Fintype.sum_prod_type, hit_mass]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro y _
  rw [← sum_mul]
  split_ifs <;> simp
end
end SharpLogRamsey.HighRankLowHit

namespace SharpLogRamsey.HighRankBudgets
open Filter Real
open scoped Topology BigOperators
noncomputable section

lemma eventually_monomial_le_linear (C a ε : ℝ) (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-1))*x := by
      have hp : x^(a-1)*x = x^a := by
        calc
          _ = x^(a-1)*x^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
      rw [mul_assoc, hp]
    _ ≤ ε*x := mul_le_mul_of_nonneg_right hx.le hx0.le

lemma K_upper {σ η D : ℝ} (hσ : 0<σ) (hD : D ≤ σ^(1-η/2)) :
    scaleK σ η D ≤ σ^(1-η/2+3*beta η) := by
  unfold scaleK
  calc
    _ ≤ σ^(1-η/2)*σ^(3*beta η) := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = _ := (Real.rpow_add hσ _ _).symm

lemma eventually_K_linear {η : ℝ} (hη : 0<η) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, D ≤ σ^(1-η/2) → c*scaleK σ η D ≤ ε*σ := by
  have he : 1-η/2+3*beta η < 1 := by unfold beta; linarith
  filter_upwards [eventually_monomial_le_linear c (1-η/2+3*beta η) ε he hε,
    eventually_gt_atTop (0:ℝ)] with σ hh hσ D hD
  exact (mul_le_mul_of_nonneg_left (K_upper hσ hD) hc).trans hh

theorem eventually_exp_K_over_q {η : ℝ} (hη : 0<η) (C a ε : ℝ)
    (hC : 0≤C) (ha : 0≤a) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, D ≤ σ^(1-η/2) →
      C*Real.exp (a*scaleK σ η D)/Real.exp σ < ε := by
  have ht : Tendsto (fun σ : ℝ => C*Real.exp (-(σ/2))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun σ : ℝ => -(σ/2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
    simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul C
  filter_upwards [eventually_K_linear hη a (1/2) ha (by norm_num),
    ht.eventually (gt_mem_nhds hε)] with σ hK hx D hD
  calc
    _ = C*Real.exp (a*scaleK σ η D-σ) := by rw [Real.exp_sub]; ring
    _ ≤ C*Real.exp (-(σ/2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      linarith [hK D hD]
    _ < ε := hx

lemma row_size {q x : ℝ} (hq : 1≤q) (hx : 1≤x) :
    q*x ≤ (⌈q*x⌉₊:ℝ) ∧ (⌈q*x⌉₊:ℝ) ≤ 2*q*x := by
  have hqx : 1≤q*x := by nlinarith
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)⟩

lemma block_size {h d : ℕ} (hd : 0<d) (hhd : 2*d ≤ h) :
    (h:ℝ)/(2*d) ≤ (h/d:ℕ) := by
  have he := Nat.mod_add_div h d
  have hm := Nat.mod_lt h hd
  have hq : 2 ≤ h/d := (Nat.le_div_iff_mul_le hd).mpr hhd
  have hb : h ≤ 2*d*(h/d) := by nlinarith
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*d)).mpr
  exact_mod_cast (show h ≤ h/d*(2*d) by nlinarith)

lemma block_embedding (h d r : ℕ) (hr : r ≤ d) : Nonempty (Fin r × Fin (h/d) ↪ Fin h) := by
  apply Function.Embedding.nonempty_of_card_le
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact (Nat.mul_le_mul_right (h/d) hr).trans (Nat.mul_div_le h d)

theorem growth_tail {q M : ℝ} {r d h : ℕ} (hq : 2≤q) (hM : 0≤M)
    (hr : r≤d) (hd : 0<d) (hhd : 2*d≤h)
    (hescape : 2*M*q^(r-2) ≤ 1/(10*q)) :
    (r:ℝ)*(1-(2/(5*q)-2*M*q^(r-2)))^(h/d) ≤
      d*Real.exp (-3*(h:ℝ)/(20*d*q)) := by
  have hq0 : 0<q := by linarith
  have hb0 : 0 ≤ 1-(2/(5*q)-2*M*q^(r-2)) := by
    have hh : 2/(5*q) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have hp : 0 ≤ 2*M*q^(r-2) := by positivity
    linarith
  have heq : 2/(5*q)-1/(10*q)=3/(10*q) := by field_simp; ring
  have hh : 1-(2/(5*q)-2*M*q^(r-2)) ≤ Real.exp (-(3/(10*q))) := by
    have H := Real.add_one_le_exp (-(3/(10*q)))
    linarith
  have hm := block_size hd hhd
  have hex : -(3/(10*q))*(↑(h/d):ℝ) ≤ -3*(h:ℝ)/(20*d*q) := by
    have H := mul_le_mul_of_nonneg_left hm (show 0≤3/(10*q) by positivity)
    have he : 3/(10*q)*((h:ℝ)/(2*d)) = 3*h/(20*d*q) := by field_simp; ring
    rw [he] at H
    simpa only [neg_mul, neg_div] using neg_le_neg H
  calc
    _ ≤ (r:ℝ)*(Real.exp (-(3/(10*q))))^(h/d) := by gcongr
    _ = (r:ℝ)*Real.exp (-(3/(10*q))*(h/d:ℕ)) := by rw [←Real.exp_nat_mul]; congr 2; ring
    _ ≤ (r:ℝ)*Real.exp (-3*(h:ℝ)/(20*d*q)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (Real.exp_nonneg _)

end
end SharpLogRamsey.HighRankBudgets
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_AtomEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankBudgets
open Filter Real
open scoped Topology BigOperators
noncomputable section
lemma atom_escape {q C K : ℝ} {r : ℕ} (hq : 0<q) (hr : 2 ≤ r)
    (hsmall : 20*C*Real.exp K ≤ q) :
    2*(C*Real.exp K/q^r)*q^(r-2) ≤ 1/(10*q) := by
  have hp : q^r=q^(r-2)*q^2 := by rw [←pow_add]; congr 1; omega
  rw [hp]
  have he : 2*(C*Real.exp K/(q^(r-2)*q^2))*q^(r-2) = 2*C*Real.exp K/q^2 := by
    field_simp
  rw [he]
  apply (div_le_iff₀ (by positivity : 0<q^2)).mpr
  have he : 1/(10*q)*q^2=q/10 := by field_simp
  rw [he]
  linarith

lemma low_hit_budget {q C K : ℝ} {d r r' : ℕ} (hq : 1≤q)
    (hr : d+2 ≤ r+r') :
    100*q^(d+1)*(C*Real.exp K/q^r')*(C*Real.exp K/q^r) ≤
      100*C^2*Real.exp (2*K)/q := by
  have hq0 : 0<q := by linarith
  have hpow : q^(d+1)*q ≤ q^r*q^r' := by
    rw [←pow_succ, ←pow_add]
    exact pow_le_pow_right₀ hq hr
  have H := mul_le_mul_of_nonneg_left hpow (show 0≤100*C^2*Real.exp (2*K) by positivity)
  have he : Real.exp (2*K)=(Real.exp K)^2 := by rw [←Real.exp_nat_mul]; congr 1
  rw [he] at H ⊢
  apply (le_div_iff₀ hq0).mpr
  have hden : 0<q^r'*q^r := by positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  field_simp
  nlinarith [sq_nonneg C]

theorem eventually_polynomial_exp_neg_rpow_lt (C a b c ε : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a*Real.exp (-c*x^b) < ε := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound
    (show 0 < ε/(2*(|C|+1)) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    _ ≤ (|C|+1)*x^a*Real.exp (-c*x^b) := by
      gcongr
    _ ≤ (|C|+1)*(ε/(2*(|C|+1))*Real.exp (c*x^b))*Real.exp (-c*x^b) := by
      gcongr
    _ = ε/2 := by
      rw [mul_assoc (|C|+1), mul_assoc, ← Real.exp_add,
        show c*x^b+-c*x^b=0 by ring, Real.exp_zero]
      field_simp
    _ < ε := by linarith

theorem eventually_error {η : ℝ} (hη : 0<η) (C ε : ℝ) (hC : 0≤C)
    (hε : 0<ε) (d : ℕ) (hd : 0<d) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, D ≤ σ^(1-η/2) → error σ η D C d < ε := by
  have hb : 0<beta η := by unfold beta; positivity
  have hε7 : 0<ε/7 := by positivity
  have h₁ := eventually_exp_K_over_q hη (100*C^2) 2 (ε/7) (by positivity) (by norm_num) hε7
  have h₂ := eventually_polynomial_exp_neg_rpow_lt d 0 (beta η) (3/(20*d)) (ε/7)
    hb (by positivity) hε7
  have h₃ := eventually_polynomial_exp_neg_rpow_lt (Real.exp 1) 0 (beta η) (1/10) (ε/7)
    hb (by norm_num) hε7
  have h₄ : Tendsto (fun σ : ℝ => 4*C*σ^(-(1999*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show 0<1999*beta η by positivity)).const_mul (4*C)
  have h₅ : Tendsto (fun σ : ℝ => C*σ^(-(2*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show 0<2*beta η by positivity)).const_mul C
  have h₆ : Tendsto (fun σ : ℝ => C*σ^(-(4*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show 0<4*beta η by positivity)).const_mul C
  have h₇ := eventually_exp_K_over_q hη (2*C) 1 (ε/7) (by positivity) (by norm_num) hε7
  filter_upwards [h₁,h₂,h₃,h₄.eventually (gt_mem_nhds hε7),
    h₅.eventually (gt_mem_nhds hε7),h₆.eventually (gt_mem_nhds hε7),h₇]
    with σ h₁ h₂ h₃ h₄ h₅ h₆ h₇ D hD
  simp only [Real.rpow_zero,mul_one] at h₂ h₃
  have h₁ := h₁ D hD
  have h₇ := h₇ D hD
  simp only [one_mul] at h₇
  unfold error
  linarith
end
end SharpLogRamsey.HighRankBudgets

namespace SharpLogRamsey.SimultaneousExtraction
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

lemma markov_complement (p : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (ht : ∑ z, p z=1)
    (f g : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    1-(∑ z, p z*f z)/A-(∑ z, p z*g z)/B ≤
      ∑ z ∈ univ.filter (fun z => f z ≤ A ∧ g z ≤ B), p z := by
  have H (z : Ω) : p z*(1-f z/A-g z/B) ≤
      if f z ≤ A ∧ g z ≤ B then p z else 0 := by
    by_cases h : f z ≤ A ∧ g z ≤ B
    · rw [ite_eq_left h]
      have h0 : 0 ≤ f z/A := div_nonneg (hf z) hA.le
      have h1 : 0 ≤ g z/B := div_nonneg (hg z) hB.le
      nlinarith [hp z]
    · rw [ite_eq_right h]
      have he : 1 ≤ f z/A+g z/B := by
        by_cases he : f z ≤ A
        · have hh : B < g z := lt_of_not_ge (fun hh => h ⟨he,hh⟩)
          have hh' : 1 ≤ g z/B := (one_le_div hB).mpr hh.le
          linarith [div_nonneg (hf z) hA.le]
        · have hh' : 1 ≤ f z/A := (one_le_div hA).mpr (le_of_not_ge he)
          linarith [div_nonneg (hg z) hB.le]
      exact mul_nonpos_of_nonneg_of_nonpos (hp z) (by linarith)
  have HH := sum_le_sum (fun z (_ : z∈univ) => H z)
  simpa only [sum_filter, mul_sub, mul_one, mul_div_assoc, sum_sub_distrib,
    sum_div, ht] using HH

theorem simultaneous_mass (p : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (ht : ∑ z, p z=1)
    (f g : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (E S A B : ℝ) (hA : 0<A) (hB : 0<B)
    (hE : ∑ z, p z*f z ≤ E) (hS : ∑ z, p z*g z ≤ S) :
    1-E/A-S/B ≤ ∑ z ∈ univ.filter (fun z => f z ≤ A ∧ g z ≤ B), p z := by
  have H := markov_complement p hp ht f g hf hg A B hA hB
  have H₁ := div_le_div_of_nonneg_right hE hA.le
  have H₂ := div_le_div_of_nonneg_right hS hB.le
  linarith

lemma retained_mem {k ℓ : ℕ} (S : Finset (Fin ℓ)) (h : k ≤ S.card) (i : Fin k) :
    retained S h i ∈ S := by
  exact S.orderEmbOfFin_mem rfl _

theorem coverage_selection {ℓ : ℕ} (good : Fin ℓ → Prop)
    (h : ((univ.filter (fun i => ¬good i)).card:ℝ) ≤ (ℓ:ℝ)/2) :
    ∃ e : Fin (ℓ/2) ↪o Fin ℓ, ∀ i, good (e i) := by
  let S := univ.filter good
  have he : S.card+(univ.filter (fun i => ¬good i)).card=ℓ := by
    simpa [S] using card_filter_add_card_filter_not (s := (univ : Finset (Fin ℓ))) good
  have hh : ℓ/2 ≤ S.card := by
    have h' : (ℓ:ℝ) ≤ 2*S.card := by
      have he' : (S.card:ℝ)+(univ.filter (fun i => ¬good i)).card=ℓ := by exact_mod_cast he
      linarith
    have hh' : ℓ ≤ 2*S.card := by exact_mod_cast h'
    omega
  refine ⟨retained S hh, fun i => ?_⟩
  exact (mem_filter.mp (retained_mem S hh i)).2
end
end SharpLogRamsey.SimultaneousExtraction

namespace SharpLogRamsey.HighRankAssembly
open scoped BigOperators
open Finset Classical HighRankDecoder HighRankCoverageProbability FiniteEventBounds
open FiniteMarginals
noncomputable section
variable {K Ω : Type*} [Field K] [Fintype K] [Fintype Ω]
variable {d : ℕ}
local notation "V" => (Fin (d+1) → K)
local notation "A" => Projectivization K (Module.Dual K V)
local notation "B" => Projectivization K V
local notation "q" => (Nat.card K : ℝ)

attribute [local instance] OAI.SharpLogRamsey.HighRankAssembly.flat_JoinedHighRankAssembly_6
attribute [local instance] OAI.SharpLogRamsey.HighRankAssembly.flat_JoinedHighRankAssembly_8
theorem low_hit_with_cutoff (hd : 2 ≤ d)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (M : ℝ) (hM : ∀ b, marginal w a b ≤ M)
    (p : B × A → ℝ) (hp : ∀ t, 0 ≤ p t)
    (good : B → Prop) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ y, good y → (∑ c, p (y,c)) ≤ N) :
    (∑ t, p t * indicator
      ((∑ z ∈ univ.filter (fun z => (a z).rep t.1.rep = 0), w z) < 2/(5*q))) ≤
    (∑ y ∈ univ.filter (fun y => ¬good y), ∑ c, p (y,c)) +
      100*q^(d+1)*M*N := by
  let p' : B × A → ℝ := fun t => if good t.1 then p t else 0
  have hdim : Module.finrank K V = (d-2)+3 := by simp; omega
  have HH := HighRankLowHit.low_hit_mass hdim w hw ht a M hM p' N hN0 (by
    intro y
    by_cases hy : good y
    · simpa [p',hy] using hN y hy
    · simpa [p',hy] using hN0)
  have he : (d-2)+3 = d+1 := by omega
  rw [he] at HH
  have H : (∑ t, p t * indicator
      ((∑ z ∈ univ.filter (fun z => (a z).rep t.1.rep = 0), w z) < 2/(5*q))) ≤
      (∑ y ∈ univ.filter (fun y => ¬good y), ∑ c, p (y,c)) +
      (∑ t, p' t * indicator
        ((∑ z ∈ univ.filter (fun z => (a z).rep t.1.rep = 0), w z) < 2/(5*q))) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro y _
    by_cases hy : good y
    · simp [p',hy]
    · simp only [hy,not_false_eq_true,ite_true,ite_false,p',zero_mul,sum_const_zero,add_zero]
      apply sum_le_sum
      intro c _
      unfold indicator
      split_ifs <;> simp [hp]
  exact H.trans (add_le_add_right HH _)

theorem coverage_source (hd : 2 ≤ d)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (b : Ω → B) (p : B × A → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hpt : ∑ t, p t = 1)
    (hincident : ∀ t, p t ≠ 0 → t.2.rep t.1.rep = 0)
    (U : Finset B) (hsupp : ∀ t, p t ≠ 0 → t.1 ∈ U)
    (good : B → Prop) (h r r' T : ℕ)
    (hr : 2 ≤ r) (hrd : r ≤ d) (hrank : d+2 ≤ r+r') (hhd : 2*d ≤ h)
    (C κ Ebad Eheavy I : ℝ) (hC : 0 ≤ C)
    (hfirst : ∀ x, marginal w a x ≤ C*Real.exp κ/q^r')
    (hsecond : ∀ y, marginal w b y ≤ C*Real.exp κ/q^r)
    (htarget : ∀ y, good y → (∑ c, p (y,c)) ≤ C*Real.exp κ/q^r)
    (hcard : (U.card:ℝ) ≤ C*q^r)
    (hbad : (∑ y ∈ univ.filter (fun y => ¬good y), ∑ c, p (y,c)) ≤ Ebad)
    (hheavy : (∑ t ∈ U ×ˢ univ, if Real.exp κ/q^d < p t then p t else 0) ≤ Eheavy)
    (hconflict : (∑ t, p t*conflictMass w (fun z => (a z).rep) b t.1 t.2) ≤ I)
    (hT : (T:ℝ) ≤ (h:ℝ)/(10*q)+1)
    (hescape : 20*C*Real.exp κ ≤ q) :
    (∑ t, p t*mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator (¬Admitted (fun z => (a z).rep) b z₁ z₂ r T t.1 t.2))) ≤
      Ebad + 100*C^2*Real.exp (2*κ)/q +
      (d*Real.exp (-3*(h:ℝ)/(20*d*q)) + Real.exp (1-(h:ℝ)/(10*q))) +
      2*h*I + Eheavy + 2*C*Real.exp κ/q := by
  have hq : 2 ≤ q := by exact_mod_cast Finite.one_lt_card (α := K)
  have hq0 : 0 < q := by linarith
  obtain ⟨e⟩ := HighRankBudgets.block_embedding h d r hrd
  have hdim : Module.finrank K V = d+1 := by simp
  have HC := HighRankAveraged.averaged_coverage w hw ht p hp hpt hincident U hsupp
    (fun z => (a z).rep) b h d r (h/d) T hdim hr hrd e
    (C*Real.exp κ/q^r) (Real.exp κ/q^d) (by positivity) (by positivity)
    (by intro y; simpa [marginal, sum_filter] using hsecond y) hT
  have HL := (low_hit_with_cutoff hd w hw ht a (C*Real.exp κ/q^r') hfirst
    p hp good (C*Real.exp κ/q^r) (by positivity) htarget).trans
    (add_le_add hbad (HighRankBudgets.low_hit_budget (by linarith : 1 ≤ q) hrank))
  have HG := HighRankBudgets.growth_tail hq
    (show 0 ≤ C*Real.exp κ/q^r by positivity) hrd (by omega : 0 < d) hhd
    (HighRankBudgets.atom_escape hq0 hr hescape)
  have HX : (if r < d then (U.card:ℝ)*(2*q^(d-r-1))*(Real.exp κ/q^d) else 0) ≤
      2*C*Real.exp κ/q := by
    split_ifs with hrd'
    · have he : q^d = q^r*q^(d-r-1)*q := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      calc
        _ ≤ (C*q^r)*(2*q^(d-r-1))*(Real.exp κ/q^d) := by gcongr
        _ = _ := by rw [he]; field_simp
    · positivity
  have HI := mul_le_mul_of_nonneg_left hconflict (show 0 ≤ 2*(h:ℝ) by positivity)
  linarith only [HC,HL,HG,HX,HI,hheavy]

theorem size_source (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (b : Ω → B) {h r T : ℕ} (hr : 0 < r) (hrd : r ≤ d)
    (X : Finset B) (hsupp : ∀ y, y ∉ X → marginal w b y = 0)
    (C κ u : ℝ) (hC : 0 < C) (hu : 0 < u) (huA : u ≤ 2*C*Real.exp κ)
    (hu20 : u ≤ 1/20) (hCu : 20*Real.exp (1/2)*u ≤ 1)
    (hcap : ∀ y ∈ X, marginal w b y ≤ C*Real.exp κ/q^r)
    (hcard : (X.card : ℝ) ≤ C*q^r)
    (hT : (h:ℝ)/(10*q) ≤ T) (hTn : d+2 ≤ T) (z₁ : Fin h → Ω) :
    (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂ *
      ((HighRankSize.domain (fun z => (a z).rep) b z₁ z₂ r T).card : ℝ)) ≤
      (10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*q^d) := by
  have HU : u ≤ 2*(C*Real.exp κ) := by nlinarith only [huA]
  have HS := HighRankSize.expected_domain (n := d+1) (by omega) hr (by omega)
    w hw ht (fun z => (a z).rep) b z₁ X hsupp (C*Real.exp κ) u
    (by positivity) hu HU hu20 hCu
    (by simpa only [Nat.card_eq_fintype_card] using hcap)
    (by simpa only [Nat.card_eq_fintype_card] using hT) hTn
  simp only [← Nat.card_eq_fintype_card, Nat.cast_add, Nat.cast_one] at HS
  have hn : d+1-r-1 = d-r := by omega
  have hp : q^r*q^(d-r)=q^d := by rw [← pow_add]; congr 1; omega
  apply HS.trans
  calc
    _ ≤ (10*(d+1)*(C*Real.exp κ)/u)^(d+1)*(C*q^r)*(1+2^(d+1+1))*(2*q^(d+1-r-1)) := by
      gcongr
    _ = _ := by
      rw [hn]
      rw [show d+1+1=d+2 by omega]
      calc
        _ = (10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*(q^r*q^(d-r))) := by ring
        _ = _ := by rw [hp]

end
end SharpLogRamsey.HighRankAssembly

namespace SharpLogRamsey.SimultaneousExtraction
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω R F : Type*} [Fintype Ω] [Fintype R] [Fintype F]

lemma independent_total (p : Ω → ℝ) (w : R → ℝ)
    (hp : ∑ x, p x = 1) (hw : ∑ z, w z = 1) :
    ∑ u, independentWeight p w u = 1 := by
  simp [independentWeight, Fintype.sum_prod_type, ← mul_sum, hp, hw]

omit [Fintype F] in
lemma missed_mean {ℓ : ℕ} (p : Ω → ℝ) (w : R → ℝ)
    (f : Ω → Fin ℓ → F) (D : R → Finset F) :
    (∑ u, independentWeight p w u * (missed f D u : ℝ)) =
      ∑ i, ∑ x, p x * ∑ z, w z * (if f x i ∉ D z then 1 else 0) := by
  have he (u : Ω × R) : (missed f D u : ℝ) =
      ∑ i : Fin ℓ, if f u.1 i ∉ D u.2 then (1:ℝ) else 0 := by
    rw [← sum_filter]
    simp only [missed, sum_const, nsmul_eq_mul, mul_one]
  simp_rw [he, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  simp [independentWeight]

omit [Fintype F] in
lemma domain_size_mean (p : Ω → ℝ) (w : R → ℝ) (hp : ∑ x, p x = 1)
    (D : R → Finset F) :
    (∑ u, independentWeight p w u * ((D u.2).card : ℝ)) =
      ∑ z, w z * ((D z).card : ℝ) := by
  simp [independentWeight, Fintype.sum_prod_type, mul_assoc, ← mul_sum,
    ← sum_mul, hp]

omit [Fintype F] in

theorem tuple_extraction {ℓ : ℕ} (hℓ : 0 < ℓ)
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hpt : ∑ x, p x = 1)
    (w : R → ℝ) (hw : ∀ z, 0 ≤ w z) (hwt : ∑ z, w z = 1)
    (f : Ω → Fin ℓ → F) (D : R → Finset F) (ε S : ℝ) (hS : 0 < S)
    (hcoverage : ∀ i, (∑ x, p x * ∑ z, w z *
      (if f x i ∉ D z then (1:ℝ) else 0)) ≤ ε)
    (hsize : (∑ z, w z * ((D z).card : ℝ)) ≤ S) :
    1-2*ε-1/4 ≤
      ∑ u ∈ univ.filter (fun u : Ω × R =>
        ((D u.2).card : ℝ) ≤ 4*S ∧
        ∃ e : Fin (ℓ/2) ↪o Fin ℓ, ∀ i, f u.1 (e i) ∈ D u.2),
        independentWeight p w u := by
  have hℓ' : (0:ℝ) < ℓ := by exact_mod_cast hℓ
  have hmean : (∑ u, independentWeight p w u * (missed f D u : ℝ)) ≤ ℓ*ε := by
    rw [missed_mean]
    simpa using sum_le_sum (fun i (_ : i∈univ) => hcoverage i)
  have HS := simultaneous_mass (independentWeight p w)
    (fun u => mul_nonneg (hp u.1) (hw u.2)) (independent_total p w hpt hwt)
    (fun u => (missed f D u : ℝ)) (fun u => ((D u.2).card : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (ℓ*ε) S (ℓ/2) (4*S) (by positivity) (by positivity) hmean
    (by rw [domain_size_mean p w hpt]; exact hsize)
  have he : 1-(ℓ:ℝ)*ε/((ℓ:ℝ)/2)-S/(4*S) = 1-2*ε-1/4 := by
    field_simp [hℓ'.ne',hS.ne']
  rw [he] at HS
  apply HS.trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro u hu
    obtain ⟨_,hf,hs⟩ := mem_filter.mp hu
    refine mem_filter.mpr ⟨mem_univ _, hs, ?_⟩
    apply coverage_selection (fun i => f u.1 i ∈ D u.2)
    convert hf using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    congr 1
    ext i
    simp
  · intro u _ _
    exact mul_nonneg (hp u.1) (hw u.2)
end
end SharpLogRamsey.SimultaneousExtraction

namespace SharpLogRamsey.HighRankAssembly
open scoped BigOperators Classical
open Finset HighRankDecoder HighRankCoverageProbability FiniteEventBounds
open FiniteMarginals SimultaneousExtraction
noncomputable section
variable {K Ω Ξ : Type*} [Field K] [Fintype K] [Fintype Ω] [Fintype Ξ]
variable {d : ℕ}
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1) → K))
local notation "B" => Projectivization K (Fin (d+1) → K)
local notation "q" => (Nat.card K : ℝ)

omit [Fintype Ξ] in
lemma row_pair_total (w : Ω → ℝ) (ht : ∑ z, w z = 1) (h : ℕ) :
    (∑ z : (Fin h → Ω) × (Fin h → Ω), ProductLaw.weight w z.1*ProductLaw.weight w z.2) = 1 := by
  have hnt : ∑ z : Fin h → Ω, ProductLaw.weight w z = 1 := by
    convert ProductLaw.total (ι := Fin h) w ht using 1
    all_goals try with_reducible_and_instances rfl
    congr!
  exact independent_total (ProductLaw.weight w) (ProductLaw.weight w) hnt hnt

attribute [local instance] OAI.SharpLogRamsey.HighRankAssembly.flat_JoinedHighRankAssembly_10
attribute [local instance] OAI.SharpLogRamsey.HighRankAssembly.flat_JoinedHighRankAssembly_11
lemma decoder_miss_mean (w : Ω → ℝ) (a : Ω → A) (b : Ω → B)
    (p : Ξ → ℝ) (f : Ξ → B × A) (h r T : ℕ) :
    (∑ x, p x * ∑ z : (Fin h → Ω) × (Fin h → Ω),
      (ProductLaw.weight w z.1*ProductLaw.weight w z.2) *
      (if f x ∉ HighRankSize.domain (fun z => (a z).rep) b z.1 z.2 r T then (1:ℝ) else 0)) =
    ∑ t, marginal p f t * mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator (¬Admitted (fun z => (a z).rep) b z₁ z₂ r T t.1 t.2)) := by
  rw [sum_marginal]
  apply sum_congr rfl
  intro x _
  congr 1
  simp [HighRankSize.domain, mean2, Fintype.sum_prod_type, indicator, mul_sum]

omit [Fintype Ξ] in
lemma row_pair_size (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (b : Ω → B) (h r T : ℕ) (S : ℝ)
    (hS : ∀ z₁ : Fin h → Ω, (∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂ *
      ((HighRankSize.domain (fun z => (a z).rep) b z₁ z₂ r T).card:ℝ)) ≤ S) :
    (∑ z : (Fin h → Ω) × (Fin h → Ω),
      (ProductLaw.weight w z.1*ProductLaw.weight w z.2) *
      ((HighRankSize.domain (fun z => (a z).rep) b z.1 z.2 r T).card:ℝ)) ≤ S := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ z₁ : Fin h → Ω, ProductLaw.weight w z₁ *
        ∑ z₂ : Fin h → Ω, ProductLaw.weight w z₂ *
          ((HighRankSize.domain (fun z => (a z).rep) b z₁ z₂ r T).card:ℝ) := by
      simp only [mul_sum, mul_assoc]
    _ ≤ ∑ z₁ : Fin h → Ω, ProductLaw.weight w z₁ *S :=
      sum_le_sum (fun z₁ _ => mul_le_mul_of_nonneg_left (hS z₁) (ProductLaw.nonneg w hw z₁))
    _ = S := by
      have hnt : ∑ z : Fin h → Ω, ProductLaw.weight w z = 1 := by
        convert ProductLaw.total (ι := Fin h) w ht using 1
        all_goals try with_reducible_and_instances rfl
        congr!
      rw [← sum_mul, hnt, one_mul]

theorem extraction_source (hd : 2 ≤ d) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → A) (b : Ω → B)
    (p : Ξ → ℝ) (hp : ∀ x, 0 ≤ p x) (hpt : ∑ x, p x = 1)
    (f : Ξ → Fin ℓ → B × A)
    (U : Fin ℓ → Finset B) (good : Fin ℓ → B → Prop)
    (h r r' T : ℕ) (hr : 2 ≤ r) (hrd : r ≤ d)
    (hrank : d+2 ≤ r+r') (hhd : 2*d ≤ h)
    (C κ u Ebad Eheavy I : ℝ) (hC : 0 < C)
    (hu : 0 < u) (huA : u ≤ 2*C*Real.exp κ)
    (hu20 : u ≤ 1/20) (hCu : 20*Real.exp (1/2)*u ≤ 1)
    (hfirst : ∀ x, marginal w a x ≤ C*Real.exp κ/q^r')
    (hsecond : ∀ y, marginal w b y ≤ C*Real.exp κ/q^r)
    (X : Finset B) (hX : ∀ y, y ∉ X → marginal w b y = 0)
    (hXcard : (X.card:ℝ) ≤ C*q^r)
    (hincident : ∀ i t, marginal p (fun x => f x i) t ≠ 0 → t.2.rep t.1.rep = 0)
    (hsupp : ∀ i t, marginal p (fun x => f x i) t ≠ 0 → t.1 ∈ U i)
    (htarget : ∀ i y, good i y → (∑ c, marginal p (fun x => f x i) (y,c)) ≤ C*Real.exp κ/q^r)
    (hcard : ∀ i, ((U i).card:ℝ) ≤ C*q^r)
    (hbad : ∀ i, (∑ y ∈ univ.filter (fun y => ¬good i y),
      ∑ c, marginal p (fun x => f x i) (y,c)) ≤ Ebad)
    (hheavy : ∀ i, (∑ t ∈ (U i) ×ˢ univ,
      if Real.exp κ/q^d < marginal p (fun x => f x i) t
      then marginal p (fun x => f x i) t else 0) ≤ Eheavy)
    (hconflict : ∀ i, (∑ t, marginal p (fun x => f x i) t *
      conflictMass w (fun z => (a z).rep) b t.1 t.2) ≤ I)
    (hTlo : (h:ℝ)/(10*q) ≤ T) (hThi : (T:ℝ) ≤ (h:ℝ)/(10*q)+1)
    (hTn : d+2 ≤ T) (hescape : 20*C*Real.exp κ ≤ q) :
    let S := (10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*q^d)
    let E := Ebad + 100*C^2*Real.exp (2*κ)/q +
      (d*Real.exp (-3*(h:ℝ)/(20*d*q)) + Real.exp (1-(h:ℝ)/(10*q))) +
      2*h*I + Eheavy + 2*C*Real.exp κ/q
    let W := fun z : (Fin h → Ω) × (Fin h → Ω) => ProductLaw.weight w z.1*ProductLaw.weight w z.2
    let D := fun z : (Fin h → Ω) × (Fin h → Ω) => HighRankSize.domain (fun z => (a z).rep) b z.1 z.2 r T
    1-2*E-1/4 ≤
      ∑ v ∈ univ.filter (fun v : Ξ × ((Fin h → Ω) × (Fin h → Ω)) =>
        ((D v.2).card:ℝ) ≤ 4*S ∧
        ∃ e : Fin (ℓ/2) ↪o Fin ℓ, ∀ i, f v.1 (e i) ∈ D v.2),
        p v.1*W v.2 := by
  dsimp only
  let W := fun z : (Fin h → Ω) × (Fin h → Ω) => ProductLaw.weight w z.1*ProductLaw.weight w z.2
  let D := fun z : (Fin h → Ω) × (Fin h → Ω) => HighRankSize.domain (fun z => (a z).rep) b z.1 z.2 r T
  have hW : ∀ z, 0 ≤ W z := fun z => mul_nonneg (ProductLaw.nonneg w hw z.1) (ProductLaw.nonneg w hw z.2)
  have hWt : ∑ z, W z = 1 := row_pair_total w ht h
  have hq : 0 < q := by exact_mod_cast Nat.card_pos (α := K)
  have hpos : 0 < ((10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*q^d)) := by
    positivity
  have HX := tuple_extraction hℓ p hp hpt W hW hWt f D
    (Ebad + 100*C^2*Real.exp (2*κ)/q +
      (d*Real.exp (-3*(h:ℝ)/(20*d*q)) + Real.exp (1-(h:ℝ)/(10*q))) +
      2*h*I + Eheavy + 2*C*Real.exp κ/q)
    ((10*(d+1)*C*Real.exp κ/u)^(d+1)*C*(1+2^(d+2))*(2*q^d)) hpos
  refine (HX ?_ ?_).trans ?_
  · intro i
    have HC := coverage_source hd w hw ht a b (marginal p (fun x => f x i))
      (marginal_nonneg p hp _) (by rw [marginal_total]; exact hpt)
      (hincident i) (U i) (hsupp i) (good i) h r r' T hr hrd hrank hhd C κ Ebad Eheavy I hC.le
      hfirst hsecond (htarget i) (hcard i) (hbad i) (hheavy i) (hconflict i) hThi hescape
    have Hmean := (decoder_miss_mean w a b p (fun x => f x i) h r T).le.trans HC
    convert Hmean using 1
    all_goals try with_reducible_and_instances rfl
    congr!
  · apply row_pair_size w hw ht a b h r T
    intro z₁
    exact size_source w hw ht a b (by omega) hrd X hX C κ u hC hu huA hu20 hCu
      (fun y _ => hsecond y) hXcard hTlo hTn z₁
  · apply le_of_eq
    congr!
end
end SharpLogRamsey.HighRankAssembly

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

lemma Law.support_card_pos (p : Law A) (S : Finset A)
    (hs : ∀ a,a∉S→p.mass a=0) : 0<S.card := by
  by_contra h
  have he : S=∅ := card_eq_zero.mp (by omega)
  have hz : ∑ a,p.mass a=0 := sum_eq_zero (fun a _=>hs a (by simp [he]))
  linarith [p.total]

lemma entropy_snd_fiber_lower (p : Law (A×B)) (S : Finset (A×B))
    (hs : ∀ z,z∉S→p.mass z=0) (T : ℝ) (hT : 0<T)
    (hcard : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤T) :
    entropy p-log T≤entropy p.snd := by
  have he : ∑ b,p.snd.mass b*entropy (p.condFst b)≤log T := by
    calc
      _ ≤ ∑ b,p.snd.mass b*log T := by
        apply sum_le_sum
        intro b _
        by_cases hb : p.snd.mass b=0
        · simp [hb]
        have hsup : ∀ a,a∉univ.filter (fun a=>(a,b)∈S)→(p.condFst b).mass a=0 := by
          intro a ha
          rw [Law.condFst_mass _ _ hb,hs (a,b) (by simpa using ha),zero_div]
        have hp : (0:ℝ)<(univ.filter (fun a=>(a,b)∈S)).card := by
          exact_mod_cast (p.condFst b).support_card_pos _ hsup
        exact mul_le_mul_of_nonneg_left
          ((entropy_le_log_card (p.condFst b) _ hsup).trans ((log_le_log_iff hp hT).2 (hcard b)))
          (p.snd.nonneg b)
      _ = log T := by rw [←sum_mul,p.snd.total,one_mul]
  linarith [entropy_chain p]

lemma entropy_fst_fiber_lower (p : Law (A×B)) (S : Finset (A×B))
    (hs : ∀ z,z∉S→p.mass z=0) (T : ℝ) (hT : 0<T)
    (hcard : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤T) :
    entropy p-log T≤entropy p.fst := by
  have hh:=entropy_snd_fiber_lower p.swap (S.image Prod.swap) (by
    rintro ⟨b,a⟩ hz
    exact hs (a,b) (fun ha=>hz (mem_image.mpr ⟨(a,b),ha,rfl⟩))) T hT (by
      intro a
      have he : univ.filter (fun b=>(b,a)∈S.image Prod.swap)=univ.filter (fun b=>(a,b)∈S) := by
        ext b
        simp only [mem_filter,mem_univ,true_and]
        constructor
        · intro hb
          obtain ⟨⟨x,y⟩,hh,heq⟩:=mem_image.mp hb
          have hx : x=a := congrArg Prod.snd heq
          have hy : y=b := congrArg Prod.fst heq
          simpa only [hx,hy] using hh
        · intro hb; exact mem_image.mpr ⟨(a,b),hb,rfl⟩
      rw [he]
      exact hcard a)
  simpa only [entropy_swap,Law.swap_snd] using hh

lemma Law.event_not_and (p : Law A) (P Q : A→Prop) :
    p.event (univ.filter (fun a=>¬(P a∧Q a)))≤
      p.event (univ.filter (fun a=>¬P a))+p.event (univ.filter (fun a=>¬Q a)) := by
  simp only [Law.event,sum_filter,←sum_add_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq,p.nonneg]

theorem high_second_upper_mass (p : Law (A×B)) (S : Finset (A×B))
    (DB : Finset B) (hs : ∀ z,z∉S→p.mass z=0)
    (hb : ∀ b,b∉DB→p.snd.mass b=0) (T L₀ κ : ℝ) (hT : 0<T) (hκ : 0<κ)
    (hcard : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤T) :
    p.snd.event (univ.filter (fun b=>exp (κ-L₀)<p.snd.mass b))≤
      (L₀+log T-entropy p+DB.card*exp (-L₀))/κ := by
  exact (p.snd.heavy_atoms DB hb L₀ hκ).trans
    (div_le_div_of_nonneg_right (by linarith [entropy_snd_fiber_lower p S hs T hT hcard]) hκ.le)

theorem high_first_upper_mass (p : Law (A×B)) (S : Finset (A×B))
    (DA : Finset A) (hs : ∀ z,z∉S→p.mass z=0)
    (ha : ∀ a,a∉DA→p.fst.mass a=0) (T L₀ κ : ℝ) (hT : 0<T) (hκ : 0<κ)
    (hcard : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤T) :
    p.fst.event (univ.filter (fun a=>exp (κ-L₀)<p.fst.mass a))≤
      (L₀+log T-entropy p+DA.card*exp (-L₀))/κ := by
  exact (p.fst.heavy_atoms DA ha L₀ hκ).trans
    (div_le_div_of_nonneg_right (by linarith [entropy_fst_fiber_lower p S hs T hT hcard]) hκ.le)

theorem high_second_bad (p : Law (A×B)) (S : Finset (A×B)) (DB : Finset B)
    (hs : ∀ z,z∉S→p.mass z=0) (hb : ∀ b,b∉DB→p.snd.mass b=0)
    (M L L₀ κ T : ℝ) (hM : 0<M) (hκ : 0<κ) (hT : 0<T)
    (hB : (DB.card:ℝ)≤M)
    (hcard : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤T) :
    p.snd.event (univ.filter (fun b=>¬highGoodSecond p M L κ (exp (κ-L₀)) b))≤
      exp (-κ)+(L-entropy p+S.card*exp (-L))/(κ*(1/50))+
        (L₀+log T-entropy p+DB.card*exp (-L₀))/κ := by
  unfold highGoodSecond
  convert (p.snd.event_not_and (goodSecond p M L κ (1/50)) (fun b=>p.snd.mass b≤exp (κ-L₀))).trans (add_le_add
    (badSecond_mass p S hs DB hb M L κ (1/50) hM hB hκ (by norm_num))
    (by simpa only [not_le] using high_second_upper_mass p S DB hs hb T L₀ κ hT hκ hcard)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact filter_congr_decidable _ _ _

theorem high_first_bad (p : Law (A×B)) (S : Finset (A×B)) (DA : Finset A)
    (hs : ∀ z,z∉S→p.mass z=0) (ha : ∀ a,a∉DA→p.fst.mass a=0)
    (M L L₀ κ T : ℝ) (hM : 0<M) (hκ : 0<κ) (hT : 0<T)
    (hA : (DA.card:ℝ)≤M)
    (hcard : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤T) :
    p.fst.event (univ.filter (fun a=>¬highGoodFirst p M L κ (exp (κ-L₀)) a))≤
      exp (-κ)+(L-entropy p+S.card*exp (-L))/(κ*(1/50))+
        (L₀+log T-entropy p+DA.card*exp (-L₀))/κ := by
  unfold highGoodFirst
  convert (p.fst.event_not_and (goodFirst p M L κ (1/50)) (fun a=>p.fst.mass a≤exp (κ-L₀))).trans (add_le_add
    (badFirst_mass p S hs DA ha M L κ (1/50) hM hA hκ (by norm_num))
    (by simpa only [not_le] using high_first_upper_mass p S DA hs ha T L₀ κ hT hκ hcard)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact filter_congr_decidable _ _ _
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]

lemma Law.onEvent_mean_le_two (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→ℝ) (hf : ∀ x,0≤f x) :
    ∑ x : E,(p.onEvent E (by linarith)).mass x*f x≤2*∑ x,p.mass x*f x := by
  rw [p.onEvent_mean]
  apply (div_le_iff₀ (by linarith : 0<p.event E)).mpr
  have hn : 0≤∑ x,p.mass x*f x := sum_nonneg (fun x _=>mul_nonneg (p.nonneg x) (hf x))
  calc
    _ ≤ ∑ x,p.mass x*f x := sum_le_univ_sum_of_nonneg (fun x=>mul_nonneg (p.nonneg x) (hf x))
    _ ≤ _ := by nlinarith

lemma Law.map_mass_eq_marginal (p : Law X) (f : X→Y) (y : Y) :
    (p.map f).mass y=FiniteMarginals.marginal p.mass f y := by
  simp only [Law.map,FiniteMarginals.marginal,sum_filter]

lemma Law.onEvent_map_le_two (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→Y) (y : Y) :
    ((p.onEvent E (by linarith)).map (fun x : E=>f x)).mass y≤2*(p.map f).mass y := by
  have hh:=p.onEvent_mean_le_two E hE (fun x=>if f x=y then 1 else 0) (by intro x; split_ifs <;> positivity)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using hh

lemma good_pair_event (p : Law (A×B)) (PA : A→Prop) (PB : B→Prop) (εA εB : ℝ)
    (hA : p.fst.event (univ.filter (fun a=>¬PA a))≤εA)
    (hB : p.snd.event (univ.filter (fun b=>¬PB b))≤εB) :
    1-εA-εB≤p.event (univ.filter (fun z=>PA z.1∧PB z.2)) := by
  have he : 1-p.event (univ.filter (fun z=>PA z.1∧PB z.2)) =
      p.event (univ.filter (fun z=>¬(PA z.1∧PB z.2))) := by
    simp only [Law.event,sum_filter]
    rw [←p.total,←sum_sub_distrib]
    apply sum_congr rfl
    intro z _
    by_cases h : PA z.1∧PB z.2 <;> simp [h]
  have hh:=p.event_not_and (fun z=>PA z.1) (fun z=>PB z.2)
  have ha : p.event (univ.filter (fun z=>¬PA z.1))=p.fst.event (univ.filter (fun a=>¬PA a)) := by
    have hh:=p.sum_map Prod.fst (fun a=>if ¬PA a then 1 else 0)
    rw [Law.map_fst] at hh
    simpa only [Law.event,sum_filter,mul_ite,mul_one,mul_zero] using hh.symm
  have hb : p.event (univ.filter (fun z=>¬PB z.2))=p.snd.event (univ.filter (fun b=>¬PB b)) := by
    have hh:=p.sum_map Prod.snd (fun b=>if ¬PB b then 1 else 0)
    rw [Law.map_snd] at hh
    simpa only [Law.event,sum_filter,mul_ite,mul_one,mul_zero] using hh.symm
  rw [ha,hb] at hh
  linarith

lemma Law.onEvent_map_cap (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→Y) (U : ℝ) (hU : 0≤U)
    (hcap : ∀ x∈E,(p.map f).mass (f x)≤U) (y : Y) :
    ((p.onEvent E (by linarith)).map (fun x : E=>f x)).mass y≤2*U := by
  by_cases hy : ((p.onEvent E (by linarith)).map (fun x : E=>f x)).mass y=0
  · rw [hy]; positivity
  obtain ⟨x,hx,he⟩:=(p.onEvent E (by linarith)).map_support (fun x : E=>f x) y hy
  have hh:=p.onEvent_map_le_two E hE f y
  rw [←he] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_left (hcap x x.property) (by norm_num))

theorem high_good_rows (p : Law (A×B)) (MA MB L κ UA UB ε : ℝ)
    (hUA : 0≤UA) (hUB : 0≤UB) (hε : ε≤1/4)
    (hA : p.fst.event (univ.filter (fun a=>¬highGoodFirst p MA L κ UA a))≤ε)
    (hB : p.snd.event (univ.filter (fun b=>¬highGoodSecond p MB L κ UB b))≤ε) :
    let E:=univ.filter (fun z : A×B=>highGoodFirst p MA L κ UA z.1∧highGoodSecond p MB L κ UB z.2)
    ∃ hE : (1:ℝ)/2≤p.event E,
      (∀ a,FiniteMarginals.marginal (p.onEvent E (by linarith)).mass (fun z=>z.val.1) a≤2*UA) ∧
      (∀ b,FiniteMarginals.marginal (p.onEvent E (by linarith)).mass (fun z=>z.val.2) b≤2*UB) ∧
      (∀ f : A×B→ℝ,(∀ z,0≤f z)→
        (∑ z : E,(p.onEvent E (by linarith)).mass z*f z)≤2*∑ z,p.mass z*f z) := by
  let E:=univ.filter (fun z : A×B=>highGoodFirst p MA L κ UA z.1∧highGoodSecond p MB L κ UB z.2)
  have hE : (1:ℝ)/2≤p.event E := by
    have hh:=good_pair_event p _ _ ε ε hA hB
    change 1-ε-ε≤p.event E at hh
    linarith
  refine ⟨hE,?_,?_,fun f hf=>p.onEvent_mean_le_two E hE f hf⟩
  · intro a
    rw [←Law.map_mass_eq_marginal]
    apply p.onEvent_map_cap E hE Prod.fst UA hUA
    intro z hz
    rw [Law.map_fst]
    exact (mem_filter.mp hz).2.1.2
  · intro b
    rw [←Law.map_mass_eq_marginal]
    apply p.onEvent_map_cap E hE Prod.snd UB hUB
    intro z hz
    rw [Law.map_snd]
    exact (mem_filter.mp hz).2.2.2
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

lemma Law.map_image_support {A B : Type*} [Fintype A] [Fintype B]
    (p : Law A) (S : Finset A) (f : A→B)
    (hS : ∀ a,a∉S→p.mass a=0) :
    ∀ b,b∉S.image f→(p.map f).mass b=0 := by
  intro b hb
  by_contra he
  obtain ⟨a,ha,rfl⟩:=p.map_support f b he
  exact hb (mem_image.mpr ⟨a,by by_contra h; exact ha (hS a h),rfl⟩)

lemma reciprocal_source_scales {σ β D : ℝ} (hσ : 0<σ) (hD : σ^β≤D) :
    σ^(4*β)≤D*σ^(3*β) ∧ D*σ^β≤(D*σ^(3*β))*σ^(-2*β) := by
  constructor
  · calc
      _ = σ^β*σ^(3*β) := by rw [←rpow_add hσ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (rpow_nonneg hσ.le _)
  · rw [mul_assoc,←rpow_add hσ,show 3*β+-2*β=β by ring]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_HighRankScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

lemma high_upper_error_scale {x b κ δ H L₀ T N C : ℝ}
    (hx : 1≤x) (hb : 0≤b) (hC : 0≤C) (hκ : x^(4*b)≤κ)
    (hδ : δ≤κ*x^(-2*b)) (hnum : L₀+log T-H+N*exp (-L₀)≤δ+C) :
    (L₀+log T-H+N*exp (-L₀))/κ≤(1+C)*x^(-2*b) := by
  have hx0 : 0<x := by linarith
  have hp : 0<x^(2*b) := rpow_pos_of_pos hx0 _
  have hk : x^(2*b)≤κ := (rpow_le_rpow_of_exponent_le hx (by linarith)).trans hκ
  have hk0 : 0<κ := hp.trans_le hk
  have hi : 1/κ≤x^(-2*b) := by
    have hh:=one_div_le_one_div_of_le hp hk
    simpa only [neg_mul,rpow_neg hx0.le,one_div] using hh
  have hd : δ/κ≤x^(-2*b) := (div_le_iff₀ hk0).mpr (by simpa only [mul_comm κ] using hδ)
  calc
    _ ≤ (δ+C)/κ := div_le_div_of_nonneg_right hnum hk0.le
    _ = δ/κ+C*(1/κ) := by ring
    _ ≤ x^(-2*b)+C*x^(-2*b) := add_le_add hd (mul_le_mul_of_nonneg_left hi hC)
    _ = _ := by ring

variable {A B : Type*} [Fintype A] [Fintype B]

theorem actual_high_endpoint_errors (p : Law (A×B)) (S : Finset (A×B))
    (σ β D d r r' : ℝ) (hσ : 1≤σ) (hβ : 0≤β) (hD : σ^β≤D)
    (hs : ∀ z,z∉S→p.mass z=0)
    (hA : ((S.image Prod.fst).card:ℝ)≤1024*exp (r'*σ))
    (hB : ((S.image Prod.snd).card:ℝ)≤1024*exp (r*σ))
    (hS : (S.card:ℝ)≤64*exp (d*σ))
    (hfA : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤2*exp ((d-r')*σ))
    (hfB : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤2*exp ((d-r)*σ))
    (hdef : d*σ-entropy p≤D*σ^β) :
    let κ:=D*σ^(3*β)
    p.fst.event (univ.filter (fun a=>¬highGoodFirst p (1024*exp (r'*σ)) (d*σ) κ (exp (κ-r'*σ)) a))≤4300*σ^(-2*β) ∧
    p.snd.event (univ.filter (fun b=>¬highGoodSecond p (1024*exp (r*σ)) (d*σ) κ (exp (κ-r*σ)) b))≤4300*σ^(-2*β) ∧
    p.event (univ.filter (fun z=>exp (κ-d*σ)<p.mass z))≤65*σ^(-2*β) := by
  dsimp only
  have hσ0 : 0<σ := by linarith
  have hsc:=reciprocal_source_scales hσ0 hD
  have hk : 0<D*σ^(3*β) := (rpow_pos_of_pos hσ0 _).trans_le hsc.1
  have ha:=p.map_image_support S Prod.fst hs
  have hb:=p.map_image_support S Prod.snd hs
  rw [Law.map_fst] at ha
  rw [Law.map_snd] at hb
  have cap {N L : ℝ} (h : N≤64*exp L) : N*exp (-L)≤64 := by
    calc
      _ ≤ (64*exp L)*exp (-L) := mul_le_mul_of_nonneg_right h (exp_nonneg _)
      _ = _ := by rw [mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one]
  have cap' {N L : ℝ} (h : N≤1024*exp L) : N*exp (-L)≤1024 := by
    calc
      _ ≤ (1024*exp L)*exp (-L) := mul_le_mul_of_nonneg_right h (exp_nonneg _)
      _ = _ := by rw [mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one]
  have hcS:=cap hS
  have he:=endpoint_error_scale hσ hβ (by norm_num : (0:ℝ)≤64) hsc.1 hsc.2 hdef hcS
  have up (v : ℝ) (N : ℝ) (hN : N≤1024*exp (v*σ)) :
      (v*σ+log (2*exp ((d-v)*σ))-entropy p+N*exp (-(v*σ)))/(D*σ^(3*β))≤1027*σ^(-2*β) := by
    have hn : v*σ+log (2*exp ((d-v)*σ))-entropy p+N*exp (-(v*σ))≤D*σ^β+1026 := by
      rw [log_mul (by norm_num) (exp_ne_zero _),log_exp]
      have hl : log (2:ℝ)≤2 := (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      linarith [cap' hN]
    convert high_upper_error_scale hσ hβ (by norm_num : (0:ℝ)≤1026) hsc.1 hsc.2 hn using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have heA:=high_first_bad p S (S.image Prod.fst) hs ha (1024*exp (r'*σ)) (d*σ) (r'*σ)
    (D*σ^(3*β)) (2*exp ((d-r')*σ)) (by positivity) hk (by positivity) hA hfA
  have heB:=high_second_bad p S (S.image Prod.snd) hs hb (1024*exp (r*σ)) (d*σ) (r*σ)
    (D*σ^(3*β)) (2*exp ((d-r)*σ)) (by positivity) hk (by positivity) hB hfB
  have hx : 0≤σ^(-2*β) := rpow_nonneg hσ0.le _
  refine ⟨?_,?_,?_⟩
  · linarith [up r' (S.image Prod.fst).card hA]
  · linarith [up r (S.image Prod.snd).card hB]
  · have hh:=p.heavy_atoms S hs (d*σ) hk
    have hm:=high_upper_error_scale (T:=1) (L₀:=d*σ) hσ hβ (by norm_num : (0:ℝ)≤64)
      hsc.1 hsc.2 (show d*σ+log 1-entropy p+S.card*exp (-(d*σ))≤D*σ^β+64 by simp only [log_one,add_zero]; linarith)
    simp only [log_one,add_zero] at hm
    norm_num only at hm
    exact hh.trans hm
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_HighRankExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real FiniteMarginals HighRankCoverageProbability FiniteEventBounds
open scoped Classical BigOperators
noncomputable section

variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
lemma Law.swap_map_marginal (p : Law X) (f : X→A×B) (a : A) (b : B) :
    FiniteMarginals.marginal p.mass (fun x=>(f x).swap) (b,a)=(p.map f).mass (a,b) := by
  simp only [FiniteMarginals.marginal,Law.map,sum_filter]
  apply sum_congr rfl
  intro x _
  have he : (f x).swap=(b,a) ↔ f x=(a,b) := by
    rcases f x with ⟨c,d⟩
    simp only [Prod.swap_prod_mk,Prod.mk.injEq,and_comm]
  simp only [he]
  split_ifs <;> rfl
end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection FiniteMarginals HighRankCoverageProbability FiniteEventBounds HighRankAssembly
open scoped Classical BigOperators
noncomputable section
variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1)→K))
local notation "B" => Projectivization K (Fin (d+1)→K)
local notation "q" => (Nat.card K:ℝ)

attribute [local instance] OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankExtraction_2
attribute [local instance] OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankExtraction_3
theorem extraction (hd : 2≤d) {ℓ : ℕ} (hℓ : 0<ℓ)
    (s : Law (A×B)) (S : Finset (A×B))
    (p : Law Ξ) (f : Ξ→Fin ℓ→A×B) (U : Fin ℓ→Finset (A×B))
    (σ β D : ℝ) (hσ : 1≤σ) (hβ : 0≤β) (hlog : log q=σ) (hD : σ^β≤D)
    (h r r' T : ℕ) (hr : 2 ≤ r) (hrd : r≤d) (hrank : d+2 ≤ r+r') (hhd : 2*d≤h)
    (u I : ℝ) (hu : 0<u) (huA : u≤2048*exp (D*σ^(3*β)))
    (hu20 : u≤1/20) (hCu : 20*exp (1/2)*u≤1)
    (hsmall : 4300*σ^(-2*β)≤1/4)
    (hs : ∀ z,z∉S→s.mass z=0)
    (hSA : ((S.image Prod.fst).card:ℝ)≤1024*q^r')
    (hSB : ((S.image Prod.snd).card:ℝ)≤1024*q^r)
    (hS : (S.card:ℝ)≤64*q^d)
    (hsfA : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ))
    (hsfB : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ))
    (hsdef : (d:ℝ)*σ-entropy s≤D*σ^β)
    (hp : ∀ x,p.mass x≠0→∀ i,f x i∈U i)
    (hinc : ∀ x,p.mass x≠0→∀ i,(f x i).1.rep (f x i).2.rep=0)
    (hUA : ∀ i,(((U i).image Prod.fst).card:ℝ)≤1024*q^r')
    (hUB : ∀ i,(((U i).image Prod.snd).card:ℝ)≤1024*q^r)
    (hU : ∀ i,((U i).card:ℝ)≤64*q^d)
    (hufA : ∀ i a,((univ.filter (fun b=>(a,b)∈U i)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ))
    (hufB : ∀ i b,((univ.filter (fun a=>(a,b)∈U i)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ))
    (hdef : ∀ i,(d:ℝ)*σ-entropy (p.map (fun x=>f x i))≤D*σ^β)
    (hconflict : ∀ i,(∑ x,p.mass x*∑ z,s.mass z*
      indicator (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0))≤I)
    (hTlo : (h:ℝ)/(10*q)≤T) (hThi : (T:ℝ)≤(h:ℝ)/(10*q)+1)
    (hTn : d+2≤T) (hescape : 20480*exp (D*σ^(3*β))≤q) :
    let κ:=D*σ^(3*β)
    let E:=univ.filter (fun z : A×B=>
      highGoodFirst s (1024*q^r') ((d:ℝ)*σ) κ (exp (κ-(r':ℝ)*σ)) z.1 ∧
      highGoodSecond s (1024*q^r) ((d:ℝ)*σ) κ (exp (κ-(r:ℝ)*σ)) z.2)
    ∃ hE : (1:ℝ)/2≤ s.event E,
      let w:=(s.onEvent E (by linarith)).mass
      let Sz:=(10*(d+1)*1024*exp κ/u)^(d+1)*1024*(1+2^(d+2))*(2*q^d)
      let err:=4365*σ^(-2*β)+100*1024^2*exp (2*κ)/q+
        (d*exp (-3*(h:ℝ)/(20*d*q))+exp (1-(h:ℝ)/(10*q)))+4*h*I+2048*exp κ/q
      let W:=fun z : (Fin h→E)×(Fin h→E)=>ProductLaw.weight w z.1*ProductLaw.weight w z.2
      let DD:=fun z : (Fin h→E)×(Fin h→E)=>HighRankSize.domain (fun z : E=>z.val.1.rep)
        (fun z : E=>z.val.2) z.1 z.2 r T
      1-2*err-1/4≤∑ v∈univ.filter (fun v : Ξ×((Fin h→E)×(Fin h→E))=>
        ((DD v.2).card:ℝ)≤4*Sz ∧ ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,(f v.1 (e i)).swap∈DD v.2),
        p.mass v.1*W v.2 := by
  dsimp only
  let κ:=D*σ^(3*β)
  have hq : 0<q := by exact_mod_cast Nat.card_pos (α:=K)
  have he (j : ℕ) : exp ((j:ℝ)*σ)=q^j := by rw [←hlog,exp_nat_mul,exp_log hq]
  have hm:=actual_high_endpoint_errors s S σ β D d r r' hσ hβ hD hs
    (by simpa only [he] using hSA) (by simpa only [he] using hSB)
    (by simpa only [he] using hS) hsfA hsfB hsdef
  dsimp only at hm
  simp only [he] at hm
  let E:=univ.filter (fun z : A×B=>
    highGoodFirst s (1024*q^r') ((d:ℝ)*σ) κ (exp (κ-(r':ℝ)*σ)) z.1 ∧
    highGoodSecond s (1024*q^r) ((d:ℝ)*σ) κ (exp (κ-(r:ℝ)*σ)) z.2)
  obtain ⟨hE,hfirst,hsecond,hmean⟩:=high_good_rows s (1024*q^r') (1024*q^r) ((d:ℝ)*σ) κ
    (exp (κ-(r':ℝ)*σ)) (exp (κ-(r:ℝ)*σ)) (4300*σ^(-2*β))
    (exp_nonneg _) (exp_nonneg _) hsmall hm.1 hm.2.1
  change (1:ℝ)/2≤ s.event E at hE
  refine ⟨hE,?_⟩
  let row:=s.onEvent E (by linarith : 0 < s.event E)
  let tp:=fun i=>p.map (fun x=>f x i)
  have hsup i : ∀ z,z∉U i→(tp i).mass z=0 := by
    intro z hz
    by_contra hh
    obtain ⟨x,hx,heq⟩:=p.map_support (fun x=>f x i) z hh
    exact hz (heq ▸ hp x hx i)
  have htarg i:=actual_high_endpoint_errors (tp i) (U i) σ β D d r r' hσ hβ hD (hsup i)
    (by simpa only [he] using hUA i) (by simpa only [he] using hUB i)
    (by simpa only [he] using hU i) (hufA i) (hufB i) (hdef i)
  dsimp only at htarg
  simp only [he] at htarg
  let good:=fun i b=>highGoodSecond (tp i) (1024*q^r) ((d:ℝ)*σ) κ (exp (κ-(r:ℝ)*σ)) b
  have hsw i a b : FiniteMarginals.marginal p.mass (fun x=>(f x i).swap) (b,a)=(tp i).mass (a,b) :=
    p.swap_map_marginal _ a b
  have hsum i b : (∑ a,FiniteMarginals.marginal p.mass (fun x=>(f x i).swap) (b,a))=(tp i).snd.mass b := by
    simp only [hsw]
    rfl
  have hcap (j : ℕ) : 2*exp (κ-(j:ℝ)*σ)≤1024*exp κ/q^j := by
    rw [exp_sub,he]
    have hp0 : 0≤exp κ/q^j := by positivity
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤1024) hp0
  have HC:=extraction_source hd hℓ row.mass row.nonneg row.total
    (fun z : E=>z.val.1) (fun z : E=>z.val.2) p.mass p.nonneg p.total
    (fun x i=>(f x i).swap) (fun i=>(U i).image Prod.snd) good h r r' T hr hrd hrank hhd
    1024 κ u (4300*σ^(-2*β)) (65*σ^(-2*β)) (2*I) (by norm_num) hu
    (by simpa only [show (2:ℝ)*1024=2048 by norm_num] using huA) hu20 hCu
    (fun a=>(hfirst a).trans (hcap r')) (fun b=>(hsecond b).trans (hcap r))
    (S.image Prod.snd) ?_ hSB ?_ ?_ ?_ hUB ?_ ?_ ?_ hTlo hThi hTn
    (by simpa only [show (20:ℝ)*1024=20480 by norm_num] using hescape)
  · convert HC using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [κ]
    ring
  · intro b hb
    have hzero:=s.map_image_support S Prod.snd hs b hb
    rw [Law.map_snd] at hzero
    have hh:=s.onEvent_map_le_two E hE Prod.snd b
    rw [Law.map_snd,hzero,mul_zero,row.map_mass_eq_marginal] at hh
    exact le_antisymm hh (marginal_nonneg row.mass row.nonneg _ b)
  · intro i ⟨b,a⟩ hmass
    rw [hsw] at hmass
    obtain ⟨x,hx,heq⟩:=p.map_support (fun x=>f x i) (a,b) hmass
    simpa only [heq] using hinc x hx i
  · intro i ⟨b,a⟩ hmass
    rw [hsw] at hmass
    have hz : (a,b)∈U i := by by_contra hh; exact hmass (hsup i (a,b) hh)
    exact mem_image.mpr ⟨(a,b),hz,rfl⟩
  · intro i b hb
    rw [hsum]
    exact hb.2.trans (by
      rw [exp_sub,he]
      have hp0 : 0≤exp κ/q^r := by positivity
      simpa only [one_mul,mul_div_assoc] using mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ)≤1024) hp0)
  · intro i
    simp only [hsum]
    exact (htarg i).2.1
  · intro i
    have hh:=(htarg i).2.2
    rw [exp_sub,he] at hh
    simp only [Law.event,sum_filter] at hh
    calc
      _ ≤ ∑ t : B×A, if exp κ/q^d<FiniteMarginals.marginal p.mass (fun x=>(f x i).swap) t
          then FiniteMarginals.marginal p.mass (fun x=>(f x i).swap) t else 0 :=
        sum_le_univ_sum_of_nonneg (fun t=>by split_ifs; exact marginal_nonneg p.mass p.nonneg _ t; rfl)
      _ = ∑ z : A×B, if exp κ/q^d<(tp i).mass z then (tp i).mass z else 0 := by
        rw [Fintype.sum_prod_type,Fintype.sum_prod_type,sum_comm]
        simp only [hsw]
      _ ≤ _ := hh
  · intro i
    rw [sum_marginal]
    calc
      _ ≤ ∑ x,p.mass x*(2*∑ z,s.mass z*
          indicator (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0)) := by
        apply sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
        exact hmean (fun z=>indicator (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0))
          (fun z=>indicator_nonneg _)
      _ = 2*(∑ x,p.mass x*∑ z,s.mass z*
          indicator (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0)) := by simp only [mul_sum]; ring_nf
      _ ≤ 2*I := mul_le_mul_of_nonneg_left (hconflict i) (by norm_num)
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter HighRankBudgets
open scoped Topology BigOperators
noncomputable section

lemma density_positive : 0 < richDensity := by unfold richDensity; positivity
lemma density_small : richDensity≤1/20 := by
  have h : 1≤exp ((1:ℝ)/2) := one_le_exp (by norm_num)
  unfold richDensity
  apply (div_le_iff₀ (by positivity : 0<100*exp ((1:ℝ)/2))).mpr
  linarith
lemma density_scaled : 20*exp (1/2)*richDensity≤1 := by
  unfold richDensity
  rw [←mul_div_assoc,mul_one]
  apply (div_le_iff₀ (by positivity : 0<100*exp ((1:ℝ)/2))).mpr
  nlinarith [exp_pos ((1:ℝ)/2)]

lemma rawError_le {σ η D : ℝ} {d : ℕ} (hσ : 1≤σ) (hη : 0<η) (hd : 0<d) :
    rawError σ η D d≤error σ η D 5000 d := by
  have hσ0 : 0<σ := by linarith
  have hq : 1≤exp σ := one_le_exp (by linarith)
  have hx : 1≤σ^beta η := one_le_rpow hσ (by unfold beta; positivity)
  obtain ⟨hlo,hhi⟩:=row_size hq hx
  change exp σ*σ^beta η≤(rawRows σ η:ℝ) at hlo
  change (rawRows σ η:ℝ)≤2*exp σ*σ^beta η at hhi
  have h1 : -3*(rawRows σ η:ℝ)/(20*d*exp σ)≤-(3/(20*d))*σ^beta η := by
    apply (div_le_iff₀ (by positivity : 0<(20:ℝ)*d*exp σ)).mpr
    have he : -(3/((20:ℝ)*d))*σ^beta η*(20*d*exp σ)=-3*(exp σ*σ^beta η) := by field_simp
    rw [he]
    linarith
  have h2 : 1-(rawRows σ η:ℝ)/(10*exp σ)≤1-(1/10)*σ^beta η := by
    have hh:=(div_le_div_iff_of_pos_right (by positivity : 0<(10:ℝ)*exp σ)).mpr hlo
    have he : exp σ*σ^beta η/(10*exp σ)=(1/10)*σ^beta η := by field_simp
    rw [he] at hh
    linarith
  have h3 : 4*(rawRows σ η:ℝ)*(2*σ^(-2000*beta η)/exp σ)≤16*σ^(-(1999*beta η)) := by
    calc
      _ ≤ 4*(2*exp σ*σ^beta η)*(2*σ^(-2000*beta η)/exp σ) := by gcongr
      _ = 16*σ^(-(1999*beta η)) := by
        have he : σ^beta η*σ^(-2000*beta η)=σ^(-(1999*beta η)) := by
          rw [←rpow_add hσ0]; congr 1; ring
        calc
          _ = 16*(σ^beta η*σ^(-2000*beta η)) := by field_simp; ring
          _ = _ := by rw [he]
  have hg1:=mul_le_mul_of_nonneg_left (exp_le_exp.mpr h1) (show (0:ℝ)≤d by positivity)
  have hg2:=exp_le_exp.mpr h2

  have he2 : exp (1-(1/10)*σ^beta η)=exp 1*exp (-(1/10)*σ^beta η) := by
    rw [show -(1/10)*σ^beta η=-((1/10)*σ^beta η) by ring,exp_neg,exp_sub]; ring
  rw [he2] at hg2
  unfold rawError error
  have hp : 0≤σ^(-4*beta η) := rpow_nonneg hσ0.le _
  have hp' : 0≤σ^(-2*beta η) := rpow_nonneg hσ0.le _
  have hp'' : 0≤σ^(-(1999*beta η)) := rpow_nonneg hσ0.le _
  have he : 0≤exp (2*scaleK σ η D)/exp σ := by positivity
  have he' : 0≤exp (scaleK σ η D)/exp σ := by positivity
  simp only [show -(2*beta η)=-2*beta η by ring,show -(4*beta η)=-4*beta η by ring]
  simp only [mul_div_assoc] at *
  linarith

theorem eventual_budgets {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 0<d) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      1≤σ ∧ 2*d ≤ rawRows σ η ∧ d+2 ≤ rawThreshold σ η ∧
      (rawRows σ η:ℝ)/(10*exp σ) ≤ rawThreshold σ η ∧
      (rawThreshold σ η:ℝ)≤(rawRows σ η:ℝ)/(10*exp σ)+1 ∧
      richDensity≤2048*exp (scaleK σ η D) ∧
      4300*σ^(-2*beta η)≤1/4 ∧ 20480*exp (scaleK σ η D)≤exp σ ∧
      rawError σ η D d≤1/8 := by
  have hb : 0<beta η := by unfold beta; positivity
  have ht:=tendsto_rpow_atTop hb
  have hs : Tendsto (fun σ : ℝ=>4300*σ^(-2*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<2*beta η by positivity)).const_mul 4300 using 1 <;> congr 2 <;> ring_nf
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht.eventually (eventually_ge_atTop (10*((d:ℝ)+2))),
    hs.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_exp_K_over_q hη 20480 1 1 (by norm_num) (by norm_num) (by norm_num),
    eventually_error hη 5000 (1/8) (by norm_num) (by norm_num) d hd]
    with σ hσ hx hs he herr D hD hD'
  have hq : 1≤exp σ := one_le_exp (by linarith)
  have hx0 : 0≤σ^beta η := by positivity
  have hlo : exp σ*σ^beta η≤(rawRows σ η:ℝ) := Nat.le_ceil _
  have hlo' : σ^beta η≤(rawRows σ η:ℝ) := (le_mul_of_one_le_left hx0 hq).trans hlo
  have hh : 2*d ≤ rawRows σ η := by exact_mod_cast (show 2*(d:ℝ)≤(rawRows σ η:ℝ) by linarith)
  have hTlo : (rawRows σ η:ℝ)/(10*exp σ) ≤ rawThreshold σ η := Nat.le_ceil _
  have hThi : (rawThreshold σ η:ℝ)≤(rawRows σ η:ℝ)/(10*exp σ)+1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hT : d+2 ≤ rawThreshold σ η := by
    have ht : (d:ℝ)+2≤(rawRows σ η:ℝ)/(10*exp σ) := by
      apply (le_div_iff₀ (by positivity : 0<10*exp σ)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hx (exp_nonneg σ)]
    exact_mod_cast ht.trans hTlo
  have hκ : 0 ≤ scaleK σ η D := mul_nonneg ((rpow_nonneg (by linarith) _).trans hD) (by positivity)
  have hu := density_small
  have hue : richDensity≤2048*exp (scaleK σ η D) := by
    have he : 1≤exp (scaleK σ η D) := one_le_exp hκ
    linarith
  have hescape : 20480*exp (scaleK σ η D)≤exp σ := by
    have h:=he D hD'
    rw [one_mul] at h
    exact ((div_lt_one (exp_pos σ)).mp h).le
  exact ⟨hσ,hh,hT,hTlo,hThi,hue,hs,hescape,(rawError_le hσ hη hd).trans (herr D hD').le⟩
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter Selection HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section
variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}

lemma highSize_eq (σ η D : ℝ) (d : ℕ) (Q : ℝ) :
    4*((10*((d:ℝ)+1)*1024*exp (scaleK σ η D)/richDensity)^(d+1)*1024*(1+2^(d+2))*(2*Q^d))=
      highPrefactor d*Q^d*exp (((d:ℝ)+1)*scaleK σ η D) := by
  rw [show ((d:ℝ)+1)*scaleK σ η D=((d+1:ℕ):ℝ)*scaleK σ η D by
    simp only [Nat.cast_add, Nat.cast_one],
    exp_nat_mul,highPrefactor]
  rw [show 10*((d:ℝ)+1)*1024*exp (scaleK σ η D)/richDensity=
    (10*((d:ℝ)+1)*1024/richDensity)*exp (scaleK σ η D) by ring,mul_pow]
  ring

attribute [local instance] OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankSuccess_2
attribute [local instance] OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankSuccess_3
theorem eventually_success {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ξ : Type) [Field K] [Fintype K] [Fintype Ξ],
      log (Nat.card K:ℝ)=σ →
      ∀ (ℓ : ℕ), 0<ℓ →
      ∀ (s : Law (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (S : Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (p : Law Ξ) (f : Ξ→Fin ℓ→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (U : Fin ℓ→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D : ℝ), σ^beta η≤D → D≤σ^(1-η/2) →
      ∀ r r' : ℕ, 2 ≤ r → r≤d → d+2 ≤ r+r' →
      (∀ z,z∉S→s.mass z=0) →
      (((S.image Prod.fst).card:ℝ)≤1024*(Nat.card K:ℝ)^r') →
      (((S.image Prod.snd).card:ℝ)≤1024*(Nat.card K:ℝ)^r) →
      ((S.card:ℝ)≤64*(Nat.card K:ℝ)^d) →
      (∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ)) →
      (∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ)) →
      ((d:ℝ)*σ-entropy s≤D*σ^beta η) →
      (∀ x,p.mass x≠0→∀ i,f x i∈U i) →
      (∀ x,p.mass x≠0→∀ i,(f x i).1.rep (f x i).2.rep=0) →
      (∀ i,(((U i).image Prod.fst).card:ℝ)≤1024*(Nat.card K:ℝ)^r') →
      (∀ i,(((U i).image Prod.snd).card:ℝ)≤1024*(Nat.card K:ℝ)^r) →
      (∀ i,((U i).card:ℝ)≤64*(Nat.card K:ℝ)^d) →
      (∀ i a,((univ.filter (fun b=>(a,b)∈U i)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ)) →
      (∀ i b,((univ.filter (fun a=>(a,b)∈U i)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ)) →
      (∀ i,(d:ℝ)*σ-entropy (p.map (fun x=>f x i))≤D*σ^beta η) →
      (∀ i,(∑ x,p.mass x*∑ z,s.mass z*FiniteEventBounds.indicator
        (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0))≤2*σ^(-2000*beta η)/(Nat.card K:ℝ)) →
      let E:=univ.filter (fun z=>
        highGoodFirst s (1024*(Nat.card K:ℝ)^r') ((d:ℝ)*σ) (scaleK σ η D)
          (exp (scaleK σ η D-(r':ℝ)*σ)) z.1 ∧
        highGoodSecond s (1024*(Nat.card K:ℝ)^r) ((d:ℝ)*σ) (scaleK σ η D)
          (exp (scaleK σ η D-(r:ℝ)*σ)) z.2)
      ∃ hE : (1:ℝ)/2≤ s.event E,
        let row:=s.onEvent E (by linarith)
        let h:=rawRows σ η
        let W:=fun z : (Fin h→E)×(Fin h→E)=>ProductLaw.weight row.mass z.1*ProductLaw.weight row.mass z.2
        let code:=fun z : (Fin h→E)×(Fin h→E)=>(fun i=>(z.1 i).val,fun i=>(z.2 i).val)
        let DD:=fun z=>rawDomain (code z) r (rawThreshold σ η)
        (1:ℝ)/2≤∑ v∈univ.filter (fun v : Ξ×((Fin h→E)×(Fin h→E))=>
          ((DD v.2).card:ℝ)≤highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D) ∧
          ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f v.1 (e i)∈DD v.2), p.mass v.1*W v.2 := by
  filter_upwards [eventual_budgets hη d (by omega)] with σ hσ
  intro K Ξ _ _ _ hlog ℓ hℓ s S p f U D hDl hDu r r' hr hrd hrank
    hs hSA hSB hS hsfA hsfB hsdef hp hinc hUA hUB hU hufA hufB hdef hcon
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.card_pos (α:=K)
  have heq : exp σ=(Nat.card K:ℝ) := by rw [←hlog,exp_log hq]
  obtain ⟨hσ1,hh,hT,hTlo,hThi,huA,hsmall,hescape,herr⟩:=hσ D hDl hDu
  rw [heq] at hTlo hThi hescape
  have H:=extraction hd hℓ s S p f U σ (beta η) D hσ1 (by unfold beta; positivity) hlog hDl
    (rawRows σ η) r r' (rawThreshold σ η) hr hrd hrank hh richDensity
    (2*σ^(-2000*beta η)/(Nat.card K:ℝ)) density_positive huA density_small density_scaled hsmall
    hs hSA hSB hS hsfA hsfB hsdef hp hinc hUA hUB hU hufA hufB hdef hcon hTlo hThi hT hescape
  dsimp only at H ⊢
  obtain ⟨hE,H⟩:=H
  refine ⟨hE,?_⟩
  have herr' : 1/2≤1-2*rawError σ η D d-1/4 := by linarith
  apply herr'.trans
  unfold rawError at herr' ⊢
  rw [heq]
  apply H.trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro v hv
    obtain ⟨hc,e,he⟩:=(mem_filter.mp hv).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,e,?_⟩
    · rw [←highSize_eq]
      rw [rawDomain, card_image_of_injective _ Prod.swap_injective]
      convert hc using 1 <;> try rfl
    · intro i
      apply mem_image.mpr
      exact ⟨(f v.1 (e i)).swap,he i,Prod.swap_swap _⟩
  · intro v _ _
    apply mul_nonneg (p.nonneg _)
    apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro j hj <;> exact (s.onEvent _ _).nonneg _
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

lemma Law.prod_map_left (p : Law X) (s : Law Y) (f : X→Z) :
    (p.prod s).map (fun z=>f z.1)=p.map f := by
  ext a
  simp only [Law.map,Law.prod,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  by_cases h : f x=a
  · simp only [h,ite_true,←mul_sum,s.total,mul_one]
  · simp only [h,ite_false,sum_const_zero]

lemma raw_rows_entropy {F Ω : Type*} [Fintype F] [Fintype Ω] (h : ℕ)
    (p : Law Ω) (code : Ω→(Fin h→F)×(Fin h→F)) :
    entropy (p.map code)≤2*(h:ℝ)*log (Fintype.card F) := by
  have hh:=entropy_le_log_card (p.map code) univ (by simp)
  simp only [card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Nat.cast_mul,Nat.cast_pow] at hh
  rw [←pow_two,log_pow,log_pow] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section
variable {F Ξ Z : Type*} [Fintype F] [Fintype Ξ] [Fintype Z]

theorem context_replacement {h ℓ : ℕ} (p : Law Ξ) (E : Finset F) (row : Law E)
    (f : Ξ→Fin ℓ→F) (DD : ((Fin h→F)×(Fin h→F))→Finset F) (B : ℝ)
    (Q : F→F→Prop)
    (hQ : ∀ x,p.mass x≠0→∀ i j,i<j→Q (f x i) (f x j))
    (stream : Ξ→Z) :
    let rows:=(Law.pi (fun _ : Fin h=>row)).prod (Law.pi (fun _ : Fin h=>row))
    let μ:=p.prod rows
    let code:=fun z : Ξ×((Fin h→E)×(Fin h→E))=>
      (fun i=>(z.2.1 i).val,fun i=>(z.2.2 i).val)
    let G:=univ.filter (fun z=>((DD (code z)).card:ℝ)≤B ∧
      ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f z.1 (e i)∈DD (code z))
    (1:ℝ)/2≤μ.event G →
    ∃ hG : 0<μ.event G,
      let ν:=μ.onEvent G hG
      ∃ choose : G→Fin (ℓ/2)↪o Fin ℓ,
      (∀ (z : G) i,f z.val.1 (choose z i)∈DD (code z)) ∧
      (∀ z : G,((DD (code z)).card:ℝ)≤B) ∧
      (∀ z : G,ν.mass z≠0→∀ i j,i<j→Q (f z.val.1 (choose z i)) (f z.val.1 (choose z j))) ∧
      (∀ a,(ν.map (fun z=>stream z.val.1)).mass a≤2*(p.map stream).mass a) ∧
      entropy (ν.map (fun z=>code z))≤2*(h:ℝ)*log (Fintype.card F) := by
  intro rows μ code G hG
  have hG0 : 0<μ.event G := by linarith
  let ν:=μ.onEvent G hG0
  have hx : ∀ z : G,∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f z.val.1 (e i)∈DD (code z) :=
    fun z=>(mem_filter.mp z.property).2.2
  choose ch hc using hx
  refine ⟨hG0,ch,hc,fun z=>(mem_filter.mp z.property).2.1,?_,?_,?_⟩
  · intro z hz i j hij
    have hp : p.mass z.val.1≠0 := by
      intro hp
      apply hz
      change p.mass z.val.1*rows.mass z.val.2/μ.event G=0
      rw [hp,zero_mul,zero_div]
    exact hQ z.val.1 hp _ _ ((ch z).strictMono hij)
  · intro a
    have hh:=μ.onEvent_map_le_two G hG (fun z=>stream z.1) a
    rw [Law.prod_map_left] at hh
    exact hh
  · exact raw_rows_entropy h _ _

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_HighRankEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section
variable {K V Ω : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype Ω]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_bound {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (Fintype.card (Projectivization K V):ℝ)≤2*(Nat.card K:ℝ)^d := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  simp only [Nat.cast_pow]
  exact HighRankExcess.geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)) d

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_positive {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (0:ℝ)<Fintype.card (Projectivization K V) := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  apply lt_of_lt_of_le (by norm_num : (0:ℝ)<(Nat.card K^0:ℕ))
  exact single_le_sum (fun i _=>Nat.cast_nonneg _) (mem_range.mpr (by omega))

omit [FiniteDimensional K V] in
lemma flag_card_log {d : ℕ} (hdim : Module.finrank K V=d+1) :
    log (Fintype.card (Projectivization K (Module.Dual K V)×Projectivization K V))≤
      2*(log 2+(d:ℝ)*log (Nat.card K)) := by
  have hdual : Module.finrank K (Module.Dual K V)=d+1 := by rw [Subspace.dual_finrank_eq,hdim]
  have ha:=projective_card_bound hdual
  have hb:=projective_card_bound hdim
  have hap:=projective_card_positive hdual
  have hbp:=projective_card_positive hdim
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  simp only [Fintype.card_prod,Nat.cast_mul]
  apply (log_le_log (mul_pos hap hbp)
    (mul_le_mul ha hb hbp.le (by positivity))).trans
  rw [←pow_two,log_pow,log_mul (by norm_num) (pow_ne_zero _ hq.ne'),log_pow]
  rfl

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_HighRankReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter Selection HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

attribute [instance] Replacement.inst

section Generic
variable {F Ξ : Type} [Fintype F] [Fintype Ξ]

theorem replacement_of_success {h ℓ : ℕ} (p : Law Ξ) (E : Finset F) (row : Law E)
    (f : Ξ→Fin ℓ→F) (DD : ((Fin h→F)×(Fin h→F))→Finset F) (B : ℝ) :
    let rows:=(Law.pi (fun _ : Fin h=>row)).prod (Law.pi (fun _ : Fin h=>row))
    let μ:=p.prod rows
    let code:=fun z : Ξ×((Fin h→E)×(Fin h→E))=>
      (fun i=>(z.2.1 i).val,fun i=>(z.2.2 i).val)
    let G:=univ.filter (fun z=>((DD (code z)).card:ℝ)≤B ∧
      ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f z.1 (e i)∈DD (code z))
    (1:ℝ)/2≤μ.event G →
    Nonempty (Replacement p f DD B (2*(h:ℝ)*log (Fintype.card F))) := by
  intro rows μ code G hg
  obtain ⟨hG,ch,hch,hcard,_,hdom,hcost⟩:=context_replacement p E row f DD B
    (fun _ _=>True) (by simp) id hg
  refine ⟨⟨G,inferInstance,μ.onEvent G hG,(fun z=>z.val.1),(fun z=>code z.val),ch,hch,hcard,?_,hcost⟩⟩
  intro a
  have hh:=hdom a
  rw [Law.map_id] at hh
  exact hh

theorem replacement_of_weight_success {h ℓ : ℕ} (p : Law Ξ) (E : Finset F) (row : Law E)
    (f : Ξ→Fin ℓ→F) (DD : ((Fin h→F)×(Fin h→F))→Finset F) (B : ℝ)
    (hg : (1:ℝ)/2≤∑ v∈univ.filter (fun v : Ξ×((Fin h→E)×(Fin h→E))=>
      ((DD (fun i=>(v.2.1 i).val,fun i=>(v.2.2 i).val)).card:ℝ)≤B ∧
      ∃ e : Fin (ℓ/2)↪o Fin ℓ,∀ i,f v.1 (e i)∈DD (fun i=>(v.2.1 i).val,fun i=>(v.2.2 i).val)),
      p.mass v.1*(ProductLaw.weight row.mass v.2.1*ProductLaw.weight row.mass v.2.2)) :
    Nonempty (Replacement p f DD B (2*(h:ℝ)*log (Fintype.card F))) := by
  apply replacement_of_success (h:=h) (ℓ:=ℓ) p E row f DD B
  simpa only [Law.event,Law.prod,Law.pi,ProductLaw.weight] using hg

end Generic

variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}

attribute [local instance] OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankReplacement_2
attribute [local instance] OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankReplacement_3
theorem eventually_replacement {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ξ : Type) [Field K] [Fintype K] [Fintype Ξ],
      log (Nat.card K:ℝ)=σ →
      ∀ (ℓ : ℕ), 0<ℓ →
      ∀ (s : Law (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (S : Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (p : Law Ξ) (f : Ξ→Fin ℓ→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (U : Fin ℓ→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D : ℝ), σ^beta η≤D → D≤σ^(1-η/2) →
      ∀ r r' : ℕ, 2 ≤ r → r≤d → d+2 ≤ r+r' →
      (∀ z,z∉S→s.mass z=0) → Caps σ r r' S →
      ((d:ℝ)*σ-entropy s≤D*σ^beta η) →
      (∀ x,p.mass x≠0→∀ i,f x i∈U i) →
      (∀ x,p.mass x≠0→∀ i,(f x i).1.rep (f x i).2.rep=0) →
      (∀ i,Caps σ r r' (U i)) →
      (∀ i,(d:ℝ)*σ-entropy (p.map (fun x=>f x i))≤D*σ^beta η) →
      (∀ i,(∑ x,p.mass x*∑ z,s.mass z*FiniteEventBounds.indicator
        (z.1.rep (f x i).2.rep=0 ∧ (f x i).1.rep z.2.rep≠0))≤2*σ^(-2000*beta η)/(Nat.card K:ℝ)) →
      Nonempty (Replacement p f (fun z=>rawDomain (h:=rawRows σ η) z r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_success hη d hd] with σ he
  intro K Ξ _ _ _ hlog ℓ hℓ s S p f U D hDl hDu r r' hr hrd hrank hs hS hsdef hp hinc hU hdef hcon
  obtain ⟨hE,hgood⟩:=he K Ξ hlog ℓ hℓ s S p f U D hDl hDu r r' hr hrd hrank
    hs hS.first hS.second hS.joint hS.firstFiber hS.secondFiber hsdef hp hinc
    (fun i=>(hU i).first) (fun i=>(hU i).second) (fun i=>(hU i).joint)
    (fun i=>(hU i).firstFiber) (fun i=>(hU i).secondFiber) hdef hcon
  let E:=univ.filter (fun z : Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)=>
    highGoodFirst s (1024*(Nat.card K:ℝ)^r') ((d:ℝ)*σ) (scaleK σ η D)
      (exp (scaleK σ η D-(r':ℝ)*σ)) z.1 ∧
    highGoodSecond s (1024*(Nat.card K:ℝ)^r) ((d:ℝ)*σ) (scaleK σ η D)
      (exp (scaleK σ η D-(r:ℝ)*σ)) z.2)
  have hE0 : 0 < s.event E := by dsimp only [E]; linarith
  let row:=s.onEvent E hE0
  let h:=rawRows σ η
  let DD:=fun z=>rawDomain (K:=K) (d:=d) (h:=h) z r (rawThreshold σ η)
  let B₀:=highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D)
  have extract:=replacement_of_weight_success (h:=h) (ℓ:=ℓ) p E row f DD B₀
  have hex : Nonempty (Replacement p f DD B₀ (2*(h:ℝ)*log (Fintype.card
      (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))))) := by
    apply extract
    dsimp only at hgood
    simpa only [DD, B₀, row, E, h] using hgood
  obtain ⟨e⟩:=hex
  refine ⟨e.cost_mono ?_⟩
  have hdim : Module.finrank K (Fin (d+1)→K)=d+1 := by simp
  have hc:=mul_le_mul_of_nonneg_left (flag_card_log hdim) (by positivity : 0≤2*(h:ℝ))
  rw [hlog] at hc
  calc
    _ ≤ 2*(h:ℝ)*(2*(log 2+(d:ℝ)*σ)) := hc
    _ = _ := by dsimp only [h]; ring

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C : Type} [Fintype β] [Fintype C]
namespace ExposureModel

theorem atRound_owner (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k)
    (z : (atRound n k p e own t).History) (i : (atRound n k p e own t).Index z) :
    (atRound n k p e own t).owner z i=own ((atRound n k p e own t).origin z i) := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => rfl
    | succ j => exact ih _ (remainingEmbedding e z.1) (fun i=>own i) j z.2.2 i

theorem atRound_embedding_owner (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k)
    (z : (atRound n k p e own t).History) (b : C)
    (x : Fin ((atRound n k p e own t).remaining z)) :
    (atRound n k p e own t).owner z ((atRound n k p e own t).embedding z (b,x))=some b := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => exact hown b x
    | succ j =>
      exact ih _ (remainingEmbedding e z.1) (fun i=>own i)
        (remaining_own e z.1 own hown) j z.2.2 x

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {X Ω B : Type*} [Fintype X] [Fintype Ω] [Fintype B]

lemma Law.common_source_support (q : Law X) (p : Law Ω) (f : X→B) (g : Ω→B)
    (h : q.map f=p.map g) (x : X) (hx : q.mass x≠0) :
    ∃ ω,p.mass ω≠0 ∧ g ω=f x := by
  have hf : (p.map g).mass (f x)≠0 := by
    rw [←h]
    exact ne_of_gt ((lt_of_le_of_ne (q.nonneg x) (Ne.symm hx)).trans_le (q.le_map f x))
  exact p.map_support g (f x) hf

namespace ExposureModel
variable {β C ι Θ : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ]

omit [Fintype Θ] [Fintype ι] [DecidableEq ι] in
lemma afterDraw_tagged (M : ExposureModel ι β C) (hp : ∀ z,0<M.remaining z)
    (tag : M.History→Θ) (φ : Θ×(ι→β)→ℝ) :
    (∑ x,(M.afterDraw hp).joint.mass x*φ (tag x.1.1,(M.afterDraw hp).restore x.1 x.2))=
      ∑ x,M.joint.mass x*φ (tag x.1,M.restore x.1 x.2) := by
  rw [joint,Law.sigma_sum,joint,Law.sigma_sum]
  exact M.freshLaw_old hp (fun z=>∑ y,(M.tupleLaw z).mass y*φ (tag z,M.restore z y))

theorem contextual_afterDraw_tagged_map (n k : ℕ) {Ω : Type} [Fintype Ω]
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z) :
    ((contextual n k p θ G e own t).afterDraw hp).joint.map
      (fun x=>(x.1.1.1,((contextual n k p θ G e own t).afterDraw hp).restore x.1 x.2))=
        p.map (fun ω=>(θ ω,G ω)) := by
  ext y
  have he:=afterDraw_tagged (contextual n k p θ G e own t) hp (fun z=>z.1)
    (fun x=>if x=y then 1 else 0)
  have he' := he.trans (contextual_tagged n k p θ G e own t (fun x=>if x=y then 1 else 0))
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using he'

theorem contextual_fresh_source (n k : ℕ) {Ω : Type} [Fintype Ω]
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
    (z : (contextual n k p θ G e own t).FreshHistory)
    (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)
    (y : (contextual n k p θ G e own t).Index z.1→β)
    (hy : ((contextual n k p θ G e own t).tupleLaw z.1).mass y≠0) :
    ∃ ω,p.mass ω≠0 ∧ θ ω=z.1.1 ∧
      ∀ i,G ω ((contextual n k p θ G e own t).origin z.1 i)=y i := by
  let M:=contextual n k p θ G e own t
  obtain ⟨ω,hω,he⟩:=Law.common_source_support (M.afterDraw hp).joint p
    (fun x=>(x.1.1.1,(M.afterDraw hp).restore x.1 x.2)) (fun ω=>(θ ω,G ω))
    (contextual_afterDraw_tagged_map n k p θ G e own t hp) ⟨z,y⟩ (mul_ne_zero hz hy)
  refine ⟨ω,hω,congrArg Prod.fst he,fun i=>?_⟩
  have hh:=congrFun (congrArg Prod.snd he) (M.origin z.1 i)
  exact hh.trans (M.restore_origin z.1 y i)

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_ExposureWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι β C X : Type} [Fintype β]
namespace ExposureModel

lemma lift_origin (M : ExposureModel ι β C) (z : M.History) (e : X↪ι)
    (h : ∀ x,∃ i,M.origin z i=e x) (x : X) : M.origin z (M.lift z e h x)=e x :=
  (h x).choose_spec

end ExposureModel

namespace Windows
variable [Fintype C]

lemma owner_early {w n : ℕ} (j : Slot w n) (i : Fin w)
    (h : owner w n j=some (i,false)) : j.1=i ∧ j.2.val<n := by
  unfold owner at h
  split_ifs at h with he hl
  · have hh:=Option.some.inj h
    exact ⟨congrArg Prod.fst hh,he⟩
  · have hh:=congrArg Prod.snd (Option.some.inj h)
    cases hh

lemma owner_late {w n : ℕ} (j : Slot w n) (i : Fin w)
    (h : owner w n j=some (i,true)) : j.1=i ∧ 3*n≤ j.2.val := by
  unfold owner at h
  split_ifs at h with he hl
  · have hh:=congrArg Prod.snd (Option.some.inj h)
    cases hh
  · have hh:=Option.some.inj h
    exact ⟨congrArg Prod.fst hh,hl⟩

lemma owner_between {w n : ℕ} (i : Fin w) (a b : Slot w n)
    (ha : owner w n a=some (i,false)) (hb : owner w n b=some (i,true))
    (x : Fin (2*n)) : position a<position (middle w n (i,x)) ∧
      position (middle w n (i,x))<position b := by
  obtain ⟨ha₁,ha₂⟩:=owner_early a i ha
  obtain ⟨hb₁,hb₂⟩:=owner_late b i hb
  change a.1.val*(4*n)+a.2.val< i.val*(4*n)+(n+x.val) ∧
    i.val*(4*n)+(n+x.val)< b.1.val*(4*n)+b.2.val
  rw [ha₁,hb₁]
  constructor <;> omega

end Windows
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_PreparedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]

variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualPreparedWindows_1
lemma model_owner (z : (model w n k p θ G t).History) (i : (model w n k p θ G t).Index z) :
    (model w n k p θ G t).owner z i=owner w (n+k) ((model w n k p θ G t).origin z i) :=
  atRound_owner n k ((p.cond θ z.1).map G) (embedding w (n+k)) (owner w (n+k)) t z.2 i

lemma model_embedding_owner (z : (model w n k p θ G t).History) (b : Block w)
    (x : Fin ((model w n k p θ G t).remaining z)) :
    (model w n k p θ G t).owner z ((model w n k p θ G t).embedding z (b,x))=some b :=
  atRound_embedding_owner n k ((p.cond θ z.1).map G) (embedding w (n+k)) (owner w (n+k))
    (embedding_owner w (n+k)) t z.2 b x

lemma target_origin (z : (model w n k p θ G t).History) (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).origin z (target w n k p θ G t z (i,x))=middle w (n+k) (i,x) :=
  lift_origin _ _ _ _ _

lemma target_owner (z : (model w n k p θ G t).History) (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).owner z (target w n k p θ G t z (i,x))=none := by
  rw [model_owner,target_origin,middle_unowned]

lemma representative_owner (z : (model w n k p θ G t).FreshHistory) (b : Block w) :
    (model w n k p θ G t).owner z.1 ((model w n k p θ G t).representative z b)=some b :=
  model_embedding_owner w n k p θ G t z.1 b (z.2 b)

lemma representative_origin_owner (z : (model w n k p θ G t).FreshHistory) (b : Block w) :
    owner w (n+k) ((model w n k p θ G t).origin z.1
      ((model w n k p θ G t).representative z b))=some b := by
  rw [←model_owner,representative_owner]

lemma target_between (z : (model w n k p θ G t).FreshHistory) (i : Fin w) (x : Fin (2*(n+k))) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false))) <
      position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (i,x))) ∧
    position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (i,x))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,true))) := by
  rw [target_origin]
  exact owner_between i _ _ (representative_origin_owner w n k p θ G t z (i,false))
    (representative_origin_owner w n k p θ G t z (i,true)) x

lemma target_other (z : (model w n k p θ G t).FreshHistory) (b : Block w)
    (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).representative z b∈otherRepresentatives
      ((model w n k p θ G t).embedding z.1) ((model w n k p θ G t).owner z.1) z.2
      (target w n k p θ G t z.1 (i,x)) := by
  apply mem_image.mpr
  refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
  rw [target_owner]
  exact Option.some_ne_none _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_GoodChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β]

lemma pairInformation_symm (p : Law (ι→β)) (i j : ι) :
    pairInformation p i j=pairInformation p j i := by
  apply Subtype.ext
  change mutualInfo (p.map (fun x=>(x i,x j)))=mutualInfo (p.map (fun x=>(x j,x i)))
  have he : p.map (fun x=>(x j,x i))=(p.map (fun x=>(x i,x j))).swap := by
    rw [Law.swap_eq_map,Law.map_map]
    rfl
  rw [he]
  simp only [mutualInfo,Law.swap_fst,Law.swap_snd,entropy_swap,add_comm]

variable {A B K V : Type} [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable {C X : Type} [Fintype C]

lemma good_charge_reversed (p : Law (ι→β)) (e : C×X↪ι) (own : ι→Option C)
    (c : ι→ι→NNReal) (hc : ∀ i j,c i j=c j i) (J D a : ℝ) (f : C→X)
    (i j : ι) (hi : i∉badIndices p e own c J D a f)
    (hj : j∈otherRepresentatives e own f i) :
    (pairInformation p j i:ℝ)+(c j i:ℝ)≤a := by
  rw [pairInformation_symm p j i,hc j i]
  exact ((not_badIndices p e own c J D a f i).mp hi).2 j hj

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real FiniteEventBounds
open scoped Classical BigOperators
noncomputable section
variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]

theorem original_forbidden_product (p : Law X) (f : X→A) (g : X→B) (R : A→B→Prop)
    (hc : ∀ x,p.mass x≠0→¬R (f x) (g x)) :
    (∑ x,p.mass x*∑ a,(p.map f).mass a*indicator (R a (g x)))≤
      2*mutualInfo (p.map (fun x=>(f x,g x))) := by
  let joint:=p.map (fun x=>(f x,g x))
  let E:=univ.filter (fun z : A×B=>R z.1 z.2)
  have hzero : joint.event E=0 := by
    apply sum_eq_zero
    intro z hz
    by_contra hh
    obtain ⟨x,hx,he⟩:=p.map_support (fun x=>(f x,g x)) z hh
    have hr := (mem_filter.mp hz).2
    rw [←he] at hr
    exact hc x hx hr
  have hf : joint.fst=p.map f := by
    rw [←Law.map_fst,Law.map_map]
    rfl
  have hg : joint.snd=p.map g := by
    rw [←Law.map_snd,Law.map_map]
    rfl
  have hh:=mutualInfo_event_transfer joint E
  rw [hzero,add_zero,hf,hg] at hh
  have he : ((p.map f).prod (p.map g)).event E=
      ∑ x,p.mass x*∑ a,(p.map f).mass a*indicator (R a (g x)) := by
    simp only [Law.event,E,sum_filter,Law.prod,Fintype.sum_prod_type]
    have hz : ∀ a b,(if R a b then (p.map f).mass a*(p.map g).mass b else 0)=
        (p.map g).mass b*((p.map f).mass a*indicator (R a b)) := by
      intro a b
      by_cases h : R a b <;> simp [indicator,h,mul_comm]
    simp only [hz]
    rw [sum_comm]
    simp only [←mul_sum]
    exact p.sum_map g _
  rw [he] at hh
  exact hh

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional K V] in
theorem high_original_conflict (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι)
    (hc : ∀ x,p.mass x≠0→(x i).1.rep (x j).2.rep=0→(x j).1.rep (x i).2.rep=0) :
    (∑ x,p.mass x*∑ z,(p.marginal i).mass z*
      indicator (z.1.rep (x j).2.rep=0∧(x j).1.rep z.2.rep≠0))≤2*(pairInformation p i j:ℝ) := by
  exact original_forbidden_product p (fun x=>x i) (fun x=>x j)
    (fun z t=>z.1.rep t.2.rep=0∧t.1.rep z.2.rep≠0)
    (fun x hx hh=>hh.2 (hc x hx hh.1))
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.ExposureModel
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ ι β C : Type} [Fintype Ω] [Fintype Θ] [Fintype ι]
  [DecidableEq ι] [Fintype β] [Fintype C]
variable (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
  (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
  (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
  (z : (contextual n k p θ G e own t).FreshHistory)
  (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)

include hp hz

lemma prepared_marginal_source
    (i : (contextual n k p θ G e own t).Index z.1) (a : β)
    (ha : (((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a≠0) :
    ∃ ω,p.mass ω≠0 ∧ θ ω=z.1.1 ∧
      G ω ((contextual n k p θ G e own t).origin z.1 i)=a := by
  obtain ⟨y,hy,he⟩:=((contextual n k p θ G e own t).tupleLaw z.1).map_support
    (fun y=>y i) a ha
  obtain ⟨ω,hω,hθ,hG⟩:=contextual_fresh_source n k p θ G e own t hp z hz y hy
  exact ⟨ω,hω,hθ,(hG i).trans he⟩

lemma prepared_marginal_domain (S : Θ→ι→Finset β)
    (hS : ∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i)
    (i : (contextual n k p θ G e own t).Index z.1) :
    ∀ a,a∉S z.1.1 ((contextual n k p θ G e own t).origin z.1 i)→
      (((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a=0 := by
  intro a ha
  by_contra h
  obtain ⟨ω,hω,hθ,hG⟩:=prepared_marginal_source n k p θ G e own t hp z hz i a h
  have hh:=hS ω hω ((contextual n k p θ G e own t).origin z.1 i)
  rw [hθ,hG] at hh
  exact ha hh

end
end SharpLogRamsey.Selection.ExposureModel

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_PreparedReciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section
variable {Ω : Type*} [Fintype Ω]
lemma Law.exists_mass_ne_zero (p : Law Ω) : ∃ ω,p.mass ω≠0 := by
  by_contra h
  push Not at h
  have hh:=p.total
  simp only [h,sum_const_zero] at hh
  norm_num at hh

namespace ExposureModel
variable {Ω Θ ι C β : Type} [Fintype Ω] [Fintype Θ] [Fintype ι] [DecidableEq ι]
  [Fintype C] [Fintype β]
lemma prepared_context_property (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
    (z : (contextual n k p θ G e own t).FreshHistory)
    (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)
    (P : Θ→Prop) (hP : ∀ ω,p.mass ω≠0→P (θ ω)) : P z.1.1 := by
  obtain ⟨y,hy⟩:=((contextual n k p θ G e own t).tupleLaw z.1).exists_mass_ne_zero
  obtain ⟨ω,hω,hθ,_⟩:=contextual_fresh_source n k p θ G e own t hp z hz y hy
  simpa only [hθ] using hP ω hω
end ExposureModel

open ExposureModel

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_GoodPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.finDecC
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.indexDecC
lemma goodTarget_not_bad (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w)
    (j : Fin (goodMiddle w n k p θ G t z bad i).card) :
    goodTarget w n k p θ G t z bad i j∉bad := by
  exact (mem_filter.mp ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin_mem rfl j)).2

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_HighRankPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_1
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_3
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_4
theorem eventually_prepared_high_oai {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D J : ℝ) (r r' : ℕ), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      2 ≤ r → r≤d → d+2 ≤ r+r' →
      (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
      (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
        (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i,Caps σ r r' (S (θ ω) i)) →
      ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
        (z : (model w n k p θ G t).FreshHistory),
        ((model w n k p θ G t).freshLaw hp).mass z≠0 →
      ∀ i : Fin w,
      let M:=model w n k p θ G t
      let q:=M.tupleLaw z.1
      let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
      let bad:=badIndices q (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J (D*σ^beta η) a z.2
      M.representative z (i,false)∉bad →
      0<(goodMiddle w n k p θ G t z bad i).card →
      Nonempty (Replacement q (fun y j=>y (goodTarget w n k p θ G t z bad i j))
        (fun code=>rawDomain (h:=rawRows σ η) code r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_replacement hη d hd] with σ he
  intro K Ω Θ _ _ _ _ hlog w n k p θ G S D J r r' hDl hDu hJ hr hrd hrr hS hf hcon hcap t hp z hz i
  dsimp only
  let M:=model w n k p θ G t
  let q:=M.tupleLaw z.1
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  let bad:=badIndices q (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J (D*σ^beta η) a z.2
  let rep:=M.representative z (i,false)
  let T:=goodTarget w n k p θ G t z bad i
  intro hrep hlen
  have hc:=prepared_context_property n k p θ G (fun _=>embedding w (n+k))
    (fun _=>owner w (n+k)) t hp z hz (fun θ=>∀ i,Caps σ r r' (S θ i)) hcap
  have entropy_good j (hj : j∉bad) : (d:ℝ)*σ-entropy (q.marginal j)≤D*σ^beta η := by
    have hh:=((not_badIndices q (M.embedding z.1) (M.owner z.1)
      (fun _ _=>0) J (D*σ^beta η) a z.2 j).mp hj).1
    exact (sub_le_sub_right hJ _).trans hh
  have targetgood j : T j∉bad := goodTarget_not_bad w n k p θ G t z bad i j
  have targetbefore j : position (M.origin z.1 rep)<position (M.origin z.1 (T j)) := by
    exact (target_between w n k p θ G t z i ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl j)).1
  have hsrc y (hy : q.mass y≠0) := contextual_fresh_source n k p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp z hz y hy
  apply he K _ hlog _ hlen (q.marginal rep) (S z.1.1 (M.origin z.1 rep)) q
    (fun y j=>y (T j)) (fun j=>S z.1.1 (M.origin z.1 (T j))) D hDl hDu r r' hr hrd hrr
  · exact prepared_marginal_domain n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz S hS rep
  · exact hc _
  · exact entropy_good rep hrep
  · intro y hy j
    obtain ⟨ω,hω,hθ,hG⟩:=hsrc y hy
    have hvalue : G ω (M.origin z.1 (T j))=y (T j) := hG (T j)
    simpa only [hθ,hvalue] using hS ω hω (M.origin z.1 (T j))
  · intro y hy j
    obtain ⟨ω,hω,hθ,hG⟩:=hsrc y hy
    have hvalue : G ω (M.origin z.1 (T j))=y (T j) := hG (T j)
    simpa only [hvalue] using hf ω hω (M.origin z.1 (T j))
  · intro j
    exact hc _
  · intro j
    exact entropy_good (T j) (targetgood j)
  · intro j
    have hi : (pairInformation q rep (T j):ℝ)≤a := by
      have hh:=good_charge_reversed q (M.embedding z.1) (M.owner z.1)
        (fun _ _=>0) (by simp) J (D*σ^beta η) a z.2 (T j) rep (targetgood j)
        (target_other w n k p θ G t z (i,false) i
          ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl j))
      simpa only [NNReal.coe_zero,add_zero] using hh
    have hh:=high_original_conflict q rep (T j) (by
      intro y hy hzero
      obtain ⟨ω,hω,hθ,hG⟩:=hsrc y hy
      have hc':=hcon ω hω (M.origin z.1 rep) (M.origin z.1 (T j)) (targetbefore j)
      rw [hG,hG] at hc'
      exact hc' hzero)
    exact hh.trans (by
      calc
        2*(pairInformation q rep (T j):ℝ) ≤ 2*a := mul_le_mul_of_nonneg_left hi (by norm_num)
        _ = _ := by dsimp [a]; ring)

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high_oai := @OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high_oai
