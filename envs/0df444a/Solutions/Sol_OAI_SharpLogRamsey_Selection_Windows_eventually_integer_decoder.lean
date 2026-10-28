-- Prove2me | solution 1 for OAI.SharpLogRamsey.Selection.Windows.eventually_integer_decoder
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:40:02.080524+00:00
-- url     : https://prove2.me/submissions/9ff069af-42b6-4ec3-ae81-bbefe5b7a7bb

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_integer_population_realization

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

theorem Law.mass_le_one (p : Law α) (a : α) : p.mass a ≤ 1 := by
  rw [← p.total]
  exact single_le_sum (fun b hb => p.nonneg b) (mem_univ a)

theorem entropy_nonneg (p : Law α) : 0 ≤ entropy p := by
  apply neg_nonneg.mpr
  exact sum_nonpos fun a ha => mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
    (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))

theorem entropy_subadditive (p : Law (α × β)) : entropy p ≤ entropy p.fst+entropy p.snd := by
  have h := mutualInfo_nonneg p
  unfold mutualInfo at h
  linarith

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
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]

theorem sum_powers_le_twice {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, q^i ≤ 2*q^(n-1) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one]
  clear hn
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hp : 0 ≤ q^m := pow_nonneg (by linarith) _
    have hmul : 2*q^m ≤ q^(m+1) := by
      rw [pow_succ]
      nlinarith
    calc
      _ ≤ 2*q^m+q^(m+1) := by
        simp only [Nat.succ_eq_add_one] at ih
        linarith
      _ ≤ 2*q^(m+1) := by linarith

end SharpLogRamsey.Selection
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

theorem entropy_le_cross (p : Law α) (q : α → ℝ) (hq : ∀ a, 0<q a)
    (hqt : ∑ a, q a ≤ 1) : entropy p ≤ -∑ a, p.mass a*Real.log (q a) := by
  have h (a : α) : p.mass a-q a ≤
      p.mass a*Real.log (p.mass a)-p.mass a*Real.log (q a) := by
    have H := mul_log_div_ge (p.nonneg a) (hq a).le (by intro hh; exact ((hq a).ne' hh).elim)
    by_cases ha : p.mass a=0
    · simpa [ha] using H
    · rw [Real.log_div ha (hq a).ne', mul_sub] at H
      exact H
  have HH := sum_le_sum (fun a (_ : a∈univ) => h a)
  simp only [sum_sub_distrib, p.total] at HH
  unfold entropy
  linarith

lemma geometric_subprob (l : α → ℕ) (hl : Function.Injective l) {r : ℝ}
    (hr : 0 < r) (hr1 : r<1) : ∑ a, (1-r)*r^(l a) ≤ 1 := by
  have hs : (∑ n ∈ univ.image l, r^n) ≤ ∑' n : ℕ, r^n := by
    exact (summable_geometric_of_lt_one hr.le hr1).sum_le_tsum _ (fun _ _ => pow_nonneg hr.le _)
  rw [sum_image (fun _ _ _ _ he => hl he), tsum_geometric_of_lt_one hr.le hr1] at hs
  rw [← mul_sum]
  have H := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hr1.le)
  simpa only [mul_inv_cancel₀ (sub_pos.mpr hr1).ne'] using H

theorem integer_entropy (p : Law α) (l : α → ℕ) (hl : Function.Injective l)
    (M : ℝ) (hM : 0<M) (hm : ∑ a, p.mass a*(l a:ℝ) ≤ M) :
    entropy p ≤ Real.log (M+1)+1 := by
  let r := M/(M+1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hc : 1-r=1/(M+1) := by dsimp [r]; field_simp; ring
  have H := entropy_le_cross p (fun a => (1-r)*r^(l a))
    (fun a => mul_pos (sub_pos.mpr hr1) (pow_pos hr _))
    (geometric_subprob l hl hr hr1)
  have he : -∑ a, p.mass a*Real.log ((1-r)*r^(l a)) =
      Real.log (M+1) + (∑ a, p.mass a*(l a:ℝ))*Real.log (1+1/M) := by
    have her : Real.log r = -Real.log (1+1/M) := by
      have heq : r=(1+1/M)⁻¹ := by dsimp [r]; field_simp
      rw [heq,Real.log_inv]
    have hlogc : Real.log (1-r) = -Real.log (M+1) := by
      rw [hc, Real.log_div one_ne_zero (by positivity : M+1≠0), Real.log_one, zero_sub]
    simp_rw [Real.log_mul (sub_pos.mpr hr1).ne' (pow_pos hr _).ne',
      Real.log_pow, hlogc,her]
    simp only [mul_add, mul_neg, sum_add_distrib, sum_neg_distrib,
      ← mul_assoc, ← sum_mul,p.total,one_mul]
    ring
  rw [he] at H
  have hlog0 : 0≤Real.log (1+1/M) := Real.log_nonneg (by
    have h : (0:ℝ)≤1/M := by positivity
    linarith)
  have hlog := Real.log_le_sub_one_of_pos (show 0<1+1/M by positivity)
  have hh := mul_le_mul_of_nonneg_left hlog hM.le
  have hx : M*(1+1/M-1)=1 := by field_simp; ring
  rw [hx] at hh
  have hm' := mul_le_mul_of_nonneg_right hm hlog0
  linarith

lemma massLevel_mean (p : Law α) :
    (∑ a, p.mass a*(massLevel p a:ℝ)) ≤ entropy p := by
  unfold entropy
  rw [←sum_neg_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : p.mass a=0
  · simp [hp]
  have hlog : 0 ≤ -Real.log (p.mass a) :=
    neg_nonneg.mpr (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))
  have H := mul_le_mul_of_nonneg_left (Nat.floor_le hlog) (p.nonneg a)
  simpa only [massLevel, mul_neg] using H

lemma level_entropy (p : Law α) :
    entropy (p.map (levelIndex p)) ≤ Real.log (entropy p+2)+1 := by
  have hh := integer_entropy (p.map (levelIndex p)) Subtype.val Subtype.val_injective
    (entropy p+1) (by linarith [entropy_nonneg p])
  have hm : ∑ n : Levels p, (p.map (levelIndex p)).mass n*(n.val:ℝ) ≤ entropy p+1 := by
    rw [p.sum_map]
    exact (massLevel_mean p).trans (by linarith)
  simpa only [show entropy p+1+1=entropy p+2 by ring] using hh hm

lemma same_level_weight (p : Law α) {a b : α} (ha : 0<p.mass a) (hb : 0<p.mass b)
    (he : massLevel p a=massLevel p b) : p.mass a ≤ Real.exp 1*p.mass b := by
  have ha0 : 0 ≤ -Real.log (p.mass a) :=
    neg_nonneg.mpr (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))
  have h₁ := Nat.floor_le ha0
  have h₂ := Nat.lt_floor_add_one (-Real.log (p.mass b))
  change -(Real.log (p.mass b)) < (massLevel p b:ℝ)+1 at h₂
  have hle : Real.log (p.mass a) ≤ 1+Real.log (p.mass b) := by
    change (massLevel p a:ℝ) ≤ -Real.log (p.mass a) at h₁
    rw [he] at h₁
    linarith
  calc
    _ = Real.exp (Real.log (p.mass a)) := (Real.exp_log ha).symm
    _ ≤ Real.exp (1+Real.log (p.mass b)) := Real.exp_le_exp.mpr hle
    _ = _ := by rw [Real.exp_add,Real.exp_log hb]

lemma Law.onEvent_mean (p : Law α) (E : Finset α) (hE : 0<p.event E) (f : α→ℝ) :
    ∑ a : E, (p.onEvent E hE).mass a*f a = (∑ a∈E, p.mass a*f a)/p.event E := by
  simp only [Law.onEvent,div_mul_eq_mul_div,←sum_div]
  congr 1
  exact sum_coe_sort E (fun a => p.mass a*f a)

theorem support_average (p : Law α) (l : α→β) (G : β→Finset α)
    (R : Finset β) (hR : (1:ℝ)/2 ≤ (p.map l).event R)
    (hG : ∀ b∈R, 0<(G b).card)
    (hfiber : ∀ b∈R, ∀ a∈G b, l a=b)
    (hcharge : ∀ b∈R, ∀ a∈G b,
      (p.map l).mass b ≤ Real.exp 1*2*(G b).card*p.mass a) (a : α) :
    ∑ b : R, ((p.map l).onEvent R (by linarith)).mass b *
      (if a∈G b then 1/((G b).card:ℝ) else 0) ≤ 4*Real.exp 1*p.mass a := by
  have hp := p.nonneg a
  have hR0 : 0<(p.map l).event R := by linarith
  have he := (p.map l).onEvent_mean R hR0
    (fun b => if a∈G b then 1/((G b).card:ℝ) else 0)
  rw [he]
  have hsum : (∑ b∈R, (p.map l).mass b*(if a∈G b then 1/((G b).card:ℝ) else 0)) ≤
      2*Real.exp 1*p.mass a := by
    by_cases ha : l a∈R
    · rw [sum_eq_single_of_mem (l a) ha]
      · by_cases hg : a∈G (l a)
        · simp only [ite_eq_left hg,one_div]
          have H := hcharge (l a) ha a hg
          have hc : (0:ℝ)<(G (l a)).card := by exact_mod_cast hG (l a) ha
          have H' : (p.map l).mass (l a)/((G (l a)).card:ℝ) ≤
              2*Real.exp 1*p.mass a := (div_le_iff₀ hc).mpr (by nlinarith [H])
          simpa only [div_eq_mul_inv] using H'
        · simp only [ite_eq_right hg,mul_zero]
          positivity
      · intro b hb hba
        have hab : a∉G b := by intro hh; exact hba (hfiber b hb a hh).symm
        simp [hab]
    · have hz : ∀ b∈R, a∉G b := by
        intro b hb hh
        exact ha ((hfiber b hb a hh) ▸ hb)
      have : (∑ b∈R, (p.map l).mass b*(if a∈G b then 1/((G b).card:ℝ) else 0))=0 := by
        apply sum_eq_zero
        intro b hb
        simp [hz b hb]
      rw [this]
      positivity
  apply (div_le_iff₀ hR0).mpr
  calc
    _ ≤ 2*Real.exp 1*p.mass a := hsum
    _ = (4*Real.exp 1*p.mass a)*(1/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)

theorem partition_entropy (p : Law α) (l : α→β) (S : Finset α)
    (hs : ∀ a, a∉S → p.mass a=0) :
    entropy p ≤ entropy (p.map l)+
      ∑ b, (p.map l).mass b*Real.log (S.filter (fun a => l a=b)).card := by
  let T (b : β) := S.filter (fun a => l a=b)
  have hm (b : β) : ∑ a∈T b, p.mass a=(p.map l).mass b := by
    apply sum_subset (by
      intro a ha
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩)
    intro a ha hna
    apply hs
    intro haS
    apply hna
    exact mem_filter.mpr ⟨haS,(mem_filter.mp ha).2⟩
  have hlog (b : β) :
      (p.map l).mass b*Real.log ((p.map l).mass b)-
      (p.map l).mass b*Real.log (T b).card ≤ ∑ a∈T b, p.mass a*Real.log (p.mass a) := by
    have H := log_sum (T b) p.mass (fun _ => 1) (fun a _ => p.nonneg a)
      (by intros; norm_num) (by intro i hi hf; norm_num at hf)
    simp only [div_one,sum_const,nsmul_eq_mul,mul_one,hm] at H
    by_cases hb : (p.map l).mass b=0
    · simpa [hb] using H
    have hc : (T b).card≠0 := by
      intro he
      have hz : T b=∅ := card_eq_zero.mp he
      exact hb (by simpa [hz] using (hm b).symm)
    rw [Real.log_div hb (by exact_mod_cast hc),mul_sub] at H
    exact H
  have H := sum_le_sum (fun b (_ : b∈univ) => hlog b)
  have he : (∑ b, ∑ a∈T b, p.mass a*Real.log (p.mass a))=
      ∑ a, p.mass a*Real.log (p.mass a) := by
    rw [show (∑ b, ∑ a∈T b, p.mass a*Real.log (p.mass a))=
      ∑ a∈S, p.mass a*Real.log (p.mass a) from sum_fiberwise S l _]
    exact sum_subset (subset_univ S) (fun a _ hna => by rw [hs a hna,zero_mul])
  rw [sum_sub_distrib,he] at H
  unfold entropy
  dsimp only [T] at H
  linarith

theorem partition_loss (p : Law α) (l : α→β) (S : Finset α)
    (hs : ∀ a, a∉S → p.mass a=0) (loss : β→ℝ) (J : ℝ)
    (hc : ∀ b, 0<(p.map l).mass b →
      Real.log (S.filter (fun a => l a=b)).card ≤ J-loss b/2) :
    ∑ b, (p.map l).mass b*loss b ≤ 2*(J-entropy p+entropy (p.map l)) := by
  have hh (b : β) : (p.map l).mass b*Real.log (S.filter (fun a => l a=b)).card ≤
      (p.map l).mass b*(J-loss b/2) := by
    by_cases hz : (p.map l).mass b=0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (hc b (lt_of_le_of_ne ((p.map l).nonneg b) (Ne.symm hz)))
        ((p.map l).nonneg b)
  have H := (partition_entropy p l S hs).trans (add_le_add_right (sum_le_sum (fun b _ => hh b)) _)
  simp only [mul_sub,←mul_div_assoc,sum_sub_distrib,←sum_mul,←sum_div,(p.map l).total,one_mul] at H
  linarith

lemma levelSet_mass (p : Law α) (b : Levels p) :
    ∑ a∈levelSet p b, p.mass a=(p.map (levelIndex p)).mass b := by
  simp only [Law.map,levelSet,sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : 0<p.mass a
  · simp [ha]
  · have hz : p.mass a=0 := le_antisymm (le_of_not_gt ha) (p.nonneg a)
    simp [hz]

lemma levelSet_charge (p : Law α) (b : Levels p) {a : α} (ha : a∈levelSet p b) :
    (p.map (levelIndex p)).mass b ≤ Real.exp 1*(levelSet p b).card*p.mass a := by
  rw [←levelSet_mass p b]
  have ha' := (mem_filter.mp ha).2
  calc
    _ ≤ ∑ _x∈levelSet p b, Real.exp 1*p.mass a := by
      apply sum_le_sum
      intro x hx
      have hx' := (mem_filter.mp hx).2
      apply same_level_weight p hx'.1 ha'.1
      exact congrArg Subtype.val (hx'.2.trans ha'.2.symm)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

lemma bad_level_charge (p : Law α) (b : Levels p) (good : Finset α)
    (hhalf : 2*((levelSet p b)∩good).card < (levelSet p b).card) :
    (p.map (levelIndex p)).mass b ≤
      2*Real.exp 1*(∑ a∈levelSet p b\good, p.mass a) := by
  let S := levelSet p b
  let B := S\good
  have hS : 0<S.card := by dsimp [S]; omega
  have hc : S.card ≤ 2*B.card := by
    have he := card_sdiff_add_card_inter S good
    dsimp [S,B] at *
    omega
  have hrow (b' : α) (hb' : b'∈B) :
      (p.map (levelIndex p)).mass b ≤ Real.exp 1*S.card*p.mass b' :=
    levelSet_charge p b (mem_sdiff.mp hb').1
  have H := sum_le_sum (fun a (ha : a∈B) => hrow a ha)
  simp only [sum_const,nsmul_eq_mul,←mul_sum] at H
  have hm := (p.map (levelIndex p)).nonneg b
  have Hc : (S.card:ℝ) ≤ 2*(B.card:ℝ) := by exact_mod_cast hc
  have Hm := mul_le_mul_of_nonneg_right Hc hm
  have H₂ : (S.card:ℝ)*(p.map (levelIndex p)).mass b ≤
      (S.card:ℝ)*(2*Real.exp 1*(∑ a∈B,p.mass a)) := by nlinarith
  exact (mul_le_mul_iff_right₀ (show (0:ℝ)<S.card by exact_mod_cast hS)).mp H₂

lemma good_level_charge (p : Law α) (b : Levels p) (good : Finset α)
    (hhalf : (levelSet p b).card ≤ 2*((levelSet p b)∩good).card)
    {a : α} (ha : a∈(levelSet p b)∩good) :
    (p.map (levelIndex p)).mass b ≤
      Real.exp 1*2*((levelSet p b)∩good).card*p.mass a := by
  have hc : ((levelSet p b).card:ℝ) ≤ 2*(((levelSet p b)∩good).card:ℝ) := by exact_mod_cast hhalf
  have hpa := p.nonneg a
  have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Real.exp_nonneg 1)) hpa
  exact (levelSet_charge p b (mem_inter.mp ha).1).trans (by nlinarith [H])

lemma Law.map_comp {γ : Type*} [Fintype γ] (p : Law α) (f : α→β) (g : β→γ) :
    (p.map f).map g=p.map (g∘f) := by
  exact p.map_map f g

lemma Law.map_prod_marginals {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law (α×β)) (f : α→γ) (g : β→δ) :
    (p.map (fun z => (f z.1,g z.2))).fst=p.fst.map f ∧
    (p.map (fun z => (f z.1,g z.2))).snd=p.snd.map g := by
  constructor
  · rw [←Law.map_fst,Law.map_comp,←Law.map_fst,Law.map_comp]
    rfl
  · rw [←Law.map_snd,Law.map_comp,←Law.map_snd,Law.map_comp]
    rfl

lemma endpoint_levels_entropy (p : Law (α×β)) :
    entropy (p.map (fun z => (levelIndex p.fst z.1,levelIndex p.snd z.2))) ≤
      Real.log (entropy p.fst+2)+Real.log (entropy p.snd+2)+2 := by
  have H := entropy_subadditive (p.map (fun z => (levelIndex p.fst z.1,levelIndex p.snd z.2)))
  have hm := p.map_prod_marginals (levelIndex p.fst) (levelIndex p.snd)
  rw [hm.1,hm.2] at H
  linarith [level_entropy p.fst,level_entropy p.snd]

lemma levelLoss_nonneg (p : Law α) {A : ℝ} (b : Levels p)
    (hcap : ((levelSet p b).card:ℝ) ≤ A) : 0≤levelLoss p A b := by
  unfold levelLoss
  by_cases hz : (levelSet p b).card=0
  · simp [hz]
  · have hc : (0:ℝ)<(levelSet p b).card := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    exact Real.log_nonneg ((le_div_iff₀ hc).mpr (by simpa using hcap))

lemma levelLoss_size (p : Law α) {A K : ℝ} (hA : 0<A) (b : Levels p)
    (hc : 0<(levelSet p b).card) (hl : levelLoss p A b≤K) :
    A*Real.exp (-K) ≤ (levelSet p b).card := by
  have hc' : (0:ℝ)<(levelSet p b).card := by exact_mod_cast hc
  have H := Real.exp_le_exp.mpr hl
  rw [levelLoss,Real.exp_log (div_pos hA hc')] at H
  have H' := (div_le_iff₀ hc').mp H
  calc
    _ ≤ (Real.exp K*(levelSet p b).card)*Real.exp (-K) :=
      mul_le_mul_of_nonneg_right H' (Real.exp_nonneg _)
    _ = _ := by rw [mul_right_comm,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

lemma level_bad_total (p : Law α) (good : Finset α) :
    (∑ b : Levels p, ∑ a∈levelSet p b\good, p.mass a)=p.event (univ\good) := by
  have he (b : Levels p) : levelSet p b\good =
      univ.filter (fun a => 0<p.mass a ∧ levelIndex p a=b ∧ a∉good) := by
    ext a
    simp [levelSet,and_assoc]
  have he' : univ\good=univ.filter (fun a : α => a∉good) := by ext; simp
  change (∑ b : Levels p, ∑ a∈levelSet p b\good,p.mass a)=∑ a∈univ\good,p.mass a
  simp_rw [he,he',sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases ha : 0<p.mass a
  · by_cases hg : a∈good <;> simp [ha,hg]
  · have hz := le_antisymm (le_of_not_gt ha) (p.nonneg a)
    simp [hz]

lemma retained_mass (p : Law α) (good : Finset α) {A K : ℝ} (hK : 0<K)
    (hcap : ∀ b, ((levelSet p b).card:ℝ)≤A) :
    1-(∑ b, (p.map (levelIndex p)).mass b*levelLoss p A b)/K-
      2*Real.exp 1*p.event (univ\good) ≤
      (p.map (levelIndex p)).event (retainedLevels p good A K) := by
  let q := p.map (levelIndex p)
  let R := retainedLevels p good A K
  have hpoint (b : Levels p) : q.mass b ≤
      (if b∈R then q.mass b else 0)+q.mass b*levelLoss p A b/K+
      2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by
    have hm := q.nonneg b
    have hl := levelLoss_nonneg p b (hcap b)
    have hb0 : 0≤∑ a∈levelSet p b\good,p.mass a := sum_nonneg (fun a _ => p.nonneg a)
    by_cases hb : b∈R
    · rw [ite_eq_left hb]
      have hh : 0≤q.mass b*levelLoss p A b/K := by positivity
      have hh' : 0≤2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by positivity
      linarith
    rw [ite_eq_right hb,zero_add]
    by_cases hc : (levelSet p b).card=0
    · have h0 : q.mass b=0 := by
        rw [show q.mass b=(∑ a∈levelSet p b,p.mass a) from (levelSet_mass p b).symm]
        simp [card_eq_zero.mp hc]
      simp only [h0,zero_mul,zero_div,zero_add]
      positivity
    by_cases hlow : levelLoss p A b≤K
    · have hf : 2*((levelSet p b)∩good).card < (levelSet p b).card := by
        by_contra! hn
        apply hb
        exact mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero hc,hlow,hn⟩
      have H := bad_level_charge p b good hf
      have hh : 0≤q.mass b*levelLoss p A b/K := by positivity
      exact H.trans (by linarith)
    · have H : q.mass b ≤ q.mass b*levelLoss p A b/K := by
        apply (le_div_iff₀ hK).mpr
        exact mul_le_mul_of_nonneg_left (le_of_not_ge hlow) hm
      have hh : 0≤2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by positivity
      linarith
  have H := sum_le_sum (fun b (_ : b∈univ) => hpoint b)
  simp only [sum_add_distrib,←sum_div,←mul_sum,q.total,←sum_filter] at H
  rw [level_bad_total p good] at H
  have heR : univ.filter (fun b => b∈R)=R := by ext; simp
  rw [heR] at H
  change 1≤q.event R+(∑ b,q.mass b*levelLoss p A b)/K+2*Real.exp 1*p.event (univ\good) at H
  change 1-_/_-_≤q.event R
  linarith

theorem auxiliary_supports (p : Law α) (good : Finset α) {A K : ℝ}
    (hA : 0<A) (hK : 0<K) (hcap : ∀ b, ((levelSet p b).card:ℝ)≤A)
    (hbudget : (∑ b, (p.map (levelIndex p)).mass b*levelLoss p A b)/K+
      2*Real.exp 1*p.event (univ\good) ≤ 1/2) :
    ∃ ρ : Law (retainedLevels p good A K),
      (∀ b : retainedLevels p good A K,
        A*Real.exp (-K)/2 ≤ (((levelSet p b)∩good).card:ℝ) ∧
        (((levelSet p b)∩good).card:ℝ)≤A) ∧
      ∀ a, (∑ b : retainedLevels p good A K, ρ.mass b*
        (if a∈(levelSet p b)∩good then 1/((((levelSet p b)∩good).card):ℝ) else 0))
        ≤ 4*Real.exp 1*p.mass a := by
  let R := retainedLevels p good A K
  have hR : (1:ℝ)/2 ≤ (p.map (levelIndex p)).event R := by
    have H := retained_mass p good hK hcap
    change 1-_/_-_≤(p.map (levelIndex p)).event R at H
    linarith
  let ρ := (p.map (levelIndex p)).onEvent R (by linarith)
  refine ⟨ρ, ?_, ?_⟩
  · intro b
    have hb := (mem_filter.mp b.property).2
    have hh : ((levelSet p b).card:ℝ) ≤ 2*(((levelSet p b)∩good).card:ℝ) := by
      exact_mod_cast hb.2.2
    have hl := levelLoss_size p hA b hb.1 hb.2.1
    have hc : (((levelSet p b)∩good).card:ℝ) ≤ (levelSet p b).card := by
      exact_mod_cast card_le_card inter_subset_left
    exact ⟨by linarith, hc.trans (hcap b)⟩
  · intro a
    apply support_average p (levelIndex p) (fun b => levelSet p b∩good) R hR
    · intro b hb
      have hh := (mem_filter.mp hb).2
      have hp := hh.1
      have hs := hh.2.2
      omega
    · intro b hb a ha
      exact (mem_filter.mp (mem_inter.mp ha).1).2.2
    · intro b hb a ha
      exact good_level_charge p b good ((mem_filter.mp hb).2.2.2) ha

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_LevelLosses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem mixing_cell_scale {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) {B z : ℝ}
    (hB : 1≤B) (hz : 0≤z) (hz1 : z≤1)
    (hcap : (S.card:ℝ)*T.card ≤ B*(Nat.card K:ℝ)^(n+3)*z^2) :
    (incidenceCount S T:ℝ) ≤ 2*B*(Nat.card K:ℝ)^(n+2)*z := by
  let q : ℝ := Nat.card K
  let p : ℝ := (∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i)
  let a : ℝ := (S.card:ℝ)*T.card
  have hq : 0<q := by
    dsimp [q]
    exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hv : 0<∑ i∈range (n+3),q^i :=
    sum_pos' (fun i _ => pow_nonneg hq.le _) ⟨0,by simp,by simp⟩
  have hp : p≤1/q := by
    apply (div_le_div_iff₀ hv hq).mpr
    have he : (∑ i∈range (n+3),q^i)=q*(∑ i∈range (n+2),q^i)+1 := geom_sum_succ
    linarith
  have ha : 0≤a := by dsimp [a]; positivity
  have hzz : z^2≤z := by nlinarith
  have hmean : p*a≤B*q^(n+2)*z := by
    have H := mul_le_mul_of_nonneg_right hp ha
    have H' : a/q≤B*q^(n+2)*z^2 := by
      apply (div_le_iff₀ hq).mpr
      change a≤B*q^(n+3)*z^2 at hcap
      calc
        a ≤ B*q^(n+3)*z^2 := hcap
        _ = _ := by rw [show n+3=(n+2)+1 by omega,pow_succ]; ring
    have H'' := mul_le_mul_of_nonneg_left hzz (show 0≤B*q^(n+2) by positivity)
    calc
      p*a ≤ a/q := by simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using H
      _ ≤ B*q^(n+2)*z^2 := H'
      _ ≤ _ := H''
  have hs := projective_mixing_sq hdim S T
  change ((incidenceCount S T:ℝ)-p*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hs
  simp only [mul_assoc] at hs
  change ((incidenceCount S T:ℝ)-p*a)^2 ≤ q^(n+1)*a at hs
  have hscale : q^(n+1)*a ≤ (B*q^(n+2)*z)^2 := by
    have H := mul_le_mul_of_nonneg_left hcap (pow_nonneg hq.le (n+1))
    have he : q^(n+1)*(B*q^(n+3)*z^2)=B*(q^(n+2)*z)^2 := by
      rw [mul_pow,←pow_mul]
      have he : q^(n+1)*q^(n+3)=q^((n+2)*2) := by rw [←pow_add]; congr 1; omega
      calc
        _ = B*(q^(n+1)*q^(n+3))*z^2 := by ring
        _ = _ := by rw [he]; ring
    change q^(n+1)*a ≤ q^(n+1)*(B*q^(n+3)*z^2) at H
    rw [he] at H
    have hBB : B≤B^2 := by nlinarith
    have H' := mul_le_mul_of_nonneg_right hBB (sq_nonneg (q^(n+2)*z))
    exact H.trans (by nlinarith [H'])
  have hpos : 0≤B*q^(n+2)*z := by positivity
  have hdev := (sq_le_sq₀ (abs_nonneg ((incidenceCount S T:ℝ)-p*a)) hpos).mp
    (by simpa using hs.trans hscale)
  have hh := le_abs_self ((incidenceCount S T:ℝ)-p*a)
  linarith

theorem mixing_loss_log {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    {A B C : ℝ} (hA : 0<A) (hB : 0<B) (hC : 1≤C)
    (hc : A*B≤C*(Nat.card K:ℝ)^(n+3))
    (hS : 0<S.card) (hT : 0<T.card)
    (hSA : (S.card:ℝ)≤A) (hTB : (T.card:ℝ)≤B)
    (he : 0 < incidenceCount S T) :
    Real.log (incidenceCount S T) ≤
      Real.log (2*C*(Nat.card K:ℝ)^(n+2))-
        (Real.log (A/S.card)+Real.log (B/T.card))/2 := by
  let x := Real.log (A/S.card)
  let y := Real.log (B/T.card)
  let z := Real.exp (-(x+y)/2)
  have hS' : (0:ℝ)<S.card := by exact_mod_cast hS
  have hT' : (0:ℝ)<T.card := by exact_mod_cast hT
  have hx : 0≤x := Real.log_nonneg ((one_le_div hS').mpr hSA)
  have hy : 0≤y := Real.log_nonneg ((one_le_div hT').mpr hTB)
  have hz : 0<z := Real.exp_pos _
  have hz1 : z≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hrS : Real.exp (-x)=(S.card:ℝ)/A := by
    rw [Real.exp_neg,Real.exp_log (div_pos hA hS')]
    simp
  have hrT : Real.exp (-y)=(T.card:ℝ)/B := by
    rw [Real.exp_neg,Real.exp_log (div_pos hB hT')]
    simp
  have hez : z^2=Real.exp (-x)*Real.exp (-y) := by
    rw [sq,←Real.exp_add,show -(x+y)/2+(-(x+y)/2)=(-x)+(-y) by ring,Real.exp_add]
  have hprod : (S.card:ℝ)*T.card=A*B*z^2 := by
    rw [hez,hrS,hrT]
    field_simp
  have H := mixing_cell_scale hdim S T hC hz.le hz1
    (show (S.card:ℝ)*T.card≤C*(Nat.card K:ℝ)^(n+3)*z^2 by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg z))
  have Hlog := Real.log_le_log (show (0:ℝ)< incidenceCount S T by exact_mod_cast he) H
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  rw [Real.log_mul (by positivity : 2*C*(Nat.card K:ℝ)^(n+2)≠0) hz.ne',
    show Real.log z=-(x+y)/2 from Real.log_exp _] at Hlog
  exact Hlog.trans_eq (by dsimp [x,y]; ring)

end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in

lemma incidenceCount_eq_card (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount S T=((S.product T).filter (fun z => Incident z.1 z.2)).card := by
  classical
  simp only [Finset.product_eq_sprod,incidenceCount,Finset.card_filter]
  rw [Finset.sum_product S T,Finset.sum_comm]

end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

lemma positiveSupport_zero (p : Law α) (a : α) (ha : a∉positiveSupport p) : p.mass a=0 := by
  simp only [positiveSupport,mem_filter,mem_univ,true_and,not_lt] at ha
  exact le_antisymm ha (p.nonneg a)

lemma positiveSupport_cell_mass (p : Law α) (f : α→β) (b : β) :
    ∑ a∈(positiveSupport p).filter (fun a => f a=b),p.mass a=(p.map f).mass b := by
  apply sum_subset (by
    intro a ha
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩)
  intro a ha hna
  apply positiveSupport_zero
  intro hs
  exact hna (mem_filter.mpr ⟨hs,(mem_filter.mp ha).2⟩)

lemma positive_cell_nonempty (p : Law α) (f : α→β) (b : β) (hb : 0<(p.map f).mass b) :
    ((positiveSupport p).filter (fun a => f a=b)).Nonempty := by
  by_contra hn
  have he := not_nonempty_iff_eq_empty.mp hn
  have H := positiveSupport_cell_mass p f b
  rw [he,sum_empty] at H
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Incidence
open SharpLogRamsey.Selection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma endpoint_cell_subset
    (p : Law (Projectivization K V × Projectivization K (Module.Dual K V)))
    (hs : ∀ z, 0<p.mass z → Incident z.1 z.2)
    (b : Levels p.fst × Levels p.snd) :
    (positiveSupport p).filter (fun z => endpointLabels p z=b) ⊆
      (((levelSet p.fst b.1).product (levelSet p.snd b.2)).filter (fun z => Incident z.1 z.2)) := by
  intro z hz
  have hp := (mem_filter.mp (mem_filter.mp hz).1).2
  have hl := (mem_filter.mp hz).2
  have ha : (levelIndex p.fst z.1)=b.1 := congrArg Prod.fst hl
  have hb : (levelIndex p.snd z.2)=b.2 := congrArg Prod.snd hl
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,hp.trans_le (p.le_fst z.1 z.2),ha⟩,
      mem_filter.mpr ⟨mem_univ _,hp.trans_le (p.le_snd z.1 z.2),hb⟩⟩,hs z hp⟩

theorem reciprocal_level_losses {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K V × Projectivization K (Module.Dual K V)))
    (hs : ∀ z, 0<p.mass z → Incident z.1 z.2)
    {A B C : ℝ} (hA : 0<A) (hB : 0<B) (hC : 1≤C)
    (hc : A*B≤C*(Nat.card K:ℝ)^(n+3))
    (hSA : ∀ b, ((levelSet p.fst b).card:ℝ)≤A)
    (hTB : ∀ b, ((levelSet p.snd b).card:ℝ)≤B) :
    (∑ b, (p.fst.map (levelIndex p.fst)).mass b*levelLoss p.fst A b)+
      (∑ b, (p.snd.map (levelIndex p.snd)).mass b*levelLoss p.snd B b) ≤
        2*(Real.log (2*C*(Nat.card K:ℝ)^(n+2))-entropy p+
          Real.log (entropy p.fst+2)+Real.log (entropy p.snd+2)+2) := by
  classical
  let l := endpointLabels p
  let loss := fun b : Levels p.fst × Levels p.snd => levelLoss p.fst A b.1+levelLoss p.snd B b.2
  have hcell (b : Levels p.fst × Levels p.snd) (hb : 0<(p.map l).mass b) :
      Real.log ((positiveSupport p).filter (fun z => l z=b)).card ≤
        Real.log (2*C*(Nat.card K:ℝ)^(n+2))-loss b/2 := by
    let S := (positiveSupport p).filter (fun z => l z=b)
    have hn := positive_cell_nonempty p l b hb
    obtain ⟨z,hz⟩ := hn
    have hsub := endpoint_cell_subset p hs b
    have hz' := mem_product.mp (mem_filter.mp (hsub (by simpa only [l] using hz))).1
    have hAS : 0<(levelSet p.fst b.1).card := card_pos.mpr ⟨z.1,hz'.1⟩
    have hBT : 0<(levelSet p.snd b.2).card := card_pos.mpr ⟨z.2,hz'.2⟩
    have hcount : S.card≤ incidenceCount (levelSet p.fst b.1) (levelSet p.snd b.2) := by
      rw [incidenceCount_eq_card]
      exact card_le_card hsub
    have hSn : 0<S.card := card_pos.mpr ⟨z,by simpa only [S,mem_filter] using hz⟩
    have HD := mixing_loss_log hdim (levelSet p.fst b.1) (levelSet p.snd b.2)
      hA hB hC hc hAS hBT (hSA b.1) (hTB b.2) (hSn.trans_le hcount)
    have Hlog : Real.log S.card≤Real.log (incidenceCount (levelSet p.fst b.1) (levelSet p.snd b.2)) :=
      Real.log_le_log (by exact_mod_cast hSn) (by exact_mod_cast hcount)
    exact Hlog.trans HD
  have H := partition_loss p l (positiveSupport p) (positiveSupport_zero p) loss
    (Real.log (2*C*(Nat.card K:ℝ)^(n+2))) (by
      intro b hb
      simpa only [l] using hcell b hb)
  have he : (∑ b, (p.map l).mass b*loss b)=
      (∑ b, (p.fst.map (levelIndex p.fst)).mass b*levelLoss p.fst A b)+
      (∑ b, (p.snd.map (levelIndex p.snd)).mass b*levelLoss p.snd B b) := by
    rw [p.sum_map l loss]
    simp only [loss,l,endpointLabels,mul_add,sum_add_distrib]
    rw [p.fst.sum_map (levelIndex p.fst) (levelLoss p.fst A),
      p.snd.sum_map (levelIndex p.snd) (levelLoss p.snd B)]
    apply congrArg₂ (·+·)
    · simp only [Law.fst,Fintype.sum_prod_type,sum_mul]
    · simp only [Law.snd,Fintype.sum_prod_type,sum_mul]
      rw [sum_comm]
  rw [he] at H
  have HH := endpoint_levels_entropy p
  change entropy (p.map l)≤_ at HH
  linarith

end SharpLogRamsey.Incidence

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

lemma levelSet_card_le_domain (p : Law A) (S : Finset A)
    (hS : ∀ a, a ∉ S → p.mass a = 0) (b : Levels p) :
    (levelSet p b).card ≤ S.card := by
  apply card_le_card
  intro a ha
  by_contra hnot
  have hp := (mem_filter.mp ha).2.1
  rw [hS a hnot] at hp
  exact lt_irrefl _ hp

lemma auxiliarySupport_exists (p : Law A) (good : Finset A) {M κ : ℝ}
    (hM : 0 < M) (hκ : 0 < κ)
    (hcap : ∀ b, ((levelSet p b).card : ℝ) ≤ M)
    (hbudget : (∑ b, (p.map (levelIndex p)).mass b * levelLoss p M b) / κ +
      2 * exp 1 * p.event (univ \ good) ≤ 1/2) :
    Nonempty (AuxiliarySupport p good M κ) := by
  obtain ⟨ρ,hsize,hρ⟩ := auxiliary_supports p good hM hκ hcap hbudget
  exact ⟨⟨ρ,hsize,hρ⟩⟩

lemma mean_levelLoss_nonneg (p : Law A) (M : ℝ)
    (hcap : ∀ b, ((levelSet p b).card : ℝ) ≤ M) :
    0 ≤ ∑ b, (p.map (levelIndex p)).mass b * levelLoss p M b :=
  sum_nonneg (fun b _ => mul_nonneg ((p.map (levelIndex p)).nonneg b)
    (levelLoss_nonneg p b (hcap b)))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem reciprocal_auxiliary_choices {n : ℕ} (hdim : Module.finrank K V = n+3)
    (p : Law (Projectivization K (Module.Dual K V) × Projectivization K V))
    (S : Finset (Projectivization K (Module.Dual K V) × Projectivization K V))
    (DA : Finset (Projectivization K (Module.Dual K V)))
    (DB : Finset (Projectivization K V))
    (hs : ∀ z, z ∉ S → p.mass z = 0)
    (hf : ∀ z, 0 < p.mass z → z.1.rep z.2.rep = 0)
    (hDA : ∀ a, a ∉ DA → p.fst.mass a = 0)
    (hDB : ∀ b, b ∉ DB → p.snd.mass b = 0)
    (MA MB C L κ ε : ℝ) (hMA : 0 < MA) (hMB : 0 < MB) (hC : 1 ≤ C)
    (hA : (DA.card : ℝ) ≤ MA) (hB : (DB.card : ℝ) ≤ MB)
    (hcap : MA * MB ≤ C * (Nat.card K : ℝ)^(n+3))
    (hκ : 0 < κ) (hε : 0 < ε)
    (hsmall :
      (2 * (log (2*C*(Nat.card K:ℝ)^(n+2)) - entropy p +
        log (entropy p.fst+2) + log (entropy p.snd+2) + 2)) / κ +
      2 * exp 1 * (exp (-κ) + (L - entropy p + S.card * exp (-L)) / (κ*ε)) ≤ 1/2) :
    Nonempty (AuxiliarySupport p.fst (univ.filter (goodFirst p MA L κ ε)) MA κ) ∧
    Nonempty (AuxiliarySupport p.snd (univ.filter (goodSecond p MB L κ ε)) MB κ) := by
  have hLA (b : Levels p.fst) : ((levelSet p.fst b).card : ℝ) ≤ MA :=
    (show ((levelSet p.fst b).card : ℝ) ≤ DA.card by
      exact_mod_cast levelSet_card_le_domain p.fst DA hDA b).trans hA
  have hLB (b : Levels p.snd) : ((levelSet p.snd b).card : ℝ) ≤ MB :=
    (show ((levelSet p.snd b).card : ℝ) ≤ DB.card by
      exact_mod_cast levelSet_card_le_domain p.snd DB hDB b).trans hB
  have hloss := Incidence.reciprocal_level_losses hdim p.swap
    (by rintro ⟨a,b⟩ h; exact hf (b,a) (by exact h))
    hMB hMA hC (by simpa only [mul_comm MA] using hcap)
    hLB hLA
  rw [entropy_swap] at hloss
  change (∑ b, (p.snd.map (levelIndex p.snd)).mass b * levelLoss p.snd MB b) +
    (∑ b, (p.fst.map (levelIndex p.fst)).mass b * levelLoss p.fst MA b) ≤
    2 * (log (2*C*(Nat.card K:ℝ)^(n+2)) - entropy p +
      log (entropy p.snd+2) + log (entropy p.fst+2) + 2) at hloss
  have hna := mean_levelLoss_nonneg p.fst MA hLA
  have hnb := mean_levelLoss_nonneg p.snd MB hLB
  have hbadA := badFirst_mass p S hs DA hDA MA L κ ε hMA hA hκ hε
  have hbadB := badSecond_mass p S hs DB hDB MB L κ ε hMB hB hκ hε
  have heA : univ \ univ.filter (goodFirst p MA L κ ε) =
      univ.filter (fun a => ¬goodFirst p MA L κ ε a) := by ext; simp
  have heB : univ \ univ.filter (goodSecond p MB L κ ε) =
      univ.filter (fun a => ¬goodSecond p MB L κ ε a) := by ext; simp
  constructor
  · apply auxiliarySupport_exists p.fst _ hMA hκ hLA
    rw [heA]
    apply le_trans _ hsmall
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ hκ.le
      linarith
    · exact mul_le_mul_of_nonneg_left hbadA (by positivity)
  · apply auxiliarySupport_exists p.snd _ hMB hκ hLB
    rw [heB]
    apply le_trans _ hsmall
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ hκ.le
      linarith
    · exact mul_le_mul_of_nonneg_left hbadB (by positivity)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_SupportThreshold
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

lemma log_entropy_envelope {x A h : ℝ} (hx : 1≤x) (hA : 0≤A)
    (hh : 0≤h) (hcap : h≤A*x) :
    log (h+2) ≤ log (A+2)+log x := by
  have hx0 : 0<x := by linarith
  have hA0 : 0<A+2 := by linarith
  rw [←log_mul hA0.ne' hx0.ne']
  apply log_le_log (by linarith)
  nlinarith

lemma supportErrorEnvelope_tendsto (b C C₀ A : ℝ) (hb : 0<b) :
    Tendsto (supportErrorEnvelope b C C₀ A) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun x : ℝ => (2+100*exp 1)*x^(-2*b)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<2*b by positivity)).const_mul (2+100*exp 1)
  have h₂ : Tendsto (fun x : ℝ =>
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)/x^(4*b)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0<4*b by positivity)).const_mul
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)
    simp only [mul_zero] at h
    apply (h.congr' ?_)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simp only [Real.rpow_neg hx, div_eq_mul_inv]
  have h₃ : Tendsto (fun x : ℝ => 4*log x/x^(4*b)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      ((isLittleO_log_rpow_atTop (show 0<4*b by positivity)).tendsto_div_nhds_zero).const_mul 4
  have h₄ : Tendsto (fun x : ℝ => 2*exp 1*exp (-(x^(4*b)))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop (show 0<4*b by positivity)))
    simpa only [Function.comp_def, mul_zero] using h.const_mul (2*exp 1)
  unfold supportErrorEnvelope
  simpa only [add_zero] using ((h₁.add h₂).add h₃).add h₄

theorem eventually_support_small (b C C₀ A : ℝ) (hb : 0<b)
    (hC : 1≤C) (hC₀ : 0≤C₀) (hA : 0≤A) :
    ∀ᶠ x : ℝ in atTop, ∀ κ δ H HA HB L S : ℝ,
      x^(4*b)≤κ → δ≤κ*x^(-2*b) → L-H≤δ → S*exp (-L)≤C₀ →
      0≤HA → HA≤A*x → 0≤HB → HB≤A*x →
      (2*(log (2*C)+L-H+log (HA+2)+log (HB+2)+2))/κ+
        2*exp 1*(exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))) ≤ 1/2 := by
  filter_upwards [(supportErrorEnvelope_tendsto b C C₀ A hb).eventually
      (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), eventually_ge_atTop (1:ℝ)] with x he hx
  intro κ δ H HA HB L S hκ hδ hH hS hHA0 hHA hHB0 hHB
  have hx0 : 0<x := by linarith
  have hxpow : 0<x^(4*b) := rpow_pos_of_pos hx0 _
  have hκ0 : 0<κ := hxpow.trans_le hκ
  have hlA := log_entropy_envelope hx hA hHA0 hHA
  have hlB := log_entropy_envelope hx hA hHB0 hHB
  have hlogx : 0≤log x := log_nonneg hx
  have hlogC : 0≤log (2*C) := log_nonneg (by linarith)
  have hlogA : 0≤log (A+2) := log_nonneg (by linarith)
  have hdiv : δ/κ≤x^(-2*b) := (div_le_iff₀ hκ0).mpr (by simpa only [mul_comm κ] using hδ)
  have hconst0 : 0≤2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀ := by positivity
  have hconst := div_le_div_of_nonneg_left hconst0 hxpow hκ
  have hlog := div_le_div_of_nonneg_left (show 0≤4*log x by positivity) hxpow hκ
  have hexp : exp (-κ)≤exp (-(x^(4*b))) := exp_le_exp.mpr (neg_le_neg hκ)
  have hfirst : (2*(log (2*C)+L-H+log (HA+2)+log (HB+2)+2))/κ ≤
      (2*(log (2*C)+δ+2*(log (A+2)+log x)+2))/κ := by
    apply div_le_div_of_nonneg_right _ hκ0.le
    linarith
  have hsecond : 2*exp 1*(exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))) ≤
      2*exp 1*(exp (-κ)+(δ+C₀)/(κ*(1/50))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hsplit : (2*(log (2*C)+δ+2*(log (A+2)+log x)+2))/κ+
      2*exp 1*(exp (-κ)+(δ+C₀)/(κ*(1/50))) =
      (2+100*exp 1)*(δ/κ)+
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)/κ+
      4*log x/κ+2*exp 1*exp (-κ) := by ring
  apply (add_le_add hfirst hsecond).trans
  rw [hsplit]
  apply le_trans _ he.le
  unfold supportErrorEnvelope
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hdiv (by positivity)) hconst) hlog)
      (mul_le_mul_of_nonneg_left hexp (by positivity))

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_UniformSupports
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

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)]

lemma projective_entropy_le {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K V)) :
    entropy p ≤ (n+3:ℕ)*log (Nat.card K) := by
  have hq : (2:ℝ)≤Nat.card K := by
    exact_mod_cast (show 2≤Nat.card K from Finite.one_lt_card)
  have hc : (Fintype.card (Projectivization K V):ℝ) ≤ (Nat.card K:ℝ)^(n+3) := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,
      Nat.cast_sum]
    simp only [Nat.cast_pow]
    apply (sum_powers_le_twice hq (by omega : 0<n+3)).trans
    simp only [show n+3-1=n+2 by omega]
    calc
      _ ≤ (Nat.card K:ℝ)*(Nat.card K:ℝ)^(n+2) :=
        mul_le_mul_of_nonneg_right hq (pow_nonneg (by linarith) _)
      _ = (Nat.card K:ℝ)^(n+3) := by
        simpa only [mul_comm] using (pow_succ (Nat.card K:ℝ) (n+2)).symm
  have hp : (0:ℝ)<Fintype.card (Projectivization K V) := by
    have : Nontrivial V := (Module.finrank_pos_iff (R := K)).mp (by omega)
    exact_mod_cast Fintype.card_pos (α := Projectivization K V)
  apply (entropy_le_log_card p univ (by simp)).trans
  simp only [card_univ]
  apply (log_le_log hp hc).trans
  rw [log_pow]

variable [Fintype (Projectivization K (Module.Dual K V))]

theorem eventually_reciprocal_auxiliary_choices (n : ℕ) (b C C₀ : ℝ)
    (hb : 0<b) (hC : 1≤C) (hC₀ : 0≤C₀) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=n+3 → log (Nat.card K)=σ →
      ∀ (p : Law (Projectivization K (Module.Dual K V) × Projectivization K V))
        (S : Finset (Projectivization K (Module.Dual K V) × Projectivization K V))
        (DA : Finset (Projectivization K (Module.Dual K V)))
        (DB : Finset (Projectivization K V)) (MA MB κ δ : ℝ),
        (∀ z,z∉S→p.mass z=0) →
        (∀ z,0<p.mass z→z.1.rep z.2.rep=0) →
        (∀ a,a∉DA→p.fst.mass a=0) →
        (∀ a,a∉DB→p.snd.mass a=0) →
        0<MA → 0<MB → (DA.card:ℝ)≤MA → (DB.card:ℝ)≤MB →
        MA*MB≤C*(Nat.card K:ℝ)^(n+3) →
        (S.card:ℝ)≤C₀*(Nat.card K:ℝ)^(n+2) →
        σ^(4*b)≤κ → δ≤κ*σ^(-2*b) → (n+2:ℕ)*σ-entropy p≤δ →
        Nonempty (AuxiliarySupport p.fst
          (univ.filter (goodFirst p MA ((n+2:ℕ)*σ) κ (1/50))) MA κ) ∧
        Nonempty (AuxiliarySupport p.snd
          (univ.filter (goodSecond p MB ((n+2:ℕ)*σ) κ (1/50))) MB κ) := by
  filter_upwards [eventually_support_small b C C₀ (n+3) hb hC hC₀ (by positivity),
      eventually_ge_atTop (1:ℝ)] with σ he hσ
  intro K V _ _ _ _ _ _ _ hdim hlog p S DA DB MA MB κ δ hs hf hDA hDB
    hMA hMB hA hB hcap hS hκ hδ hdef
  have hσ0 : 0<σ := by linarith
  have hκ0 : 0<κ := (rpow_pos_of_pos hσ0 (4*b)).trans_le hκ
  have hq : (0:ℝ)<Nat.card K := by
    exact_mod_cast (show 0<Nat.card K from Nat.zero_lt_one.trans Finite.one_lt_card)
  have hn : exp ((n+2:ℕ)*σ)=(Nat.card K:ℝ)^(n+2) := by
    rw [←hlog,exp_nat_mul,exp_log hq]
  have hSn : (S.card:ℝ)*exp (-((n+2:ℕ)*σ))≤C₀ := by
    have h := mul_le_mul_of_nonneg_right hS (le_of_lt (exp_pos (-((n+2:ℕ)*σ))))
    rw [←hn,mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one] at h
    exact h
  have hHA := projective_entropy_le (V:=Module.Dual K V)
    (by simpa only [Subspace.dual_finrank_eq] using hdim) p.fst
  have hHB := projective_entropy_le hdim p.snd
  rw [hlog] at hHA hHB
  have hnlog : log (2*C*(Nat.card K:ℝ)^(n+2)) = log (2*C)+(n+2:ℕ)*σ := by
    rw [log_mul (by positivity : 2*C≠0) (pow_ne_zero _ hq.ne'),log_pow,hlog]
  apply reciprocal_auxiliary_choices hdim p S DA DB hs hf hDA hDB
    MA MB C ((n+2:ℕ)*σ) κ (1/50) hMA hMB hC hA hB hcap hκ0 (by norm_num)
  rw [hnlog]
  exact he κ δ (entropy p) (entropy p.fst) (entropy p.snd) ((n+2:ℕ)*σ)
    S.card hκ hδ hdef hSn (entropy_nonneg _)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hHA) (entropy_nonneg _)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hHB)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection SharpLogRamsey.MomentBudgetBridge

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

end SharpLogRamsey.SourceScales
end

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

lemma prepared_marginal_property (P : Θ→ι→β→Prop)
    (hP : ∀ ω,p.mass ω≠0→∀ i,P (θ ω) i (G ω i))
    (i : (contextual n k p θ G e own t).Index z.1) :
    ∀ a,(((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a≠0→
      P z.1.1 ((contextual n k p θ G e own t).origin z.1 i) a := by
  intro a ha
  obtain ⟨ω,hω,hθ,hG⟩:=prepared_marginal_source n k p θ G e own t hp z hz i a ha
  simpa only [hθ,hG] using hP ω hω ((contextual n k p θ G e own t).origin z.1 i)

end
end SharpLogRamsey.Selection.ExposureModel

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

variable {A B : Type*} [Fintype A] [Fintype B]

theorem actual_endpoint_errors (p : Law (A×B)) (S : Finset (A×B))
    (DA : Finset A) (DB : Finset B)
    (hs : ∀ z,z∉S→p.mass z=0)
    (ha : ∀ a,a∉DA→p.fst.mass a=0) (hb : ∀ b,b∉DB→p.snd.mass b=0)
    (MA MB L κ x β δ C₀ : ℝ) (hMA : 0<MA) (hMB : 0<MB)
    (hA : (DA.card:ℝ)≤MA) (hB : (DB.card:ℝ)≤MB)
    (hx : 1≤x) (hβ : 0≤β) (hC₀ : 0≤C₀)
    (hκ : x^(4*β)≤κ) (hδ : δ≤κ*x^(-2*β))
    (hdef : L-entropy p≤δ) (hS : (S.card:ℝ)*exp (-L)≤C₀) :
    p.fst.event (univ.filter (fun a=>¬goodFirst p MA L κ (1/50) a))≤(51+50*C₀)*x^(-2*β) ∧
    p.snd.event (univ.filter (fun b=>¬goodSecond p MB L κ (1/50) b))≤(51+50*C₀)*x^(-2*β) := by
  have hκ0 : 0<κ := (rpow_pos_of_pos (by linarith : 0<x) (4*β)).trans_le hκ
  have he:=endpoint_error_scale hx hβ hC₀ hκ hδ hdef hS
  exact ⟨(badFirst_mass p S hs DA ha MA L κ (1/50) hMA hA hκ0 (by norm_num)).trans he,
    (badSecond_mass p S hs DB hb MB L κ (1/50) hMB hB hκ0 (by norm_num)).trans he⟩

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_IntegerScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma K_le_Kstar {σ η D : ℝ} (hσ : 1≤σ) (hη : 0<η) (hD : 0≤D) :
    scaleK σ η D≤ scaleKstar σ η D := by
  unfold scaleK scaleKstar
  apply mul_le_mul_of_nonneg_left _ hD
  exact rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη; linarith)

theorem eventually_integer_regime (η : ℝ) (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ,σ^beta η≤D → D≤σ^(1-η/2) →
      log 1024+3*scaleK σ η D+scaleKstar σ η D<σ ∧
      log (200/97)≤ scaleK σ η D ∧
      2*scaleKstar σ η D+2*scaleK σ η D+log 4≤16*scaleKstar σ η D ∧
      0<σ^(-100*beta η) ∧ σ^(-100*beta η)≤1/40000 := by
  have hb:=beta_pos hη
  have hneg : 0<η/2-6*beta η := by unfold beta; linarith
  have ha : Tendsto (fun σ : ℝ=>σ^(-η/2+6*beta η)) atTop (𝓝 0) := by
    rw [show -η/2+6*beta η = -(η/2-6*beta η) by ring]
    exact tendsto_rpow_neg_atTop hneg
  have ht : Tendsto (fun σ : ℝ=>log 1024*σ^(-1:ℝ)+4*σ^(-η/2+6*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).const_mul (log 1024)).add (ha.const_mul 4)
  have hg : Tendsto (fun σ : ℝ=>σ^(4*beta η)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hτ : Tendsto (fun σ : ℝ=>σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using
      tendsto_rpow_neg_atTop (show 0<100*beta η by positivity)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hg.eventually (eventually_ge_atTop (log (200/97))),
    hτ.eventually (gt_mem_nhds (show (0:ℝ)<1/40000 by norm_num))] with σ hσ hs hg hτ D hDl hDu
  have hσ0 : 0<σ := by linarith
  have hD : 1≤D := (one_le_rpow hσ hb.le).trans hDl
  have hKK:=K_le_Kstar hσ hη (by linarith : 0≤D)
  have hK : σ^(4*beta η)≤ scaleK σ η D := by
    calc
      _ = σ^beta η*σ^(3*beta η) := by rw [←rpow_add hσ0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDl (by positivity)
  have hKu : scaleKstar σ η D≤σ^(1-η/2+6*beta η) := by
    unfold scaleKstar
    rw [rpow_add hσ0]
    exact mul_le_mul_of_nonneg_right hDu (by positivity)
  have hK1 : 1≤ scaleKstar σ η D :=
    one_le_mul_of_one_le_of_one_le hD (one_le_rpow hσ (by positivity))
  refine ⟨?_,hg.trans hK,?_,rpow_pos_of_pos hσ0 _,hτ.le⟩
  · have hh : log 1024+4*σ^(1-η/2+6*beta η)<σ := by
      have he : log 1024*σ^(-1:ℝ)+4*σ^(-η/2+6*beta η)=
          (log 1024+4*σ^(1-η/2+6*beta η))/σ := by
        have hep : σ^(1-η/2+6*beta η)/σ=σ^(-η/2+6*beta η) := by
          calc
            _ = σ^(1-η/2+6*beta η)/σ^(1:ℝ) := by rw [rpow_one]
            _ = _ := by rw [←rpow_sub hσ0]; congr 1; ring
        rw [rpow_neg_one,add_div,mul_div_assoc,hep]
        ring
      rw [he] at hs
      simpa only [one_mul] using (div_lt_iff₀ hσ0).mp hs
    linarith
  · have hlog : log (4:ℝ)≤3 := by
      have hh:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      linarith
    linarith
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_ReciprocalScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter
open scoped Topology
noncomputable section

lemma treeErrorEnvelope_tendsto (β C : ℝ) (hβ : 0<β) :
    Tendsto (treeErrorEnvelope β C) atTop (𝓝 0) := by
  have hp (a : ℝ) (ha : 0<a) : Tendsto (fun x : ℝ=>x^(-a*β)) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (mul_pos ha hβ)
  have he : Tendsto (fun x : ℝ=>x^β*exp (-x)) atTop (𝓝 0) := by
    simpa only [neg_one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero β 1 (by norm_num)
  unfold treeErrorEnvelope
  simpa only [mul_zero,add_zero] using
    ((((hp 1998 (by norm_num)).const_mul (240*(4*exp 1)^2*C)).add
      ((hp 1899 (by norm_num)).const_mul ((4*exp 1)^2*C))).add
      (he.const_mul 2)).add ((hp 2 (by norm_num)).const_mul (2*C)) |>.add
      ((hp 1999 (by norm_num)).const_mul (48*(4*exp 1)*C))

lemma treeError_le_envelope {β C x q h ε εA εB δA δB : ℝ}
    (hβ : 0<β) (hC : 0≤C) (hx : 1≤x) (hq : x≤q)
    (hh0 : 0≤h) (hh : h≤x^β) (hε : 0≤ε)
    (hεA : 0≤εA) (hεB : 0≤εB)
    (he : q*ε≤C*x^(-2000*β)) (heA : q*εA≤C*x^(-2000*β))
    (heB : q*εB≤C*x^(-2000*β))
    (hdA : δA≤C*x^(-2*β)) (hdB : δB≤C*x^(-2*β)) :
    treeError q (x^(-100*β)) h ε εA εB δA δB≤treeErrorEnvelope β C x := by
  have hx0 : 0<x := by linarith
  have hq0 : 0≤q := by linarith
  have hxβ : 1≤x^β := one_le_rpow hx hβ.le
  have hexp : exp (-q)≤exp (-x) := exp_le_exp.mpr (neg_le_neg hq)
  have hfirst : 240*(4*exp 1)^2*(q*ε)*h^2≤
      240*(4*exp 1)^2*(C*x^(-2000*β))*(x^β)^2 := by
    calc
      _ ≤ 240*(4*exp 1)^2*(q*ε)*(x^β)^2 := by
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh0 hh 2)
        exact mul_nonneg (by positivity) (mul_nonneg hq0 hε)
      _ ≤ _ := by gcongr
  have hsecond : ((4*exp 1)^2*(q*ε)/x^(-100*β))*h≤
      ((4*exp 1)^2*(C*x^(-2000*β))/x^(-100*β))*x^β := by gcongr
  have hfail : 2*exp (-q)*h≤2*exp (-x)*x^β := by gcongr
  have hlast : (h+1)*(12*(4*exp 1)*(q*εA)+12*(4*exp 1)*(q*εB))≤
      (2*x^β)*(24*(4*exp 1)*(C*x^(-2000*β))) := by
    have ha : h+1≤2*x^β := by linarith
    apply mul_le_mul ha _ (by positivity) (by positivity)
    have h1:=mul_le_mul_of_nonneg_left heA (show 0≤12*(4*exp 1) by positivity)
    have h2:=mul_le_mul_of_nonneg_left heB (show 0≤12*(4*exp 1) by positivity)
    linarith
  have p1 : x^(-2000*β)*(x^β)^2=x^(-1998*β) := by
    rw [←rpow_mul_natCast hx0.le,←rpow_add hx0]; congr 1; ring
  have p2 : x^(-2000*β)/x^(-100*β)*x^β=x^(-1899*β) := by
    rw [←rpow_sub hx0,←rpow_add hx0]; congr 1; ring
  have p3 : x^β*x^(-2000*β)=x^(-1999*β) := by
    rw [←rpow_add hx0]; congr 1; ring
  unfold treeError treeErrorEnvelope
  calc
    _ ≤ 240*(4*exp 1)^2*(C*x^(-2000*β))*(x^β)^2+
        ((4*exp 1)^2*(C*x^(-2000*β))/x^(-100*β))*x^β+
        2*exp (-x)*x^β+(C*x^(-2*β)+C*x^(-2*β))+
        (2*x^β)*(24*(4*exp 1)*(C*x^(-2000*β))) := by
      convert add_le_add (add_le_add (add_le_add (add_le_add hfirst hsecond) hfail)
        (add_le_add hdA hdB)) hlast using 1 <;> first | rfl | ring
    _ = _ := by
      have h1 : 240*(4*exp 1)^2*(C*x^(-2000*β))*(x^β)^2=
          240*(4*exp 1)^2*C*x^(-1998*β) := by rw [←p1]; ring
      have h2 : ((4*exp 1)^2*(C*x^(-2000*β))/x^(-100*β))*x^β=
          (4*exp 1)^2*C*x^(-1899*β) := by rw [←p2]; ring
      have h3 : (2*x^β)*(24*(4*exp 1)*(C*x^(-2000*β)))=
          48*(4*exp 1)*C*x^(-1999*β) := by rw [←p3]; ring
      rw [h1,h2,h3]; ring

theorem eventually_tree_small (β C e : ℝ) (hβ : 0<β) (hC : 0≤C) (he : 0<e) :
    ∀ᶠ x : ℝ in atTop,∀ q h ε εA εB δA δB : ℝ,
      x≤q → 0≤h → h≤x^β → 0≤ε → 0≤εA → 0≤εB →
      q*ε≤C*x^(-2000*β) → q*εA≤C*x^(-2000*β) → q*εB≤C*x^(-2000*β) →
      δA≤C*x^(-2*β) → δB≤C*x^(-2*β) →
      treeError q (x^(-100*β)) h ε εA εB δA δB≤e := by
  filter_upwards [(treeErrorEnvelope_tendsto β C hβ).eventually
      (gt_mem_nhds he),eventually_ge_atTop (1:ℝ)] with x hex hx
  intro q h ε εA εB δA δB hq hh0 hh hε hεA hεB he0 heA heB hdA hdB
  exact (treeError_le_envelope hβ hC hx hq hh0 hh hε hεA hεB he0 heA heB hdA hdB).trans hex.le

end
end SharpLogRamsey.ActualPivot

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

theorem eventually_actual_reciprocal (n : ℕ) (β : ℝ) (hβ : 0<β) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=n+3 → log (Nat.card K)=σ →
      ∀ (p : Law (Projectivization K (Module.Dual K V)×Projectivization K V))
        (S : Finset (Projectivization K (Module.Dual K V)×Projectivization K V)) (D u : ℝ),
        (∀ a,a∉S→p.mass a=0) →
        (∀ a,0<p.mass a→a.1.rep a.2.rep=0) →
        ((S.image Prod.fst).card:ℝ)≤1024*exp (((n+3:ℕ):ℝ)*σ-u) →
        ((S.image Prod.snd).card:ℝ)≤1024*exp u →
        (S.card:ℝ)≤64*(Nat.card K:ℝ)^(n+2) → σ^β≤D →
        ((n+2:ℕ):ℝ)*σ-entropy p≤D*σ^β →
        let MA:=1024*exp (((n+3:ℕ):ℝ)*σ-u)
        let MB:=1024*exp u
        let L:=((n+2:ℕ):ℝ)*σ
        let κ:=D*σ^(3*β)
        Nonempty (AuxiliarySupport p.fst (univ.filter (goodFirst p MA L κ (1/50))) MA κ) ∧
        Nonempty (AuxiliarySupport p.snd (univ.filter (goodSecond p MB L κ (1/50))) MB κ) ∧
        p.fst.event (univ.filter (fun a=>¬goodFirst p MA L κ (1/50) a))≤3251*σ^(-2*β) ∧
        p.snd.event (univ.filter (fun b=>¬goodSecond p MB L κ (1/50) b))≤3251*σ^(-2*β) := by
  filter_upwards [eventually_reciprocal_auxiliary_choices n β (1024^2) 64 hβ
      (by norm_num) (by norm_num),eventually_ge_atTop (1:ℝ)] with σ he hσ
  intro K V _ _ _ _ _ _ _ hdim hlog p S D u hs hf hA hB hS hD hdef
  have hσ0 : 0<σ := by linarith
  have hq : (0:ℝ)<Nat.card K := by
    exact_mod_cast (show 0<Nat.card K from Nat.zero_lt_one.trans Finite.one_lt_card)
  have hA0 : 0<1024*exp (((n+3:ℕ):ℝ)*σ-u) := by positivity
  have hB0 : 0<1024*exp u := by positivity
  have ha := p.map_image_support S Prod.fst hs
  have hb := p.map_image_support S Prod.snd hs
  rw [Law.map_fst] at ha
  rw [Law.map_snd] at hb
  have hcap : (1024*exp (((n+3:ℕ):ℝ)*σ-u))*(1024*exp u)≤
      1024^2*(Nat.card K:ℝ)^(n+3) := by
    rw [show (1024*exp (((n+3:ℕ):ℝ)*σ-u))*(1024*exp u)=
      1024^2*exp (((n+3:ℕ):ℝ)*σ) by rw [show ((n+3:ℕ):ℝ)*σ=(((n+3:ℕ):ℝ)*σ-u)+u by ring,exp_add]; ring_nf]
    rw [←hlog,exp_nat_mul,exp_log hq]
  have hsc:=reciprocal_source_scales hσ0 hD
  have hch:=he K V hdim hlog p S (S.image Prod.fst) (S.image Prod.snd) _ _ _ _
    hs hf ha hb hA0 hB0 hA hB hcap hS hsc.1 hsc.2 hdef
  have hp : (S.card:ℝ)*exp (-(((n+2:ℕ):ℝ)*σ))≤64 := by
    have hh:=mul_le_mul_of_nonneg_right hS (le_of_lt (exp_pos (-(((n+2:ℕ):ℝ)*σ))))
    have hn : exp (((n+2:ℕ):ℝ)*σ)=(Nat.card K:ℝ)^(n+2) := by
      rw [←hlog,exp_nat_mul,exp_log hq]
    rw [←hn,mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one] at hh
    exact hh
  have herr:=actual_endpoint_errors p S (S.image Prod.fst) (S.image Prod.snd) hs ha hb
    _ _ _ _ σ β (D*σ^β) 64 hA0 hB0 hA hB hσ hβ.le (by norm_num) hsc.1 hsc.2 hdef hp
  exact ⟨hch.1,hch.2,by norm_num only at herr ⊢; exact herr⟩

end
end SharpLogRamsey.Selection

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

theorem eventually_prepared_reciprocal (d : ℕ) (β : ℝ) (hβ : 0<β) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ (Ω Θ ι C : Type) [Fintype Ω] [Fintype Θ] [Fintype ι] [DecidableEq ι] [Fintype C]
        (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→ι→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→ι→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→ι→ℝ) (n k : ℕ) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C)
        (t : Fin k) (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
        (D J a : ℝ),
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        σ^β≤D → ((d+2:ℕ):ℝ)*σ≤J →
        ∀ (z : (contextual n k p θ G e own t).FreshHistory)
          (c : (contextual n k p θ G e own t).Index z.1→
            (contextual n k p θ G e own t).Index z.1→NNReal),
          ((contextual n k p θ G e own t).freshLaw hp).mass z≠0 →
          ∀ i,i∉badIndices ((contextual n k p θ G e own t).tupleLaw z.1)
            ((contextual n k p θ G e own t).embedding z.1)
            ((contextual n k p θ G e own t).owner z.1) c J (D*σ^β) a z.2 →
          let q:=((contextual n k p θ G e own t).tupleLaw z.1).marginal i
          let ui:=u z.1.1 ((contextual n k p θ G e own t).origin z.1 i)
          let MA:=1024*exp (((d+3:ℕ):ℝ)*σ-ui)
          let MB:=1024*exp ui
          let L:=((d+2:ℕ):ℝ)*σ
          let κ:=D*σ^(3*β)
          Nonempty (AuxiliarySupport q.fst (univ.filter (goodFirst q MA L κ (1/50))) MA κ) ∧
          Nonempty (AuxiliarySupport q.snd (univ.filter (goodSecond q MB L κ (1/50))) MB κ) ∧
          q.fst.event (univ.filter (fun x=>¬goodFirst q MA L κ (1/50) x))≤3251*σ^(-2*β) ∧
          q.snd.event (univ.filter (fun x=>¬goodSecond q MB L κ (1/50) x))≤3251*σ^(-2*β) := by
  filter_upwards [eventually_actual_reciprocal d β hβ] with σ he
  intro K V _ _ _ _ _ _ _ hdim hlog Ω Θ ι C _ _ _ _ _ p θ G S u n k e own t hp D J a
    hS hf hcap hD hJ z c hz i hi
  let M:=contextual n k p θ G e own t
  have hd:=((not_badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
    c J (D*σ^β) a z.2 i).mp hi).1
  have hcaps:=prepared_context_property n k p θ G e own t hp z hz
    (fun θ=>∀ i,(((S θ i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u θ i) ∧
      (((S θ i).image Prod.snd).card:ℝ)≤1024*exp (u θ i) ∧
      ((S θ i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) hcap
  apply he K V hdim hlog (M.tupleLaw z.1|>.marginal i) (S z.1.1 (M.origin z.1 i)) D
    (u z.1.1 (M.origin z.1 i))
  · exact prepared_marginal_domain n k p θ G e own t hp z hz S hS i
  · intro x hx
    exact prepared_marginal_property n k p θ G e own t hp z hz
      (fun _ _ x=>x.1.rep x.2.rep=0) hf i x (ne_of_gt hx)
  · exact (hcaps _).1
  · exact (hcaps _).2.1
  · exact (hcaps _).2.2
  · exact hD
  · exact (sub_le_sub_right hJ _).trans hd
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_ChronologicalTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree

open BinaryTree

lemma balanced_height (lo n : ℕ) : (balanced lo n).height≤Nat.log 2 n+1 := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rw [balanced]
    split_ifs with h
    · simp
    · simp only [height]
      by_cases hn : n=1
      · subst n
        simp [balanced]
      have hn2 : 2≤n := by omega
      have hl : n/2<n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      have hr : n-n/2-1<n := by omega
      have hrle : n-n/2-1≤n/2 := by omega
      have h1 := ih (n/2) hl (lo:=lo)
      have h2 := ih (n-n/2-1) hr (lo:=lo+n/2+1)
      have hlog := Nat.log_monotone (b:=2) hrle
      have he := Nat.log_div_base 2 n
      have hp : 0<Nat.log 2 n := Nat.log_pos (by decide) hn2
      omega

end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_BalancedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree
open BinaryTree Finset FreshExecution
open scoped Classical
noncomputable section

variable {I : Type*} [LinearOrder I]

lemma map_height {A B : Type*} (f : A→B) (t : BinaryTree A) : (t.map f).height=t.height := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [BinaryTree.map,height,hl,hr]

attribute [local instance] OAI.SharpLogRamsey.ChronologicalTree.liveEq
lemma liveTree_height (S : Finset I) (fallback : I) :
    (liveTree S fallback).height≤Nat.log 2 S.card+1 := by
  rw [liveTree,map_height]
  exact balanced_height _ _

end
end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreeHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree
open Finset Filter Real BinaryTree
open scoped Classical Topology
noncomputable section

lemma eventually_natLog_small (β C a : ℝ) (hβ : 0<β) (hC : 0<C) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,(n:ℝ)≤C*x^a → (Nat.log 2 n:ℝ)+1≤x^β := by
  have hp : Tendsto (fun x : ℝ=>x^(-β)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hβ
  have hl := (isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero
  have ht : Tendsto (fun x : ℝ=>(log C/log 2+1)*x^(-β)+(a/log 2)*(log x/x^β))
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (hp.const_mul (log C/log 2+1)).add (hl.const_mul (a/log 2))
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop (1:ℝ)] with x hx hx1 n hn
  have hx0 : 0<x := by linarith
  have hp0 : 0<x^β := rpow_pos_of_pos hx0 _
  have hd : 0<log (2:ℝ) := log_pos (by norm_num)
  have hlog : (log C/log 2+1)+(a/log 2)*log x≤x^β := by
    have he : (log C/log 2+1)*x^(-β)+(a/log 2)*(log x/x^β)=
        ((log C/log 2+1)+(a/log 2)*log x)/x^β := by
      rw [rpow_neg hx0.le]
      ring
    rw [he] at hx
    simpa only [one_mul] using ((div_lt_iff₀ hp0).mp hx).le
  rcases eq_or_ne n 0 with rfl|hn0
  · simpa using one_le_rpow hx1 hβ.le
  · have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnlog : log (n:ℝ)≤log C+a*log x := by
      calc
        _ ≤ log (C*x^a) := log_le_log hnpos hn
        _ = _ := by rw [log_mul hC.ne' (rpow_pos_of_pos hx0 a).ne',log_rpow hx0]
    have hnat := Real.natLog_le_logb n 2
    dsimp only [logb] at hnat
    norm_num only [Nat.cast_ofNat] at hnat
    calc
      (Nat.log 2 n:ℝ)+1 ≤ log (n:ℝ)/log 2+1 := by linarith only [hnat]
      _ ≤ (log C+a*log x)/log 2+1 := by gcongr
      _ = (log C/log 2+1)+(a/log 2)*log x := by ring
      _ ≤ _ := hlog

theorem eventually_liveTree_height (β C a : ℝ) (hβ : 0<β) (hC : 0<C) :
    ∀ᶠ x : ℝ in atTop, ∀ w : ℕ,(w:ℝ)≤C*x^a →
      ∀ (live : Finset (Fin w)) (fallback : Fin w),
        ((liveTree live fallback).height:ℝ)≤x^β := by
  filter_upwards [eventually_natLog_small β C a hβ hC] with x hx w hw live fallback
  have hcard : (live.card:ℝ)≤(w:ℝ) := by
    exact_mod_cast (show live.card≤w by simpa using card_le_univ live)
  calc
    _ ≤ (Nat.log 2 live.card:ℝ)+1 := by exact_mod_cast liveTree_height live fallback
    _ ≤ x^β := hx live.card (hcard.trans hw)
end
end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_UniformInteger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.uniformIntBanks
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.uniformIntFinDec
local instance uniformIntSlotDec_r8e5915_1 (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.uniformIntBlockDec
theorem eventually_integer_decoder_oai (d : ℕ) (η C A loss : ℝ)
    (hη : 0<η) (hC : 0<C) (hloss : 0<loss) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      ∀ (hdim : Module.finrank K V=d+3), log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
        (hτ : 0≤τ) (hτsmall : τ≤1/40000)
        (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J : ℝ),
        (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,IntegerBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
          (z : (model w n k p θ G t).FreshHistory),
          ((model w n k p θ G t).freshLaw hp).mass z≠0 →
          ∀ fallback : Fin w,
          let M:=model w n k p θ G t
          let q:=M.tupleLaw z.1
          let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
          let c:=reciprocalCharges q Projectivization.rep Projectivization.rep
            (1/(100*((d:ℝ)+3))) r (d+3-r)
          let bad:=badIndices q (M.embedding z.1) (M.owner z.1) c J (D*σ^beta η) a z.2
          let live:=univ\badWindows (M.representative z) bad
          ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) q,
            (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
              ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
              (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
                (fun i=>book.chronoChoose hdim hτ hτsmall (e.supports ω i))
                (fun _=>chronoRead b)
                (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) tab
                (liveTree live fallback) (univ,univ)).length))≤
              (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*loss := by
  let E:=20000*((d:ℝ)+3)^2+8
  let CE:=E+3251
  have hb:=beta_pos hη
  have hCE : 0≤CE := by dsimp [CE,E]; positivity
  filter_upwards [eventually_prepared_reciprocal d (beta η) hb,
    eventually_integer_regime η hη,eventually_liveTree_height (beta η) C A hb hC,
    eventually_tree_small (beta η) CE loss hb hCE hloss,
    eventually_ge_atTop (1:ℝ)] with σ hsupp hreg hheight htree hσ
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hτ0 hτsmall Ω Θ _ _ w n k p θ G S u r J hw hr hJ hS hf hcon hcap hband t hp z hz fallback
  let M:=model w n k p θ G t
  let q:=M.tupleLaw z.1
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  let κ:=scaleK σ η D
  let gap:=scaleKstar σ η D
  let b:=16*gap
  let τ:=σ^(-100*beta η)
  let c:=reciprocalCharges q Projectivization.rep Projectivization.rep (1/(100*((d:ℝ)+3))) r (d+3-r)
  let bad:=badIndices q (M.embedding z.1) (M.owner z.1) c J (D*σ^beta η) a z.2
  let live:=univ\badWindows (M.representative z) bad
  have hσ0 : 0<σ := by linarith
  have hD : 0<D := (rpow_pos_of_pos hσ0 _).trans_le hDl
  have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  have hreg':=hreg D hDl hDu
  have hpb : ∀ i,IntegerBand r (log (Nat.card K)) gap (u z.1.1 (M.origin z.1 i)) := by
    have hh:=prepared_context_property n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz
      (fun θ=>∀ i,IntegerBand r σ gap (u θ i)) hband
    intro i
    rw [hlog]
    exact hh _
  obtain ⟨e,he⟩:=integer_population_realization w n k p θ G t hp z hz hdim book
    (by dsimp [b,gap,scaleKstar]; positivity) hreg'.2.2.2.1 hreg'.2.2.2.2
    r hr κ gap J (D*σ^beta η) a (3251*σ^(-2*beta η))
    (fun i=>u z.1.1 (M.origin z.1 i)) hpb
    (by simpa only [κ,gap,hlog] using hreg'.1) hreg'.2.1 hreg'.2.2.1
    (by dsimp [a]; positivity) hcon hf fallback (by
      dsimp only
      intro i hi
      have hh:=hsupp K V hdim hlog Ω Θ (Slot w (n+k)) (Block w) p θ G S u n k
        (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp D J a hS hf hcap hDl hJ z c hz i hi
      simpa only [hlog,κ,scaleK] using hh)
  refine ⟨e,he.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply htree (Nat.card K) ((liveTree live fallback).height:ℝ) (E*a) (E*a) (E*a)
    (3251*σ^(-2*beta η)) (3251*σ^(-2*beta η))
  · rw [←hlog]
    exact (log_le_sub_one_of_pos hq0).trans (by linarith)
  · positivity
  · exact hheight w hw live fallback
  · dsimp [E,a]; positivity
  · dsimp [E,a]; positivity
  · dsimp [E,a]; positivity
  all_goals first
    | (have heq : (Nat.card K:ℝ)*(E*a)=E*σ^(-2000*beta η) := by dsimp [a]; field_simp [ne_of_gt hq0]
       rw [heq]
       apply mul_le_mul_of_nonneg_right _ (by positivity)
       dsimp [CE]; linarith)
    | (apply mul_le_mul_of_nonneg_right _ (by positivity)
       dsimp [CE,E]
       nlinarith [sq_nonneg ((d:ℝ)+3)])
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Selection.Windows.eventually_integer_decoder_oai := @OAI.SharpLogRamsey.Selection.Windows.eventually_integer_decoder_oai
