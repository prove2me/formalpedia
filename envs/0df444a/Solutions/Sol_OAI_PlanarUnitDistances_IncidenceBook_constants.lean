-- Prove2me | solution 1 for OAI.PlanarUnitDistances.IncidenceBook.constants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T03:00:55.41666+00:00
-- url     : https://prove2.me/submissions/8f257eba-dbfc-4545-b61e-afd771158f67

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceScale_scale_limit

section
-- module Solutions.OAIQ2_Uni.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Cross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma avg_congr (μ : Law X) {f g : X → ℝ} (h : ∀ x, f x = g x) : avg μ f = avg μ g := by
  unfold avg
  exact sum_congr rfl (fun x _ => congrArg (μ.val x * ·) (h x))
lemma avg_ite (μ : Law X) (P : X → Prop) [DecidablePred P] :
    avg μ (fun x => if P x then 1 else 0) = event μ P := by
  unfold event
  apply avg_congr
  intro x
  split_ifs <;> rfl

lemma avg_const (μ : Law X) (c : ℝ) : avg μ (fun _ => c) = c := by
  simp [avg,← sum_mul,μ.total]
lemma avg_add (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x+g x)=avg μ f+avg μ g := by simp [avg,mul_add,sum_add_distrib]
lemma avg_sub (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x-g x)=avg μ f-avg μ g := by simp [avg,mul_sub,sum_sub_distrib]
lemma avg_smul (μ : Law X) (c : ℝ) (f : X  →  ℝ) :
    avg μ (fun x => c*f x)=c*avg μ f := by simp [avg,mul_left_comm, mul_sum]
lemma avg_mono (μ : Law X) {f g : X  →  ℝ} (h : ∀ x,f x ≤ g x) : avg μ f ≤ avg μ g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x)
lemma avg_le_const (μ : Law X) {f : X  →  ℝ} {c : ℝ} (h : ∀ x,f x ≤ c) : avg μ f ≤ c :=
  (avg_mono μ h).trans_eq (avg_const μ c)
lemma event_le_one (μ : Law X) (P : X  →  Prop) : event μ P ≤ 1 := by
  classical
  apply avg_le_const; intro x; split <;> norm_num
lemma event_compl (μ : Law X) (P : X  →  Prop) : event μ (fun x => ¬P x)=1-event μ P := by
  classical
  calc
    event μ (fun x => ¬P x) = avg μ (fun x => 1 - if P x then 1 else 0) := by
      apply avg_congr
      intro x
      split_ifs <;> simp_all
    _ = 1 - event μ P := by rw [avg_sub,avg_const,avg_ite]
lemma event_mono (μ : Law X) {P Q : X  →  Prop} (h : ∀ x,P x → Q x) : event μ P ≤ event μ Q := by
  classical
  apply avg_mono; intro x; split_ifs <;> simp_all
lemma event_union_le (μ : Law X) (P Q : X  →  Prop) :
    event μ (fun x => P x ∨ Q x) ≤ event μ P+event μ Q := by
  classical
  unfold event
  rw [← avg_add]
  apply avg_mono; intro x; split_ifs <;> simp_all

lemma pair_avg (μ : Law X) (ν : Law Y) (f : X×Y → ℝ) :
    avg (pair μ ν) f=avg μ (fun x => avg ν (fun y => f (x,y))) := by
  simp [avg,pair,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma pair_fst (μ : Law X) (ν : Law Y) (f : X → ℝ) :
    avg (pair μ ν) (fun x => f x.1)=avg μ f := by
  rw [pair_avg]; simp_rw [avg_const]
lemma pair_snd (μ : Law X) (ν : Law Y) (f : Y → ℝ) :
    avg (pair μ ν) (fun x => f x.2)=avg ν f := by
  rw [pair_avg]; dsimp only; rw [avg_const]
lemma pair_prod (μ : Law X) (ν : Law Y) (f : X → ℝ) (g : Y → ℝ) :
    avg (pair μ ν) (fun x => f x.1*g x.2)=avg μ f*avg ν g := by
  rw [pair_avg]; dsimp only; simp_rw [avg_smul];
  simp only [avg, ← mul_assoc, sum_mul]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.StarScore
open FiniteLaw StrictCross
noncomputable section
variable {X A B : Type*} [Fintype X]

lemma frequency_nonneg (μ : Law X) (bit : X  →  Bool) : 0 ≤ frequency μ bit := event_nonneg _ _
lemma frequency_le_one (μ : Law X) (bit : X  →  Bool) : frequency μ bit ≤ 1 := event_le_one _ _
lemma variation_nonneg (μ : Law X) (bit : X  →  Bool) : 0 ≤ variation μ bit := by
  unfold variation
  exact mul_nonneg (mul_nonneg (by norm_num) (frequency_nonneg _ _))
    (sub_nonneg.mpr (frequency_le_one _ _))
end
end PlanarUnitDistances.StarScore

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
open scoped Classical
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma atom_le_fiber (μ : Law X) (φ : X → Y) (x : X) : μ.val x ≤ fiberMass μ φ (φ x) := by
  classical
  rw [fiberMass_eq]
  have h := single_le_sum (s := univ) (f := fun y => if φ y=φ x then μ.val y else 0)
    (fun y _ => by split_ifs <;> simp [μ.nonneg]) (mem_univ x)
  simpa using h

lemma push_avg (μ : Law X) (φ : X → Y) (g : Y → ℝ) :
    avg (push μ φ) g = avg μ (fun x => g (φ x)) := by
  classical
  unfold avg push
  simp only [fiberMass_eq,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp

omit [Fintype Y] in
lemma cond_weight (μ : Law X) (φ : X → Y) (y : Y) (x : X) :
    fiberMass μ φ y * (cond μ φ y).val x = if φ x=y then μ.val x else 0 := by
  classical
  by_cases hy : 0 < fiberMass μ φ y
  · simp only [cond,hy,↓reduceDIte]
    split_ifs
    · field_simp
    · ring
  · have hz := le_antisymm (le_of_not_gt hy) (fiberMass_nonneg μ φ y)
    simp only [hz,zero_mul]
    split_ifs with hxy
    · have h := atom_le_fiber μ φ x
      rw [hxy,hz] at h
      exact (le_antisymm h (μ.nonneg x)).symm
    · rfl

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma cond_tower_dep (μ : Law X) (φ : X → Y) (f : Y → X → ℝ) :
    avg (push μ φ) (fun y => avg (cond μ φ y) (f y)) = avg μ (fun x => f (φ x) x) := by
  classical
  unfold avg
  simp only [push,mul_sum,← mul_assoc,cond_weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw StarScore CrossStructure
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

lemma row_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (left π) (fun p => avg (row π p) (f p)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [row,push_avg]
  change avg (push π Prod.fst) _ = _
  exact cond_tower_dep π Prod.fst (fun p pq => f p pq.2)
lemma col_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (right π) (fun q => avg (col π q) (fun p => f p q)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [col,push_avg]
  change avg (push π Prod.snd) _ = _
  exact cond_tower_dep π Prod.snd (fun q pq => f pq.1 q)
lemma row_event (π : Law (P×Q)) (g : P → Q → Prop) :
    avg (left π) (fun p => event (row π p) (g p)) = event π (fun pq => g pq.1 pq.2) := by
  unfold event
  exact row_avg π _
lemma col_event (π : Law (P×Q)) (g : P → Q → Prop) :
    avg (right π) (fun q => event (col π q) (fun p => g p q)) = event π (fun pq => g pq.1 pq.2) := by
  unfold event
  exact col_avg π _

end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.RareScore
open FiniteLaw CrossStructure
open scoped Classical
noncomputable section
variable {A B X : Type*}

lemma minority_exception {r b : Bool} {l x y : A×B}
    (hb : Consistent b x y) (hr : b=r) : exceptional r l x ∨ exceptional r l y := by
  subst b
  cases r <;> simp only [exceptional,Consistent,Bool.false_eq_true, ↓reduceIte] at *
  · by_contra! h; exact hb.1 (h.1.trans h.2.symm)
  · by_contra! h; exact hb.2 (h.1.trans h.2.symm)

end
end PlanarUnitDistances.RareScore

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Wedges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma law_ext {μ ν : Law X} (h : ∀x,μ.val x=ν.val x) : μ=ν := by
  cases μ with | mk a ha sa =>
    cases ν with | mk b hb sb =>
      have : a=b := funext h
      subst b
      rfl

end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]
lemma left_val (π : Law (P×Q)) (p : P) : (left π).val p = ∑q,π.val (p,q) := by
  simp only [left,push,fiberMass_eq,Fintype.sum_prod_type]
  rw [sum_comm]
  simp
lemma right_val (π : Law (P×Q)) (q : Q) : (right π).val q = ∑p,π.val (p,q) := by
  simp [right,push,fiberMass_eq,Fintype.sum_prod_type]
lemma col_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (right π).val q*(col π q).val p=π.val (p,q) := by
  simp only [col,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.1=p then fiberMass π Prod.snd q*(cond π Prod.snd q).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma col_val (π : Law (P×Q)) {q : Q} (hq : 0<(right π).val q) (p : P) :
    (col π q).val p=π.val (p,q)/(right π).val q := by
  apply (eq_div_iff hq.ne').mpr
  simpa only [mul_comm] using col_weight π p q
end
end PlanarUnitDistances.FiniteStarCoupling

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteInformation
open scoped InnerProductSpace
open Finset Real

lemma hellinger_pointwise {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : p ≠ 0 → q ≠ 0) :
    (sqrt p - sqrt q)^2 ≤ p * log (p/q) - p + q := by
  by_cases hpz : p = 0
  · simp [hpz, sq_sqrt hq]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm (hac hpz))
  have hspp := sqrt_pos.mpr hpp
  have hsqp := sqrt_pos.mpr hqp
  have hsp := sq_sqrt hp
  have hsq := sq_sqrt hq
  have hl := log_le_sub_one_of_pos (div_pos hsqp hspp)
  rw [log_div (ne_of_gt hsqp) (ne_of_gt hspp), log_sqrt hq, log_sqrt hp] at hl
  have hm : p * (sqrt q / sqrt p) = sqrt p * sqrt q := by
    rw [← mul_div_assoc]
    apply (div_eq_iff (ne_of_gt hspp)).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*p by positivity)
  rw [log_div hpz (hac hpz)]
  nlinarith

theorem hellinger_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) :
    (∑ a, (sqrt (p a) - sqrt (q a))^2) ≤ KL p q := by
  have hh := sum_le_sum (s := univ) (fun a _ => hellinger_pointwise (hp a) (hq a) (hac a))
  simpa only [sum_add_distrib, sum_sub_distrib, hpsum, hqsum, sub_add_cancel, KL] using hh

theorem TV_sq_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : (TV p q)^2 ≤ KL p q := by
  have hH := hellinger_le_KL p q hp hq hpsum hqsum hac
  have hs : (∑ a, (sqrt (p a) + sqrt (q a))^2) ≤ 4 := by
    calc
      _ ≤ ∑ a, (2*p a + 2*q a) := by
        apply sum_le_sum
        intro a _
        nlinarith [sq_nonneg (sqrt (p a) - sqrt (q a)), sq_sqrt (hp a), sq_sqrt (hq a)]
      _ = 4 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hpsum, hqsum]; norm_num
  have hid (a : α) : |p a-q a| =
      |sqrt (p a)-sqrt (q a)| * (sqrt (p a)+sqrt (q a)) := by
    rw [← abs_of_nonneg (show 0 ≤ sqrt (p a)+sqrt (q a) by positivity), ← abs_mul]
    congr 1
    nlinarith [sq_sqrt (hp a), sq_sqrt (hq a)]
  have hcs := sum_mul_sq_le_sq_mul_sq univ
    (fun a => |sqrt (p a)-sqrt (q a)|) (fun a => sqrt (p a)+sqrt (q a))
  simp only [← hid, sq_abs] at hcs
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ∑ a, (sqrt (p a)-sqrt (q a))^2 by positivity)
  unfold TV
  nlinarith

theorem KL_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : 0 ≤ KL p q :=
  (sq_nonneg _).trans (TV_sq_le_KL p q hp hq hpsum hqsum hac)

lemma KL_term_chain {p q P Q : ℝ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hac : p ≠ 0 → q ≠ 0) :
    p * log (p/q) = p * log (P/Q) +
      P * ((p/P) * log ((p/P)/(q/Q))) := by
  by_cases hp : p = 0
  · simp [hp]
  have hq := hac hp
  rw [log_div (div_ne_zero hp hP) (div_ne_zero hq hQ),
    log_div hp hP, log_div hq hQ, log_div hp hq, log_div hP hQ]
  field_simp
  ring

lemma sum_ac {α : Type*} [Fintype α] {p q : α → ℝ}
    (hq : ∀ a, 0 ≤ q a) (hac : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hp : ∑ a, p a ≠ 0) : ∑ a, q a ≠ 0 := by
  intro hqz
  have hz := (sum_eq_zero_iff_of_nonneg (fun a _ => hq a)).mp hqz
  apply hp
  apply sum_eq_zero
  intro a ha
  by_contra hh
  exact hac a hh (hz a ha)

theorem KL_chain {α β : Type*} [Fintype α] [Fintype β]
    (p q : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0) :
    KL p q = KL (fun a => ∑ b, p (a,b)) (fun a => ∑ b, q (a,b)) +
      ∑ a, (∑ b, p (a,b)) *
        KL (fun b => p (a,b) / (∑ c, p (a,c)))
          (fun b => q (a,b) / (∑ c, q (a,c))) := by
  unfold KL
  rw [Fintype.sum_prod_type, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  by_cases hz : ∑ b, p (a,b) = 0
  · have hpz := (sum_eq_zero_iff_of_nonneg (fun b _ => hp (a,b))).mp hz
    simp [fun b => hpz b (mem_univ b)]
  have hqz := sum_ac (fun b => hq (a,b)) (fun b => hac (a,b)) hz
  calc
    _ = ∑ b, (p (a,b) * log ((∑ c, p (a,c)) / (∑ c, q (a,c))) +
          (∑ c, p (a,c)) * ((p (a,b) / (∑ c, p (a,c))) *
            log ((p (a,b) / (∑ c, p (a,c))) / (q (a,b) / (∑ c, q (a,c)))))) := by
      apply sum_congr rfl
      intro b _
      exact KL_term_chain hz hqz (hac (a,b))
    _ = _ := by rw [sum_add_distrib, sum_mul, mul_sum]

theorem KL_fst_le {α β : Type*} [Fintype α] [Fintype β]
    (p q : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0) :
    KL (fun a => ∑ b, p (a,b)) (fun a => ∑ b, q (a,b)) ≤ KL p q := by
  rw [KL_chain p q hp hq hac]
  apply le_add_of_nonneg_right
  apply sum_nonneg
  intro a _
  by_cases hz : ∑ b, p (a,b) = 0
  · simp [hz]
  have hP : 0 ≤ ∑ b, p (a,b) := sum_nonneg fun b _ => hp (a,b)
  have hQ : 0 ≤ ∑ b, q (a,b) := sum_nonneg fun b _ => hq (a,b)
  have hqz := sum_ac (fun b => hq (a,b)) (fun b => hac (a,b)) hz
  apply mul_nonneg hP
  apply KL_nonneg
  · intro b; exact div_nonneg (hp (a,b)) hP
  · intro b; exact div_nonneg (hq (a,b)) hQ
  · rw [← sum_div, div_self hz]
  · rw [← sum_div, div_self hqz]
  · intro b hb
    apply div_ne_zero
    · apply hac (a,b)
      intro hh
      exact hb (by simp [hh])
    · exact hqz

lemma push_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (f : α → β) (b : β) :
    0 ≤ push p f b := by
  apply sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · exact le_rfl

lemma push_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (f : α → β) : ∑ b, push p f b = ∑ a, p a := by
  unfold push
  rw [sum_comm]
  simp

lemma push_ac {α β : Type*} [Fintype α] [DecidableEq β]
    {p q : α → ℝ} (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (f : α → β) (b : β) :
    push p f b ≠ 0 → push q f b ≠ 0 := by
  apply sum_ac
  · intro a; split_ifs; exact hq a; exact le_rfl
  · intro a ha; split_ifs at * <;> simp_all

lemma KL_graph {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p q : α → ℝ) (f : α → β) :
    KL (fun ba : β × α => if f ba.2 = ba.1 then p ba.2 else 0)
      (fun ba : β × α => if f ba.2 = ba.1 then q ba.2 else 0) = KL p q := by
  unfold KL
  rw [Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro a _
  simp only
  conv_lhs => arg 2; ext b; rw [apply_ite₂ (fun x y : ℝ => x * log (x/y))]
  simp

theorem KL_push_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (f : α → β) :
    KL (push p f) (push q f) ≤ KL p q := by
  rw [← KL_graph p q f]
  apply KL_fst_le (fun ba : β × α => if f ba.2 = ba.1 then p ba.2 else 0)
    (fun ba : β × α => if f ba.2 = ba.1 then q ba.2 else 0)
  · intro ba; split_ifs; exact hp ba.2; exact le_rfl
  · intro ba; split_ifs; exact hq ba.2; exact le_rfl
  · intro ba ha; split_ifs at * <;> simp_all

theorem expectation_TV {α : Type*} [Fintype α] (p q F : α → ℝ)
    {B : ℝ} (hF : ∀ a, |F a| ≤ B) :
    |(∑ a, p a * F a) - ∑ a, q a * F a| ≤ 2 * B * TV p q := by
  unfold TV
  calc
    _ = |∑ a, (p a-q a)*F a| := by rw [← sum_sub_distrib]; congr 1; apply sum_congr rfl; intros; ring
    _ ≤ ∑ a, |(p a-q a)*F a| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |p a-q a| * B := by
      apply sum_le_sum; intro a _; rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hF a) (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

lemma row_nonneg {α β : Type*} [Fintype β] {p : α × β → ℝ}
    (hp : ∀ ab, 0 ≤ p ab) (a : α) : 0 ≤ row p a := sum_nonneg fun b _ => hp (a,b)

lemma row_ac {α β : Type*} [Fintype β] {p q : α × β → ℝ}
    (hq : ∀ ab, 0 ≤ q ab) (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0)
    (a : α) : row p a ≠ 0 → row q a ≠ 0 :=
  sum_ac (fun b => hq (a,b)) (fun b => hac (a,b))

lemma cond_nonneg {α β : Type*} [Fintype β] {p : α × β → ℝ}
    (hp : ∀ ab, 0 ≤ p ab) (a : α) (b : β) : 0 ≤ cond p a b :=
  div_nonneg (hp (a,b)) (row_nonneg hp a)

lemma cond_sum {α β : Type*} [Fintype β] (p : α × β → ℝ) (a : α)
    (ha : row p a ≠ 0) : ∑ b, cond p a b = 1 := by
  simp only [cond, ← sum_div]
  exact div_self ha

lemma cond_ac {α β : Type*} [Fintype β] {p q : α × β → ℝ}
    (hq : ∀ ab, 0 ≤ q ab) (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0)
    (a : α) (ha : row p a ≠ 0) (b : β) :
    cond p a b ≠ 0 → cond q a b ≠ 0 := by
  intro hb
  apply div_ne_zero
  · apply hac (a,b)
    intro hz
    exact hb (by simp [cond, hz])
  · exact row_ac hq hac a ha

lemma cond_KL_nonneg {α β : Type*} [Fintype β] {p q : α × β → ℝ}
    (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0) (a : α) (ha : row p a ≠ 0) :
    0 ≤ KL (cond p a) (cond q a) :=
  KL_nonneg _ _ (cond_nonneg hp a) (cond_nonneg hq a)
    (cond_sum p a ha) (cond_sum q a (row_ac hq hac a ha)) (cond_ac hq hac a ha)

theorem conditional_TV_sq {α β : Type*} [Fintype α] [Fintype β]
    (p q : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hpsum : ∑ ab, p ab = 1) (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0) :
    (∑ a, row p a * TV (cond p a) (cond q a))^2 ≤ KL p q - KL (row p) (row q) := by
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) univ
    (r := fun a => row p a * TV (cond p a) (cond q a))
    (f := row p) (g := fun a => row p a * KL (cond p a) (cond q a))
    (fun a _ => row_nonneg hp a)
    (fun a _ => by
      by_cases ha : row p a = 0
      · simp [ha]
      · exact mul_nonneg (row_nonneg hp a) (cond_KL_nonneg hp hq hac a ha))
    (fun a _ => by
      by_cases ha : row p a = 0
      · simp [ha]
      have hh := TV_sq_le_KL (cond p a) (cond q a)
        (cond_nonneg hp a) (cond_nonneg hq a)
        (cond_sum p a ha) (cond_sum q a (row_ac hq hac a ha)) (cond_ac hq hac a ha)
      nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (row p a))])
  have hs : ∑ a, row p a = 1 := by
    simpa only [row, ← Fintype.sum_prod_type] using hpsum
  rw [hs, one_mul] at hcs
  have hc := KL_chain p q hp hq hac
  change KL p q = KL (row p) (row q) + ∑ a, row p a * KL (cond p a) (cond q a) at hc
  linarith

lemma row_expectation {α β : Type*} [Fintype β] (p : α × β → ℝ)
    (hp : ∀ ab, 0 ≤ p ab) (F : α × β → ℝ) (a : α) :
    (∑ b, p (a,b) * F (a,b)) = row p a * ∑ b, cond p a b * F (a,b) := by
  by_cases ha : row p a = 0
  · have hz := (sum_eq_zero_iff_of_nonneg (fun b _ => hp (a,b))).mp ha
    simp [ha, fun b => hz b (mem_univ b)]
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  dsimp [cond]
  field_simp

theorem conditional_centered_bound {α β : Type*} [Fintype α] [Fintype β]
    (p q : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hpsum : ∑ ab, p ab = 1) (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0)
    (F : α × β → ℝ) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ ab, |F ab| ≤ B)
    (hc : ∀ a, row p a ≠ 0 → ∑ b, cond q a b * F (a,b) = 0) :
    |∑ ab, p ab * F ab| ≤ 2*B*sqrt (KL p q - KL (row p) (row q)) := by
  have hv := conditional_TV_sq p q hp hq hpsum hac
  have hvs : (∑ a, row p a * TV (cond p a) (cond q a)) ≤
      sqrt (KL p q-KL (row p) (row q)) := le_sqrt_of_sq_le hv
  calc
    _ = |∑ a, ∑ b, p (a,b)*F (a,b)| := by rw [Fintype.sum_prod_type]
    _ ≤ ∑ a, |∑ b, p (a,b)*F (a,b)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, 2*B*(row p a*TV (cond p a) (cond q a)) := by
      apply sum_le_sum
      intro a _
      rw [row_expectation p hp F a, abs_mul, abs_of_nonneg (row_nonneg hp a)]
      by_cases ha : row p a = 0
      · simp [ha]
      have hh := expectation_TV (cond p a) (cond q a) (fun b => F (a,b)) (fun b => hF (a,b))
      rw [hc a ha, sub_zero] at hh
      have hm := mul_le_mul_of_nonneg_left hh (row_nonneg hp a)
      nlinarith
    _ = 2*B*(∑ a, row p a*TV (cond p a) (cond q a)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hvs (by positivity)

lemma push_expectation {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [AddCommMonoid V] [Module ℝ V] (p : α → ℝ) (f : α → β) (v : β → V) :
    ∑ b, push p f b • v b = ∑ a, p a • v (f a) := by
  unfold push
  simp only [sum_smul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [ite_smul, zero_smul]
  simp

lemma push_comp {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] (p : α → ℝ) (f : α → β) (g : β → γ) :
    push (push p f) g = push p (g ∘ f) := by
  classical
  funext c
  unfold push
  simp_rw [show ∀ b, (if g b = c then ∑ a, if f a = b then p a else 0 else 0) =
      ∑ a, if g b = c then (if f a = b then p a else 0) else 0 from
    fun b => by split_ifs <;> simp]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  have hi : ∀ b, (if g b = c then if f a = b then p a else 0 else 0) =
      if f a = b then (if g b = c then p a else 0) else 0 := by
    intro b
    split_ifs <;> rfl
  simp_rw [hi]
  simp

lemma push_equiv {α β : Type*} [Fintype α] [DecidableEq β]
    (p : α → ℝ) (e : α ≃ β) (b : β) : push p e b = p (e.symm b) := by
  classical
  unfold push
  simp_rw [← e.eq_symm_apply]
  simp

lemma KL_push_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p q : α → ℝ) (e : α ≃ β) : KL (push p e) (push q e) = KL p q := by
  simp only [KL, push_equiv]
  exact Equiv.sum_comp e.symm (fun a => p a * log (p a / q a))

lemma row_refinement {α β γ : Type*} [Fintype α] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (p : α → ℝ) (h : α → β) (c : α → γ) :
    row (push p (fun a => (h a,c a))) = push p h := by
  funext b
  unfold row push
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [Prod.mk.injEq]
  by_cases ha : h a = b <;> simp [ha]

lemma KL_refinement_nonneg {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (h : α → β) (c : α → γ) :
    0 ≤ KL (push p (fun a => (h a,c a))) (push q (fun a => (h a,c a))) -
      KL (push p h) (push q h) := by
  rw [← row_refinement p h c, ← row_refinement q h c]
  apply sub_nonneg.mpr
  exact KL_fst_le _ _ (push_nonneg hp _) (push_nonneg hq _) (push_ac hq hac _)

section Features
variable {H C V : Type*} [Fintype H] [Fintype C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [Fintype H] in
lemma norm_mean_le (x : H × C → ℝ) (hx : ∀ hc, 0 ≤ x hc)
    (v : C → V) {B : ℝ} (hB : 0 ≤ B) (hv : ∀ c, ‖v c‖ ≤ B) (h : H) :
    ‖mean x v h‖ ≤ B := by
  by_cases hr : row x h = 0
  · simp [mean, cond, hr, hB]
  calc
    _ ≤ ∑ c, ‖cond x h c • v c‖ := norm_sum_le _ _
    _ = ∑ c, cond x h c * ‖v c‖ := by
      apply sum_congr rfl
      intro c _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cond_nonneg hx h c)]
    _ ≤ ∑ c, cond x h c * B := by
      apply sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (hv c) (cond_nonneg hx h c)
    _ = B := by rw [← sum_mul, cond_sum x h hr, one_mul]

omit [Fintype H] in
lemma centered_mean (x : H × C → ℝ) (v : C → V) (h : H)
    (hr : row x h ≠ 0) :
    ∑ c, cond x h c • (v c - mean x v h) = 0 := by
  rw [show (fun c => cond x h c • (v c - mean x v h)) =
    (fun c => cond x h c • v c - cond x h c • mean x v h) by
      funext c; rw [smul_sub], sum_sub_distrib, ← sum_smul, cond_sum x h hr, one_smul]
  exact sub_self _

omit [Fintype H] in
lemma paired_row (x : H × C → ℝ) (h : H × H) :
    row (paired x) h = row x h.1 * row x h.2 := by
  simp only [row, paired, Fintype.sum_prod_type, sum_mul_sum]

omit [Fintype H] in
lemma paired_cond (x : H × C → ℝ) (h : H × H) (c : C × C) :
    cond (paired x) h c = cond x h.1 c.1 * cond x h.2 c.2 := by
  simp only [cond, paired_row, paired, mul_div_mul_comm]

omit [Fintype H] in
lemma paired_centered (x : H × C → ℝ) (v : C → V) (h : H × H)
    (hr : row (paired x) h ≠ 0) :
    ∑ c, cond (paired x) h c *
      ⟪v c.1 - mean x v h.1, v c.2 - mean x v h.2⟫_ℝ = 0 := by
  rw [paired_row] at hr
  have h1 := (mul_ne_zero_iff.mp hr).1
  have h2 := (mul_ne_zero_iff.mp hr).2
  simp only [paired_cond, Fintype.sum_prod_type]
  calc
    _ = ⟪∑ c, cond x h.1 c • (v c - mean x v h.1),
        ∑ c, cond x h.2 c • (v c - mean x v h.2)⟫_ℝ := by
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro c _
      apply sum_congr rfl
      intro d _
      ring
    _ = 0 := by rw [centered_mean x v h.1 h1, inner_zero_left]

theorem feature_increment (a : (H × H) × (C × C) → ℝ)
    (x : H × C → ℝ) (ha : ∀ v, 0 ≤ a v) (hx : ∀ v, 0 ≤ x v)
    (hs : ∑ v, a v = 1) (hac : ∀ v, a v ≠ 0 → paired x v ≠ 0)
    (v : C → V) {B : ℝ} (hB : 0 ≤ B) (hv : ∀ c, ‖v c‖ ≤ B) :
    |∑ hc, a hc * ⟪v hc.2.1 - mean x v hc.1.1,
      v hc.2.2 - mean x v hc.1.2⟫_ℝ| ≤
      8*B^2*sqrt (KL a (paired x) - KL (row a) (row (paired x))) := by
  have hn : ∀ h c, ‖v c - mean x v h‖ ≤ 2*B := by
    intro h c
    calc
      _ ≤ ‖v c‖ + ‖mean x v h‖ := norm_sub_le _ _
      _ ≤ B+B := add_le_add (hv c) (norm_mean_le x hx v hB hv h)
      _ = 2*B := by ring
  convert conditional_centered_bound a (paired x) ha
    (fun a => mul_nonneg (hx _) (hx _)) hs hac
    (fun hc => ⟪v hc.2.1 - mean x v hc.1.1, v hc.2.2 - mean x v hc.1.2⟫_ℝ)
    (B := 4*B^2) (by positivity) (fun hc => ?_) (fun h hh => ?_) using 1 <;> try ring_nf
  · calc
      _ ≤ ‖v hc.2.1-mean x v hc.1.1‖*‖v hc.2.2-mean x v hc.1.2‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (2*B)*(2*B) := mul_le_mul (hn _ _) (hn _ _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · exact paired_centered x v h (row_ac (fun a => mul_nonneg (hx _) (hx _)) hac h hh)
end Features

section Observation
variable {P H C : Type*} [Fintype P] [Fintype H] [Fintype C]
  [DecidableEq H] [DecidableEq C]

omit [Fintype H] [Fintype C] in
lemma product_observation (μ : P → ℝ) (h : P → H) (c : P → C) :
    push (fun pr : P × P => μ pr.1 * μ pr.2) (observation h c) =
      paired (push μ (fun p => (h p,c p))) := by
  funext a
  rcases a with ⟨⟨h1,h2⟩,⟨c1,c2⟩⟩
  dsimp [push, observation, paired]
  rw [Fintype.sum_prod_type, sum_mul_sum]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype H] in
lemma observation_row (pLaw : P × P → ℝ) (h : P → H) (c : P → C) :
    row (push pLaw (observation h c)) = push pLaw (fun pr => (h pr.1,h pr.2)) :=
  row_refinement pLaw (fun pr => (h pr.1,h pr.2)) (fun pr => (c pr.1,c pr.2))

lemma observation_entropy (pLaw ρ : P × P → ℝ) (h : P → H) (c : P → C) :
    KL (push pLaw (observation h c)) (push ρ (observation h c)) =
      KL (push pLaw (fun pr => ((h pr.1,c pr.1),(h pr.2,c pr.2))))
        (push ρ (fun pr => ((h pr.1,c pr.1),(h pr.2,c pr.2)))) := by
  let e := Equiv.prodProdProdComm H H C C
  rw [← KL_push_equiv (push pLaw (observation h c)) (push ρ (observation h c)) e,
    push_comp, push_comp]
  rfl

theorem observation_covariance {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (pLaw : P × P → ℝ) (μ : P → ℝ) (hpLaw : ∀ pr, 0 ≤ pLaw pr) (hμ : ∀ p, 0 ≤ μ p)
    (hs : ∑ pr, pLaw pr = 1) (hac : ∀ pr, pLaw pr ≠ 0 → μ pr.1 * μ pr.2 ≠ 0)
    (h : P → H) (c : P → C) (v : C → V) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ c, ‖v c‖ ≤ B) :
    |∑ pr, pLaw pr *
      ⟪v (c pr.1) - mean (push μ (fun p => (h p,c p))) v (h pr.1),
       v (c pr.2) - mean (push μ (fun p => (h p,c p))) v (h pr.2)⟫_ℝ| ≤
    8*B^2*sqrt (
      KL (push pLaw (fun pr => ((h pr.1,c pr.1),(h pr.2,c pr.2))))
        (push (fun pr : P × P => μ pr.1*μ pr.2)
          (fun pr => ((h pr.1,c pr.1),(h pr.2,c pr.2)))) -
      KL (push pLaw (fun pr => (h pr.1,h pr.2)))
        (push (fun pr : P × P => μ pr.1*μ pr.2) (fun pr => (h pr.1,h pr.2)))) := by
  let ρ : P × P → ℝ := fun pr => μ pr.1*μ pr.2
  have hr : ∀ pr, 0 ≤ ρ pr := fun pr => mul_nonneg (hμ _) (hμ _)
  have he := feature_increment (push pLaw (observation h c))
    (push μ (fun p => (h p,c p))) (push_nonneg hpLaw _) (push_nonneg hμ _)
    (by rw [push_sum]; exact hs)
    (by rw [← product_observation]; exact push_ac hr hac _) v hB hv
  rw [← product_observation μ h c, observation_entropy, observation_row,
    observation_row] at he
  have hf := push_expectation pLaw (observation h c)
    (fun hc : (H × H) × (C × C) =>
      ⟪v hc.2.1 - mean (push μ (fun p => (h p,c p))) v hc.1.1,
        v hc.2.2 - mean (push μ (fun p => (h p,c p))) v hc.1.2⟫_ℝ)
  simp only [smul_eq_mul, observation] at hf
  rwa [hf] at he
end Observation

section Wedges
variable {P Q V : Type*} [Fintype P] [Fintype Q]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem wedge_square (κ : Q → ℝ) (w : Q → P → ℝ) (U : P → V) :
    (∑ pr, wedge κ w pr * ⟪U pr.1,U pr.2⟫_ℝ) =
      ∑ q, κ q * ‖∑ p, w q p • U p‖^2 := by
  unfold wedge
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Fintype.sum_prod_type, mul_sum]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  ring

omit [Fintype P] in
lemma wedge_nonneg (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p) (pr : P × P) :
    0 ≤ wedge κ w pr := sum_nonneg fun q _ => mul_nonneg (mul_nonneg (hκ q) (hw q _)) (hw q _)

lemma wedge_sum (κ : Q → ℝ) (w : Q → P → ℝ)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1) :
    ∑ pr, wedge κ w pr = 1 := by
  unfold wedge
  rw [sum_comm]
  simp only [Fintype.sum_prod_type, ← mul_sum, hsw, mul_one]
  exact hsκ

theorem weighted_inner_bound (κ : Q → ℝ) (hκ : ∀ q, 0 ≤ κ q)
    (hsκ : ∑ q, κ q = 1) (a g : Q → V) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ q, ‖g q‖ ≤ B) :
    |∑ q, κ q * ⟪a q,g q⟫_ℝ| ≤ B * sqrt (∑ q, κ q * ‖a q‖^2) := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) univ
    (r := fun q => κ q * ‖a q‖) (f := κ) (g := fun q => κ q * ‖a q‖^2)
    (fun q _ => hκ q) (fun q _ => mul_nonneg (hκ q) (sq_nonneg _))
    (fun q _ => by ring_nf; exact le_rfl)
  rw [hsκ, one_mul] at hc
  have hsr := le_sqrt_of_sq_le hc
  calc
    _ ≤ ∑ q, |κ q * ⟪a q,g q⟫_ℝ| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, κ q * (‖a q‖ * B) := by
      apply sum_le_sum
      intro q _
      rw [abs_mul, abs_of_nonneg (hκ q)]
      apply mul_le_mul_of_nonneg_left _ (hκ q)
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hg q) (norm_nonneg _))
    _ = B * ∑ q, κ q * ‖a q‖ := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsr hB
end Wedges

universe u

lemma history_card (C : Type*) [Fintype C] (n : ℕ) :
    Fintype.card (History C n) = (Fintype.card C)^n := by
  induction n with
  | zero =>
      calc
        _ = Fintype.card PUnit := Fintype.card_congr (Equiv.refl _)
        _ = _ := by rw [Fintype.card_punit, pow_zero]
  | succ n ih =>
      calc
        _ = Fintype.card (History C n × C) := Fintype.card_congr (Equiv.refl _)
        _ = _ := by rw [Fintype.card_prod, ih, pow_succ]

lemma transcriptKL_zero {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]
    (p q : P × P → ℝ) (hp : ∑ pr, p pr = 1) (hq : ∑ pr, q pr = 1)
    (c : ℕ → P → C) : transcriptKL p q c 0 = 0 := by
  simp [transcriptKL, transcript, push, KL, hp, hq, History]

lemma transcriptKL_mono {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]
    (p q : P × P → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (c : ℕ → P → C) (n : ℕ) :
    transcriptKL p q c n ≤ transcriptKL p q c (n+1) := by
  have hh := KL_refinement_nonneg p q hp hq hac
    (fun pr => (transcript c n pr.1,transcript c n pr.2))
    (fun pr => (c n pr.1,c n pr.2))
  change 0 ≤ KL (push p (observation (transcript c n) (c n)))
    (push q (observation (transcript c n) (c n))) - transcriptKL p q c n at hh
  rw [observation_entropy] at hh
  exact sub_nonneg.mp hh

theorem transcript_budget {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]
    (p q : P × P → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hps : ∑ a, p a = 1) (hqs : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (c : ℕ → P → C) (K : ℕ) :
    (∑ n ∈ range K, (transcriptKL p q c (n+1)-transcriptKL p q c n)) ≤ KL p q := by
  have ht : (∑ n ∈ range K, (transcriptKL p q c (n+1)-transcriptKL p q c n)) =
      transcriptKL p q c K - transcriptKL p q c 0 := by
    induction K with
    | zero => simp
    | succ K ih => rw [sum_range_succ, ih]; ring
  rw [ht, transcriptKL_zero p q hps hqs c, sub_zero]
  exact KL_push_le p q hp hq hac _

section Marginal
variable {P Q : Type*} [Fintype P] [Fintype Q]

omit [Fintype P] in
lemma marginal_nonneg (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p) (p : P) :
    0 ≤ marginal κ w p := sum_nonneg fun q _ => mul_nonneg (hκ q) (hw q p)

lemma marginal_sum (κ : Q → ℝ) (w : Q → P → ℝ)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1) :
    ∑ p, marginal κ w p = 1 := by
  unfold marginal
  rw [sum_comm]
  simp_rw [← mul_sum, hsw, mul_one]
  exact hsκ

omit [Fintype P] in
lemma wedge_ac (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p) (pr : P × P) :
    wedge κ w pr ≠ 0 → marginal κ w pr.1 * marginal κ w pr.2 ≠ 0 := by
  intro hh
  apply mul_ne_zero
  · intro hz
    have ht := (sum_eq_zero_iff_of_nonneg (fun q _ => mul_nonneg (hκ q) (hw q pr.1))).mp hz
    apply hh
    apply sum_eq_zero
    intro q hq
    rw [ht q hq, zero_mul]
  · intro hz
    have ht := (sum_eq_zero_iff_of_nonneg (fun q _ => mul_nonneg (hκ q) (hw q pr.2))).mp hz
    apply hh
    apply sum_eq_zero
    intro q hq
    calc
      _ = (κ q * w q pr.2) * w q pr.1 := by ring
      _ = 0 := by rw [ht q hq, zero_mul]
end Marginal

lemma average_sq_le (K : ℕ) (hK : 0 < K) (f : ℕ → ℝ) :
    ((∑ n ∈ range K, f n)/(K:ℝ))^2 ≤ (∑ n ∈ range K, (f n)^2)/(K:ℝ) := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) (range K)
    (r := f) (f := fun _ => (1:ℝ)) (g := fun n => (f n)^2)
    (fun _ _ => by norm_num) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at hc
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hk)).mpr
  calc
    _ ≤ (K:ℝ) * ∑ n ∈ range K, f n^2 := hc
    _ = _ := by field_simp

lemma average_sqrt_le (K : ℕ) (hK : 0 < K) (f : ℕ → ℝ)
    (hf : ∀ n ∈ range K, 0 ≤ f n) :
    (∑ n ∈ range K, sqrt (f n))/(K:ℝ) ≤ sqrt ((∑ n ∈ range K, f n)/(K:ℝ)) := by
  apply le_sqrt_of_sq_le
  convert average_sq_le K hK (fun n => sqrt (f n)) using 1
  congr 1
  apply sum_congr rfl
  intro n hn
  exact (sq_sqrt (hf n hn)).symm

section FrozenPrediction
variable {P Q C V : Type*} [Fintype P] [Fintype Q] [Fintype C] [DecidableEq C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem frozen_prediction (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (c : ℕ → P → C) (v : ℕ → C → V) (g : ℕ → Q → V)
    {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hv : ∀ n c, ‖v n c‖ ≤ B) (hg : ∀ n q, ‖g n q‖ ≤ B')
    (K : ℕ) (hK : 0 < K) :
    (∑ n ∈ range K, discrepancy κ w c v g n)/(K:ℝ) ≤
      4*B*B'*sqrt (sqrt (KL (wedge κ w)
        (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))) := by
  let pLaw := wedge κ w
  let μ := marginal κ w
  let qLaw : P × P → ℝ := fun pr => μ pr.1 * μ pr.2
  have hp := wedge_nonneg κ w hκ hw
  have hm := marginal_nonneg κ w hκ hw
  have hq : ∀ pr, 0 ≤ qLaw pr := fun pr => mul_nonneg (hm _) (hm _)
  have hps := wedge_sum κ w hsκ hsw
  have hms := marginal_sum κ w hsκ hsw
  have hqs : ∑ pr, qLaw pr = 1 := by
    dsimp [qLaw, μ]
    rw [Fintype.sum_prod_type, ← sum_mul_sum, hms, one_mul]
  have hac := wedge_ac κ w hκ hw
  let D := KL pLaw qLaw
  have hD : 0 ≤ D := KL_nonneg _ _ hp hq hps hqs hac
  let delta := fun n => transcriptKL pLaw qLaw c (n+1) - transcriptKL pLaw qLaw c n
  have hd : ∀ n, 0 ≤ delta n := fun n => sub_nonneg.mpr (transcriptKL_mono _ _ hp hq hac c n)
  have hbudget : (∑ n ∈ range K, delta n) ≤ D :=
    transcript_budget _ _ hp hq hps hqs hac c K
  let variance := fun n => ∑ q, κ q * ‖∑ p, w q p • residual μ c v n p‖^2
  have hvar : ∀ n, 0 ≤ variance n := fun n => sum_nonneg fun q _ => mul_nonneg (hκ q) (sq_nonneg _)
  have hcov : ∀ n, variance n ≤ 8*B^2*sqrt (delta n) := by
    intro n
    have hh := observation_covariance pLaw μ hp hm hps hac (transcript c n) (c n) (v n) hB (hv n)
    change |∑ pr, wedge κ w pr * ⟪residual μ c v n pr.1,residual μ c v n pr.2⟫_ℝ| ≤
      8*B^2*sqrt (delta n) at hh
    rw [wedge_square, abs_of_nonneg (hvar n)] at hh
    exact hh
  have hdisc : ∀ n, discrepancy κ w c v g n ≤ B' * sqrt (variance n) := by
    intro n
    exact weighted_inner_bound κ hκ hsκ _ (g n) hB' (hg n)
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have havar : (∑ n ∈ range K, variance n)/(K:ℝ) ≤ 8*B^2*sqrt (D/(K:ℝ)) := by
    calc
      _ ≤ (∑ n ∈ range K, 8*B^2*sqrt (delta n))/(K:ℝ) :=
        div_le_div_of_nonneg_right (sum_le_sum fun n _ => hcov n) hk.le
      _ = 8*B^2*((∑ n ∈ range K, sqrt (delta n))/(K:ℝ)) := by rw [← mul_sum]; ring
      _ ≤ 8*B^2*sqrt ((∑ n ∈ range K, delta n)/(K:ℝ)) :=
        mul_le_mul_of_nonneg_left (average_sqrt_le K hK delta (fun n _ => hd n)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sqrt_le_sqrt (div_le_div_of_nonneg_right hbudget hk.le)) (by positivity)
  calc
    _ ≤ (∑ n ∈ range K, B'*sqrt (variance n))/(K:ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum fun n _ => hdisc n) hk.le
    _ = B'*((∑ n ∈ range K, sqrt (variance n))/(K:ℝ)) := by rw [← mul_sum]; ring
    _ ≤ B'*sqrt ((∑ n ∈ range K, variance n)/(K:ℝ)) :=
      mul_le_mul_of_nonneg_left (average_sqrt_le K hK variance (fun n _ => hvar n)) hB'
    _ ≤ B'*sqrt (8*B^2*sqrt (D/(K:ℝ))) := mul_le_mul_of_nonneg_left (sqrt_le_sqrt havar) hB'
    _ ≤ _ := by
      have hroot : sqrt (8*B^2*sqrt (D/(K:ℝ))) ≤ 4*B*sqrt (sqrt (D/(K:ℝ))) := by
        apply (sqrt_le_iff).mpr
        constructor
        · positivity
        · rw [mul_pow, mul_pow, sq_sqrt (sqrt_nonneg _)]
          nlinarith [mul_nonneg (sq_nonneg B) (sqrt_nonneg (D/(K:ℝ)))]
      simpa [mul_assoc, mul_left_comm, mul_comm, D, pLaw, qLaw, μ] using mul_le_mul_of_nonneg_left hroot hB'
end FrozenPrediction

section Posterior
variable {P H C V : Type*} [Fintype P] [Fintype H] [Fintype C]
  [DecidableEq H] [DecidableEq C] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [Fintype H] in
lemma row_push_pair (μ : P → ℝ) (h : P → H) (c : P → C) :
    row (push μ (fun p => (h p,c p))) = push μ h := by
  exact row_refinement μ h c

omit [Fintype H] in

lemma mean_posterior (μ : P → ℝ) (h : P → H) (c : P → C) (v : C → V) (x : H) :
    mean (push μ (fun p => (h p,c p))) v x =
      ∑ p, posterior μ h x p • v (c p) := by
  unfold mean cond
  rw [row_push_pair]
  simp only [push, sum_div, sum_smul, Prod.mk.injEq]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  by_cases he : h p = x <;> simp [he, posterior, push, ite_div, ite_smul]
end Posterior

section RandomTests
open MeasureTheory ProbabilityTheory
variable {Ω T H : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace H]
  {ρ : Measure Ω} {ν : Measure T} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]

lemma fresh_integral (u : Ω → H) (v : Ω → T) (hu : Measurable u) (hv : Measurable v)
    (hind : IndepFun u v ρ) (hlaw : ρ.map v = ν) (F : H × T → ℝ)
    (hF : Measurable F) (A : ℝ) (hbound : ∀ z, ‖F z‖ ≤ A) :
    (∫ ω, F (u ω,v ω) ∂ρ) = ∫ ω, ∫ t, F (u ω,t) ∂ν ∂ρ := by
  have hmap := hind.map_prod_eq_prod_map_map hu.aemeasurable hv.aemeasurable
  rw [hlaw] at hmap
  have hleft : (∫ ω, F (u ω,v ω) ∂ρ) = ∫ z, F z ∂((ρ.map u).prod ν) := by
    rw [← hmap, integral_map (hu.prodMk hv).aemeasurable hF.aestronglyMeasurable]
  rw [hleft]
  have hright : ((ρ.prod ν).map (fun z : Ω × T => (u z.1,z.2))) = (ρ.map u).prod ν := by
    calc
      _ = (ρ.prod ν).map (Prod.map u (id : T → T)) := by
        congr 1
      _ = (ρ.map u).prod (ν.map id) := (Measure.map_prod_map ρ ν hu measurable_id).symm
      _ = _ := by rw [Measure.map_id]
  have hpair : Measurable (fun z : Ω × T => (u z.1,z.2)) :=
    (hu.comp measurable_fst).prodMk measurable_snd
  rw [← hright, integral_map hpair.aemeasurable hF.aestronglyMeasurable]
  apply integral_prod
  apply Integrable.of_bound (hF.comp (hu.comp measurable_fst |>.prodMk measurable_snd)).aestronglyMeasurable A
  exact Filter.Eventually.of_forall fun z => hbound (u z.1,z.2)

lemma average_integral_bound (K : ℕ) (_hK : 0 < K) (F : ℕ → Ω → ℝ)
    (hF : ∀ n ∈ range K, Integrable (F n) ρ) (A : ℝ)
    (hb : ∀ ω, (∑ n ∈ range K, F n ω)/(K:ℝ) ≤ A) :
    (∑ n ∈ range K, ∫ ω, F n ω ∂ρ)/(K:ℝ) ≤ A := by
  have hi : Integrable (fun ω => (∑ n ∈ range K, F n ω)/(K:ℝ)) ρ :=
    (integrable_finsetSum _ hF).div_const _
  calc
    _ = ∫ ω, (∑ n ∈ range K, F n ω)/(K:ℝ) ∂ρ := by
      rw [integral_div, integral_finsetSum _ hF]
    _ ≤ ∫ _, A ∂ρ := integral_mono hi (integrable_const A) hb
    _ = A := by simp
end RandomTests

section HistoriesMeasurable
open MeasureTheory ProbabilityTheory
universe uC
variable {C : Type uC} [MeasurableSpace C]

omit [MeasurableSpace C] in
lemma transcript_congr {P : Type*} (c d : ℕ → P → C) (n : ℕ)
    (hc : ∀ k < n, c k = d k) : transcript c n = transcript d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext p
    change (transcript c n p,c n p) = (transcript d n p,d n p)
    rw [ih (fun k hk => hc k (Nat.lt_succ_of_lt hk)), hc n (Nat.lt_succ_self n)]

lemma measurable_transcript {Ω P : Type*} [MeasurableSpace Ω]
    (c : ℕ → Ω → P → C) (hc : ∀ n p, Measurable (fun ω => c n ω p)) (n : ℕ) :
    Measurable (fun ω p => transcript (fun k => c k ω) n p) := by
  induction n with
  | zero =>
    change Measurable (fun _ : Ω => (fun _ : P => PUnit.unit))
    exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro p
    exact ((measurable_pi_apply p).comp ih).prodMk (hc n p)

lemma prefix_independent {Ω P T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    {ρ : Measure Ω} (tests : ℕ → Ω → T) (ht : ∀ n, Measurable (tests n))
    (hind : iIndepFun tests ρ) (t0 : T) (c : T → P → C)
    (hc : ∀ p, Measurable (fun t => c t p)) (n : ℕ) :
    IndepFun (fun ω p => transcript (fun k => c (tests k ω)) n p) (tests n) ρ := by
  classical
  let extend : ((range n) → T) → ℕ → T :=
    fun v k => if hk : k ∈ range n then v ⟨k,hk⟩ else t0
  have he : ∀ k, Measurable (fun v => extend v k) := by
    intro k
    by_cases hk : k ∈ range n
    · simpa only [extend, dite_eq_left hk] using
        (measurable_pi_apply (⟨k,hk⟩ : range n) : Measurable (fun v : range n → T => v ⟨k,hk⟩))
    · simpa only [extend, dite_eq_right hk] using (measurable_const : Measurable (fun _ : range n → T => t0))
  let F : ((range n) → T) → P → History C n :=
    fun v p => transcript (fun k => c (extend v k)) n p
  have hF : Measurable F := measurable_transcript _ (fun k p => (hc p).comp (he k)) n
  have hi := (hind.indepFun_finset (range n) {n} (by simp) ht).comp hF
    (measurable_pi_apply (⟨n,mem_singleton_self n⟩ : ({n} : Finset ℕ)))
  have heq : (fun ω => F (fun i : range n => tests i ω)) =
      (fun ω p => transcript (fun k => c (tests k ω)) n p) := by
    funext ω
    apply transcript_congr
    intro k hk
    simp only [extend, mem_range.mpr hk, dite_true]
  change IndepFun (fun ω => F (fun i : range n => tests i ω)) (tests n) ρ at hi
  rw [heq] at hi
  exact hi
end HistoriesMeasurable

section RandomDevice
open MeasureTheory ProbabilityTheory
variable {P Q C V : Type*} [Fintype P] [Fintype Q] [Fintype C] [DecidableEq C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_convex_sum_le {A : Type*} [Fintype A] (a : A → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) (u : A → V) {R : ℝ}
    (hu : ∀ i, ‖u i‖ ≤ R) : ‖∑ i, a i • u i‖ ≤ R := by
  calc
    _ ≤ ∑ i, ‖a i • u i‖ := norm_sum_le _ _
    _ = ∑ i, a i * ‖u i‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg, ha]
    _ ≤ ∑ i, a i * R := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hu i) (ha i)
    _ = R := by rw [← sum_mul, hs, one_mul]

lemma testDiscrepancy_bound {H : Type*} [Fintype H] [DecidableEq H]
    (κ : Q → ℝ) (w : Q → P → ℝ) (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (h : P → H) (c : P → C) (v : C → V) (g : Q → V)
    {B B' : ℝ} (hB : 0 ≤ B) (_hB' : 0 ≤ B')
    (hv : ∀ c, ‖v c‖ ≤ B) (hg : ∀ q, ‖g q‖ ≤ B') :
    ‖testDiscrepancy κ w h c v g‖ ≤ 2*B*B' := by
  let u := fun p => v (c p) - mean (push (marginal κ w) (fun p => (h p,c p))) v (h p)
  have hu : ∀ p, ‖u p‖ ≤ 2*B := by
    intro p
    have hh := norm_mean_le (push (marginal κ w) (fun p => (h p,c p)))
      (push_nonneg (marginal_nonneg κ w hκ hw) _) v hB hv (h p)
    exact (norm_sub_le _ _).trans (by linarith [hv (c p)])
  have hqu : ∀ q, ‖∑ p, w q p • u p‖ ≤ 2*B := fun q =>
    norm_convex_sum_le _ (hw q) (hsw q) u hu
  rw [testDiscrepancy, Real.norm_eq_abs, abs_abs]
  calc
    _ ≤ ∑ q, |κ q * ⟪∑ p, w q p • u p,g q⟫_ℝ| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, κ q * (2*B*B') := by
      apply sum_le_sum
      intro q _
      rw [abs_mul, abs_of_nonneg (hκ q)]
      apply mul_le_mul_of_nonneg_left _ (hκ q)
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hqu q) (hg q) (norm_nonneg _) (by positivity))
    _ = _ := by rw [← sum_mul, hsκ, one_mul]

variable [MeasurableSpace C]
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
  {ρ : Measure Ω} {ν : Measure T} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]

theorem random_prediction (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (tests : ℕ → Ω → T) (ht : ∀ n, Measurable (tests n))
    (hind : iIndepFun tests ρ) (hlaw : ∀ n, ρ.map (tests n) = ν) (t0 : T)
    (c : T → P → C) (v : T → C → V) (g : T → Q → V)
    (hc : ∀ p, Measurable (fun t => c t p))
    (hδ : ∀ n, Measurable (fun z : (P → History C n) × T =>
      testDiscrepancy κ w z.1 (c z.2) (v z.2) (g z.2)))
    {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hv : ∀ t c, ‖v t c‖ ≤ B) (hg : ∀ t q, ‖g t q‖ ≤ B')
    (K : ℕ) (hK : 0 < K) :
    (∑ n ∈ range K, ∫ ω, ∫ t, testDiscrepancy κ w
      (transcript (fun k => c (tests k ω)) n) (c t) (v t) (g t) ∂ν ∂ρ)/(K:ℝ) ≤
      4*B*B'*sqrt (sqrt (KL (wedge κ w)
        (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))) := by
  let H := fun n ω p => transcript (fun k => c (tests k ω)) n p
  let δ := fun n (z : (P → History C n) × T) =>
    testDiscrepancy κ w z.1 (c z.2) (v z.2) (g z.2)
  have hH : ∀ n, Measurable (H n) := fun n =>
    measurable_transcript _ (fun k p => (hc p).comp (ht k)) n
  have hb : ∀ n z, ‖δ n z‖ ≤ 2*B*B' := fun n z =>
    testDiscrepancy_bound κ w hκ hw hsκ hsw z.1 (c z.2) (v z.2) (g z.2) hB hB' (hv z.2) (hg z.2)
  have hfresh (n : ℕ) : (∫ ω, δ n (H n ω,tests n ω) ∂ρ) =
      ∫ ω, ∫ t, δ n (H n ω,t) ∂ν ∂ρ :=
    fresh_integral (H n) (tests n) (hH n) (ht n)
      (prefix_independent tests ht hind t0 c hc n) (hlaw n) (δ n) (hδ n) _ (hb n)
  change (∑ n ∈ range K, ∫ ω, ∫ t, δ n (H n ω,t) ∂ν ∂ρ)/(K:ℝ) ≤ _
  simp_rw [← hfresh]
  apply average_integral_bound K hK
  · intro n _
    exact Integrable.of_bound ((hδ n).comp ((hH n).prodMk (ht n))).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => hb n (H n ω,tests n ω))
  · intro ω
    exact frozen_prediction κ w hκ hw hsκ hsw
      (fun n => c (tests n ω)) (fun n => v (tests n ω)) (fun n => g (tests n ω))
      hB hB' (fun n => hv (tests n ω)) (fun n => hg (tests n ω)) K hK

lemma sqrt_sqrt_eq_quarter {x : ℝ} (hx : 0 ≤ x) : sqrt (sqrt x) = x ^ (1/4:ℝ) := by
  rw [sqrt_eq_rpow, sqrt_eq_rpow, ← rpow_mul hx]
  norm_num

theorem exists_prediction_history [Nonempty C]
    (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (c : T → P → C) (v : T → C → V) (g : T → Q → V)
    (hc : ∀ p, Measurable (fun t => c t p))
    (hδ : ∀ n, Measurable (fun z : (P → History C n) × T =>
      testDiscrepancy κ w z.1 (c z.2) (v z.2) (g z.2)))
    {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hv : ∀ t c, ‖v t c‖ ≤ B) (hg : ∀ t q, ‖g t q‖ ≤ B')
    (K : ℕ) (hK : 0 < K) :
    ∃ n < K, ∃ h : P → History C n,
      (univ.image h).card ≤ (Fintype.card C)^(K-1) ∧
      (∫ t, testDiscrepancy κ w h (c t) (v t) (g t) ∂ν) ≤
        4*B*B'*(KL (wedge κ w)
          (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))^(1/4:ℝ) := by
  classical
  let ρ : Measure (ℕ → T) := Measure.infinitePi (fun _ : ℕ => ν)
  let tests := fun n (ω : ℕ → T) => ω n
  have ht : ∀ n, Measurable (tests n) := fun n => measurable_pi_apply n
  have hind : iIndepFun tests ρ := iIndepFun_infinitePi (fun _ => measurable_id)
  have hlaw : ∀ n, ρ.map (tests n) = ν := fun n =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) n).map_eq
  let t0 : T := Classical.choice (nonempty_of_isProbabilityMeasure ν)
  have hpred := random_prediction κ w hκ hw hsκ hsw tests ht hind hlaw t0 c v g hc hδ
    hB hB' hv hg K hK
  have hD : 0 ≤ KL (wedge κ w) (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2) := by
    have hm := marginal_nonneg κ w hκ hw
    have hs := marginal_sum κ w hsκ hsw
    apply KL_nonneg _ _ (wedge_nonneg κ w hκ hw) (fun pr => mul_nonneg (hm _) (hm _))
      (wedge_sum κ w hsκ hsw) _ (wedge_ac κ w hκ hw)
    rw [Fintype.sum_prod_type, ← sum_mul_sum, hs, one_mul]
  rw [sqrt_sqrt_eq_quarter (div_nonneg hD (Nat.cast_nonneg K))] at hpred
  let R := 4*B*B'*(KL (wedge κ w)
    (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))^(1/4:ℝ)
  let H := fun n ω p => transcript (fun k => c (tests k ω)) n p
  let F := fun n (ω : ℕ → T) => ∫ t, testDiscrepancy κ w (H n ω) (c t) (v t) (g t) ∂ν
  have hsum : (∑ n ∈ range K, ∫ ω, F n ω ∂ρ) ≤ ∑ _ ∈ range K, R := by
    have he := (div_le_iff₀ (show (0:ℝ) < K by exact_mod_cast hK)).mp hpred
    simpa only [sum_const, card_range, nsmul_eq_mul, mul_comm, R, F, H] using he
  obtain ⟨n,hn,hnb⟩ := exists_le_of_sum_le (nonempty_range_iff.mpr (Nat.ne_of_gt hK)) hsum
  have hH : Measurable (H n) := measurable_transcript _ (fun k p => (hc p).comp (ht k)) n
  have hpair : Measurable (fun z : (ℕ → T) × T => (H n z.1,z.2)) :=
    (hH.comp measurable_fst).prodMk measurable_snd
  have hi : Integrable (fun z : (ℕ → T) × T =>
      testDiscrepancy κ w (H n z.1) (c z.2) (v z.2) (g z.2)) (ρ.prod ν) :=
    Integrable.of_bound ((hδ n).comp hpair).aestronglyMeasurable (2*B*B')
      (Filter.Eventually.of_forall fun z => testDiscrepancy_bound κ w hκ hw hsκ hsw
        (H n z.1) (c z.2) (v z.2) (g z.2) hB hB' (hv z.2) (hg z.2))
  obtain ⟨ω,hω⟩ := exists_le_integral hi.integral_prod_left
  have hn' : n < K := mem_range.mp hn
  refine ⟨n,hn',H n ω,?_,hω.trans hnb⟩
  calc
    _ ≤ Fintype.card (History C n) := card_le_univ _
    _ = (Fintype.card C)^n := history_card C n
    _ ≤ _ := Nat.pow_le_pow_right Fintype.card_pos (by omega)
end RandomDevice

end PlanarUnitDistances.FiniteInformation

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.UnitCodegree
open Polynomial Complex
open scoped ComplexConjugate

lemma unit_distance_equation (p q : ℂ) (h : dist p q = 1) :
    (q-p)*(conj q-conj p) = 1 := by
  rw [← map_sub, mul_conj, normSq_eq_norm_sq, ← dist_eq_norm, dist_comm q p, h]
  norm_num

end PlanarUnitDistances.UnitCodegree

namespace PlanarUnitDistances.UniformGraphLaw
open Finset FiniteLaw FiniteStarCoupling IncidenceEntropy
open scoped Classical BigOperators
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma right_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (q : Q) :
    (right (law E hE)).val q=degree E q/edgeCount E := by
  rw [right_val]
  simp only [law,←sum_div,degree]
lemma left_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (p : P) :
    (left (law E hE)).val p=pointLaw E p := by
  rw [left_val]
  simp only [law,←sum_div,pointLaw]
lemma col_eq (E : P → Q → Prop) (hE : 0<edgeCount E) {q : Q}
    (hq : 0<degree E q) (p : P) :
    (col (law E hE) q).val p=indicator E p q/degree E q := by
  rw [col_val (law E hE) (by rw [right_eq]; exact div_pos hq hE),right_eq]
  change (indicator E p q/edgeCount E)/(degree E q/edgeCount E)=_
  field_simp
end
end PlanarUnitDistances.UniformGraphLaw

namespace PlanarUnitDistances.GeometricLaw
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
lemma row_count (P Q : Finset Plane) (p : P) :
    (∑q,IncidenceEntropy.indicator (E P Q) p q)=CircleIncidence.degree Q p := by
  change (∑q : Q,if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)=_
  rw [CircleIncidence.degree_sum]
  exact (Finset.sum_coe_sort Q (fun q => if dist (p:Plane) q=1 then (1:ℝ) else 0)).trans
    (by simp only [dist_comm])
lemma left_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) :
    (left (graph P Q he)).val p=CircleIncidence.degree Q p/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.left_eq,IncidenceEntropy.pointLaw,edgeCount_eq,row_count]
lemma right_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (q : Q) :
    (right (graph P Q he)).val q=CircleIncidence.degree P q/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.right_eq,degree_eq,edgeCount_eq]
lemma counting_event (P : Finset Plane) (hp : 0<P.card) (A : Finset P) :
    event (counting P hp) (fun p => p∈A)=(A.card:ℝ)/(P.card:ℝ) := by
  have hattach : P.attach ∩ A=A := by ext p; simp
  simp [event,avg,counting,mul_ite,Finset.sum_ite_mem,hattach,div_eq_mul_inv]

lemma image_sub {P : Finset Plane} (A : Finset P) : image A⊆P := by
  intro p hp
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
  exact a.property
lemma image_card {P : Finset Plane} (A : Finset P) : (image A).card=A.card :=
  Finset.card_image_of_injective _ Subtype.val_injective
lemma event_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    (A : Finset P) (B : Finset Q) :
    event (graph P Q he) (fun pq => pq.1∈A ∧ pq.2∈B)=
      CircleIncidence.incidences (image A) (image B)/CircleIncidence.incidences P Q := by
  simp only [event,avg,graph,UniformGraphLaw.law,edgeCount_eq,Fintype.sum_prod_type]
  simp_rw [mul_ite,mul_one,mul_zero,ite_and]
  have hattach : Q.attach ∩ B=B := by ext q; simp
  have hsum : ∀p : P,
      (∑q : Q,if p∈A then if q∈B then IncidenceEntropy.indicator (E P Q) p q/CircleIncidence.incidences P Q else 0 else 0)=
      if p∈A then ∑q∈B,IncidenceEntropy.indicator (E P Q) p q/CircleIncidence.incidences P Q else 0 := by
    intro p
    by_cases hp : p∈A
    · simp [hp,hattach]
    · simp [hp]
  simp_rw [hsum]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  simp_rw [←Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  unfold CircleIncidence.incidences image
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  apply Finset.sum_congr rfl
  intro q _
  rw [CircleIncidence.degree_sum,Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  rfl

theorem expansion (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    {ξ : ℝ}
    (hx : ∀A⊆P,∀B⊆Q,CircleIncidence.incidences A B/CircleIncidence.incidences P Q ≤
      Real.sqrt ((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))*
        (((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))^(1/25:ℝ)+ξ)) :
    ∀A : Finset P,∀B : Finset Q,event (graph P Q he) (fun pq => pq.1∈A ∧ pq.2∈B) ≤
      Real.sqrt (event (counting P (card_pos P Q he).1) (fun p => p∈A)*
        event (counting Q (card_pos P Q he).2) (fun q => q∈B))*
        ((event (counting P (card_pos P Q he).1) (fun p => p∈A)*
          event (counting Q (card_pos P Q he).2) (fun q => q∈B))^(1/25:ℝ)+ξ) := by
  intro A B
  rw [event_eq,counting_event,counting_event]
  simpa only [image_card] using hx (image A) (image_sub A) (image B) (image_sub B)

lemma wedge_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    (hd : ∀q : Q,0<CircleIncidence.degree P q) :
    FiniteInformation.wedge (right (graph P Q he)).val (fun q => (col (graph P Q he) q).val)=
      IncidenceEntropy.wedge (E P Q) := by
  funext pr
  unfold FiniteInformation.wedge IncidenceEntropy.wedge
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  rw [graph,UniformGraphLaw.right_eq]
  simp only [UniformGraphLaw.col_eq _ _ (by rw [degree_eq]; exact hd q)]
  have hq : IncidenceEntropy.degree (E P Q) q≠0 := by rw [degree_eq]; exact (hd q).ne'
  field_simp

end
end PlanarUnitDistances.GeometricLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sequence
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceSequence
open Filter PowerGrowth CircleIncidence
open scoped Classical
noncomputable section
lemma Good.point_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (p : P) : 0 < degree Q p := by
  have hm : (0:ℝ) < P.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).1
  have hh := (le_div_iff₀ h.positive).mp (h.atomP p p.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hm) h.positive).trans_le hh

lemma Good.center_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (q : Q) : 0 < degree P q := by
  have hn : (0:ℝ) < Q.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).2
  have hh := (le_div_iff₀ h.positive).mp (h.atomQ q q.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hn) h.positive).trans_le hh

lemma Sequence.accuracy_limit : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma Sequence.error_limit (s : Sequence) : Tendsto s.ξ atTop (nhds 0) :=
  squeeze_zero (fun i => (s.good i).error_nonneg) (fun i => (s.good i).error_le)
    Sequence.accuracy_limit

end
end PlanarUnitDistances.IncidenceSequence

namespace PlanarUnitDistances.CommonFieldModel
open scoped Classical
noncomputable section
variable (P Q : Finset Plane)

variable {P Q}

namespace Model
variable (M : Model P Q)
lemma unit_identity (p : P) (q : Q) (h : dist (p:Plane) (q:Plane)=1) :
    (M.z (.inl p)-M.z (.inr q))*(M.w (.inl p)-M.w (.inr q))=1 := by
  apply Subtype.val_injective
  change ((M.z (.inl p):ℂ)-(M.z (.inr q):ℂ))*((M.w (.inl p):ℂ)-(M.w (.inr q):ℂ))=1
  simp only [M.z_eq,M.w_eq,location,Sum.elim_inl,Sum.elim_inr]
  exact UnitCodegree.unit_distance_equation _ _ (by
    rw [UnitCodegree.zCoordinate.dist_map,dist_comm]; exact h)

end Model
end
end PlanarUnitDistances.CommonFieldModel

namespace PlanarUnitDistances.ExpansionConsequences
open Finset Real

section FiniteLaw
variable {P Q : Type*} [Fintype P] [Fintype Q]
variable (w : P → Q → ℝ)

omit [Fintype P] in
lemma left_nonneg (hw : ∀ p q, 0 ≤ w p q) (p : P) : 0 ≤ left w p :=
  sum_nonneg (fun q _ => hw p q)
omit [Fintype Q] in
lemma right_nonneg (hw : ∀ p q, 0 ≤ w p q) (q : Q) : 0 ≤ right w q :=
  sum_nonneg (fun p _ => hw p q)
lemma mass_nonneg {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (s : Finset A) :
    0 ≤ mass μ s := sum_nonneg (fun a _ => hμ a)
lemma mass_le_one {A : Type*} [Fintype A] (μ : A → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμsum : ∑ a, μ a = 1) (s : Finset A) :
    mass μ s ≤ 1 := by
  simpa [mass, hμsum] using
    sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun a _ _ => hμ a)
lemma right_sum (hs : ∑ p, ∑ q, w p q = 1) : ∑ q, right w q = 1 := by
  unfold right
  rw [sum_comm]
  exact hs
omit [Fintype P] [Fintype Q] in
lemma rectangle_right (F : Finset P) (G : Finset Q) :
    rect w F G = ∑ q ∈ G, ∑ p ∈ F, w p q := by
  exact sum_comm
omit [Fintype Q] in
lemma conditional_nonneg (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) (q : Q) :
    0 ≤ conditional w F q :=
  div_nonneg (sum_nonneg (fun p _ => hw p q)) (right_nonneg w hw q)
omit [Fintype Q] in
lemma conditional_le_one (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) (q : Q) :
    conditional w F q ≤ 1 := by
  have hsub : (∑ p ∈ F, w p q) ≤ right w q :=
    sum_le_sum_of_subset_of_nonneg (subset_univ F) (fun p _ _ => hw p q)
  exact div_le_one_of_le₀ hsub (right_nonneg w hw q)
omit [Fintype Q] in
lemma right_mul_conditional (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) (q : Q) :
    right w q * conditional w F q = ∑ p ∈ F, w p q := by
  have hsub : (∑ p ∈ F, w p q) ≤ right w q :=
    sum_le_sum_of_subset_of_nonneg (subset_univ F) (fun p _ _ => hw p q)
  by_cases hq : right w q = 0
  · have hz : (∑ p ∈ F, w p q) = 0 :=
      le_antisymm (hq ▸ hsub) (sum_nonneg (fun p _ => hw p q))
    simp [hq, hz]
  · exact mul_div_cancel₀ _ hq
lemma conditional_mean (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) :
    ∑ q, right w q * conditional w F q = mass (left w) F := by
  simp_rw [right_mul_conditional w hw]
  rw [sum_comm]
  rfl
omit [Fintype Q] in
lemma rectangle_conditional (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) (G : Finset Q) :
    rect w F G = ∑ q ∈ G, right w q * conditional w F q := by
  rw [rectangle_right]
  simp_rw [right_mul_conditional w hw]

lemma threshold_markov {Q : Type*} [Fintype Q] (κ g : Q → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hg : ∀ q, 0 ≤ g q) {d : ℝ} (_hd : 0 ≤ d) :
    d * mass κ (univ.filter (fun q => d < g q)) ≤ ∑ q, κ q * g q := by
  classical
  rw [mass, mul_sum]
  calc
    _ ≤ ∑ q ∈ univ.filter (fun q => d < g q), κ q * g q := by
      apply sum_le_sum
      intro q hq
      calc
        d * κ q = κ q * d := mul_comm _ _
        _ ≤ κ q * g q := mul_le_mul_of_nonneg_left (le_of_lt (mem_filter.mp hq).2) (hκ q)
    _ ≤ ∑ q, κ q * g q :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => mul_nonneg (hκ q) (hg q))

lemma wedge_split (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) {d : ℝ} (hd : 0 ≤ d) :
    wedgeMass w F ≤ d * mass (left w) F +
      rect w F (univ.filter (fun q => d < conditional w F q)) := by
  classical
  rw [← conditional_mean w hw, rectangle_conditional w hw, mul_sum,
    sum_filter, ← sum_add_distrib]
  unfold wedgeMass
  apply sum_le_sum
  intro q _
  have hk := right_nonneg w hw q
  have hg := conditional_nonneg w hw F q
  have hg1 := conditional_le_one w hw F q
  by_cases hq : d < conditional w F q
  · simp only [hq, ↓reduceIte]
    nlinarith [mul_nonneg hk (mul_nonneg hd hg),
      mul_nonneg hk (mul_nonneg hg (sub_nonneg.mpr hg1))]
  · simp only [hq, ↓reduceIte, add_zero]
    have hqd := le_of_not_gt hq
    nlinarith [mul_nonneg hk (mul_nonneg hg (sub_nonneg.mpr hqd))]

theorem wedge_rare (hw : ∀ p q, 0 ≤ w p q) (F : Finset P)
    {θ d : ℝ} (hθ : 0 ≤ θ) (hd : 0 < d)
    (hexp : ∀ G : Finset Q, rect w F G ≤
      θ * sqrt (mass (left w) F * mass (right w) G)) :
    wedgeMass w F ≤ (d + θ / sqrt d) * mass (left w) F := by
  classical
  let G : Finset Q := univ.filter (fun q => d < conditional w F q)
  let h := mass (left w) F
  let k := mass (right w) G
  have hh : 0 ≤ h := mass_nonneg _ (left_nonneg w hw) F
  have hk : 0 ≤ k := mass_nonneg _ (right_nonneg w hw) G
  have hdg : d*k ≤ h := by
    simpa [G, h, k, conditional_mean w hw] using
      threshold_markov (right w) (conditional w F) (right_nonneg w hw)
        (conditional_nonneg w hw F) hd.le
  have hroot : sqrt d * sqrt (h*k) ≤ h := by
    have hs := sq_sqrt (mul_nonneg hh hk)
    have hd2 := sq_sqrt hd.le
    have hn := sqrt_nonneg d
    have hn' := sqrt_nonneg (h*k)
    have hm := mul_le_mul_of_nonneg_left hdg hh
    nlinarith [sq_nonneg (sqrt d * sqrt (h*k) - h)]
  have hspos : 0 < sqrt d := sqrt_pos.mpr hd
  have hb : sqrt (h*k) ≤ h / sqrt d := (le_div_iff₀ hspos).mpr (by nlinarith)
  calc
    wedgeMass w F ≤ d*h + rect w F G := wedge_split w hw F hd.le
    _ ≤ d*h + θ*sqrt (h*k) := by linarith [hexp G]
    _ ≤ d*h + θ*(h / sqrt d) := by linarith [mul_le_mul_of_nonneg_left hb hθ]
    _ = (d + θ / sqrt d)*h := by ring

end FiniteLaw

section LabelMatching
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma outside_mass (μ : A → ℝ) (hs : ∑ p, μ p = 1) (a : A) :
    mass μ (outside a) = 1 - μ a := by
  have he : outside a = univ.erase a := by ext p; simp [outside, ne_comm]
  rw [he, mass]
  have hh := sum_erase_add univ μ (mem_univ a)
  linarith

lemma matched_add_mismatch (w : A → A → ℝ) :
    (∑ a, w a a) + mismatch w = ∑ p, ∑ q, w p q := by
  have he (p : A) : w p p = ∑ q, if p = q then w p q else 0 := by simp
  simp_rw [he]
  unfold mismatch
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  by_cases h : p=q <;> simp [h]

lemma mass_left_indicator (w : A → A → ℝ) (a : A) :
    mass (left w) (outside a) = ∑ p, ∑ q, if p ≠ a then w p q else 0 := by
  simp only [mass, outside, sum_filter, left, sum_ite_irrel, sum_const_zero]
lemma mass_right_indicator (w : A → A → ℝ) (a : A) :
    mass (right w) (outside a) = ∑ p, ∑ q, if q ≠ a then w p q else 0 := by
  rw [sum_comm]
  simp only [mass, outside, sum_filter, right, sum_ite_irrel, sum_const_zero]
lemma rect_outside_indicator (w : A → A → ℝ) (a : A) :
    rect w (outside a) (outside a) =
      ∑ p, ∑ q, if p ≠ a ∧ q ≠ a then w p q else 0 := by
  simp only [rect, outside, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p ≠ a
  · simp [hp]
  · simp [hp]

lemma exactly_one_le_mismatch (w : A → A → ℝ) (hw : ∀ p q, 0 ≤ w p q) (a : A) :
    mass (left w) (outside a) + mass (right w) (outside a) ≤
      mismatch w + 2*rect w (outside a) (outside a) := by
  rw [mass_left_indicator, mass_right_indicator, rect_outside_indicator]
  unfold mismatch
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro p _
  apply sum_le_sum
  intro q _
  by_cases hp : p=a <;> by_cases hq : q=a <;> by_cases he : p=q <;>
    simp_all <;> linarith [hw p q]

omit [DecidableEq A] in
lemma diagonal_expansion (w : A → A → ℝ) (U V : A → ℝ)
    (hU : ∀ a, 0 ≤ U a) (hV : ∀ a, 0 ≤ V a)
    (hUs : ∑ a, U a = 1) (hVs : ∑ a, V a = 1)
    {η ξ z : ℝ} (hη : 0 ≤ η) (hξ : 0 ≤ ξ) (hz : 0 ≤ z)
    (huv : ∀ a, U a * V a ≤ z)
    (hexp : ∀ a, w a a ≤ sqrt (U a*V a) * ((U a*V a)^η+ξ)) :
    ∑ a, w a a ≤ z^η+ξ := by
  have hcs : ∑ a, sqrt (U a*V a) ≤ 1 := by
    simpa only [sqrt_mul (hU _), hUs, hVs, sqrt_one, mul_one] using
      sum_sqrt_mul_sqrt_le univ hU hV
  calc
    _ ≤ ∑ a, sqrt (U a*V a) * (z^η+ξ) := by
      apply sum_le_sum
      intro a _
      exact (hexp a).trans (mul_le_mul_of_nonneg_left
        (by linarith [rpow_le_rpow (mul_nonneg (hU a) (hV a)) (huv a) hη])
        (sqrt_nonneg _))
    _ = (∑ a, sqrt (U a*V a)) * (z^η+ξ) := by rw [sum_mul]
    _ ≤ z^η+ξ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcs) (add_nonneg (rpow_nonneg hz η) hξ)]

theorem matching_dominant (w : A → A → ℝ) (U V : A → ℝ)
    (hw : ∀ p q, 0 ≤ w p q) (hws : ∑ p, ∑ q, w p q = 1)
    (hU : ∀ a, 0 ≤ U a) (hV : ∀ a, 0 ≤ V a)
    (hUs : ∑ a, U a = 1) (hVs : ∑ a, V a = 1)
    {γ η ξ ε : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (_hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleft : ∀ a, γ*U a ≤ left w a) (hright : ∀ a, γ*V a ≤ right w a)
    (hexp : ∀ F G : Finset A, rect w F G ≤
      sqrt (mass U F * mass V G) * ((mass U F * mass V G)^η+ξ))
    (hsmall : (1-ε)^η+ξ < 1-mismatch w)
    (htiny : ε^η+ξ ≤ γ/2) :
    ∃ a, mass (left w) (outside a) + mass (right w) (outside a) ≤ 2*mismatch w := by
  have hUle (a : A) : U a ≤ 1 := by
    simpa [mass] using mass_le_one U hU hUs {a}
  have hVle (a : A) : V a ≤ 1 := by
    simpa [mass] using mass_le_one V hV hVs {a}
  have hex : ∃ a, 1-ε < U a * V a := by
    by_contra hn
    push Not at hn
    have he := diagonal_expansion w U V hU hV hUs hVs hη hξ (sub_nonneg.mpr hε1) hn
      (fun a => by simpa [rect, mass] using hexp {a} {a})
    have heq := matched_add_mismatch w
    linarith
  obtain ⟨a,ha⟩ := hex
  let F := outside a
  let h := mass (left w) F
  let k := mass (right w) F
  let x := mass U F
  let y := mass V F
  have hx0 : 0 ≤ x := mass_nonneg U hU F
  have hy0 : 0 ≤ y := mass_nonneg V hV F
  have hx : x ≤ ε := by
    have hp := mul_le_of_le_one_right (hU a) (hVle a)
    dsimp [x,F]
    rw [outside_mass U hUs]
    linarith
  have hy : y ≤ ε := by
    have hp := mul_le_of_le_one_left (hV a) (hUle a)
    dsimp [y,F]
    rw [outside_mass V hVs]
    linarith
  have hdL : γ*x ≤ h := by
    dsimp [x,h,mass]
    rw [mul_sum]
    exact sum_le_sum (fun a _ => hleft a)
  have hdR : γ*y ≤ k := by
    dsimp [y,k,mass]
    rw [mul_sum]
    exact sum_le_sum (fun a _ => hright a)
  have hsqrt : 2*γ*sqrt (x*y) ≤ h+k := by
    have hh := sq_sqrt (mul_nonneg hx0 hy0)
    have hr := sqrt_nonneg (x*y)
    have hs : 2*sqrt (x*y) ≤ x+y := by nlinarith [sq_nonneg (x-y)]
    have := mul_le_mul_of_nonneg_left hs hγ.le
    linarith
  have hxy : x*y ≤ ε := (mul_le_of_le_one_right hx0 (hy.trans hε1)).trans hx
  have hpow := rpow_le_rpow (mul_nonneg hx0 hy0) hxy hη
  have hJ : rect w F F ≤ (h+k)/4 := by
    have he := hexp F F
    have hm := mul_le_mul_of_nonneg_left (show (x*y)^η+ξ ≤ γ/2 by linarith)
      (sqrt_nonneg (x*y))
    change rect w F F ≤ sqrt (x*y) * ((x*y)^η+ξ) at he
    nlinarith
  refine ⟨a, ?_⟩
  have hm := exactly_one_le_mismatch w hw a
  change h+k ≤ 2*mismatch w
  change h+k ≤ mismatch w + 2*rect w F F at hm
  linarith

lemma independent_mismatch_le (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (hs : ∑ a, μ a = 1) (a : A) :
    mismatch (fun p q => μ p * μ q) ≤ 2*mass μ (outside a) := by
  have he : ∀ p q, (if p ≠ q then μ p*μ q else 0) ≤
      (if p ≠ a then μ p*μ q else 0) + (if q ≠ a then μ p*μ q else 0) := by
    intro p q
    by_cases hp : p=a <;> by_cases hq : q=a <;> by_cases he : p=q <;>
      simp_all <;> nlinarith [mul_nonneg (hμ p) (hμ q)]
  have hh := sum_le_sum (s := univ) (fun p _ => sum_le_sum (s := univ) (fun q _ => he p q))
  simp only [sum_add_distrib] at hh
  rw [← mass_left_indicator, ← mass_right_indicator] at hh
  have hl : left (fun p q => μ p*μ q) = μ := by
    funext p
    simp [left, ← mul_sum, hs]
  have hr : right (fun p q => μ p*μ q) = μ := by
    funext q
    simp [right, ← sum_mul, hs]
  rw [hl,hr] at hh
  unfold mismatch
  linarith

lemma mismatch_nonneg (w : A → A → ℝ) (hw : ∀ p q, 0 ≤ w p q) :
    0 ≤ mismatch w := by
  unfold mismatch
  exact sum_nonneg (fun p _ => sum_nonneg (fun q _ => by split_ifs; exact hw p q; exact le_rfl))
lemma mismatch_le_one (w : A → A → ℝ) (hw : ∀ p q, 0 ≤ w p q)
    (hws : ∑ p, ∑ q, w p q = 1) : mismatch w ≤ 1 := by
  rw [← hws]
  exact sum_le_sum (fun p _ => sum_le_sum (fun q _ => by split_ifs <;> simp_all))

end LabelMatching

theorem matching_parameters {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) :
    ∃ ε s₀ ξ₀ : ℝ, 0 < s₀ ∧ 0 < ξ₀ ∧ 0 ≤ ε ∧ ε ≤ 1 ∧
      ∀ s ξ : ℝ, ξ ≤ ξ₀ → s ≤ s₀ →
        (1-ε)^η+ξ < 1-s ∧ ε^η+ξ ≤ γ/2 := by
  let b := min (γ/4) (1/2 : ℝ)
  have hb : 0 < b := lt_min (by linarith) (by norm_num)
  have hb1 : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let ε := b^(1/η)
  have he0 : 0 < ε := rpow_pos_of_pos hb _
  have he1 : ε < 1 := rpow_lt_one hb.le hb1 (one_div_pos.mpr hη)
  have he : ε^η = b := by
    dsimp [ε]
    rw [← rpow_mul hb.le, one_div_mul_cancel hη.ne', rpow_one]
  have hg : 0 < 1-(1-ε)^η := by
    have := rpow_lt_one (by linarith : 0 ≤ 1-ε) (by linarith : 1-ε < 1) hη
    linarith
  let s₀ := (1-(1-ε)^η)/4
  let ξ₀ := min (γ/4) s₀
  refine ⟨ε,s₀,ξ₀,by dsimp [s₀]; positivity,lt_min (by linarith) (by dsimp [s₀]; positivity),
    he0.le,he1.le,?_⟩
  intro s ξ hξ hs
  have hξs : ξ ≤ s₀ := hξ.trans (min_le_right _ _)
  have hξγ : ξ ≤ γ/4 := hξ.trans (min_le_left _ _)
  have hbγ : b ≤ γ/4 := min_le_left _ _
  dsimp [s₀] at hs hξs
  constructor <;> linarith

universe u

theorem uniform_label_matching {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) :
    ∃ s₀ ξ₀ C : ℝ, 0 < s₀ ∧ 0 < ξ₀ ∧ 0 < C ∧
    ∀ (A : Type u) [Fintype A] [DecidableEq A]
      (w : A → A → ℝ) (U V : A → ℝ),
      (∀ p q, 0 ≤ w p q) → (∑ p, ∑ q, w p q = 1) →
      (∀ a, 0 ≤ U a) → (∀ a, 0 ≤ V a) → (∑ a, U a = 1) → (∑ a, V a = 1) →
      (∀ a, γ*U a ≤ left w a) → (∀ a, γ*V a ≤ right w a) →
      ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ ξ₀ →
      (∀ F G : Finset A, rect w F G ≤
        sqrt (mass U F * mass V G) * ((mass U F * mass V G)^η+ξ)) →
      (mismatch w ≤ s₀ → ∃ a, mass (left w) (outside a) +
        mass (right w) (outside a) ≤ C*mismatch w) ∧
      mismatch (fun p q => left w p * left w q) ≤ C*mismatch w ∧
      mismatch (fun p q => right w p * right w q) ≤ C*mismatch w := by
  obtain ⟨ε,s₀,ξ₀,hs₀,hξ₀,he0,he1,hpar⟩ := matching_parameters hγ hη
  let C := max (4 : ℝ) (1/s₀)
  have hC4 : 4 ≤ C := le_max_left _ _
  have hCs : 1/s₀ ≤ C := le_max_right _ _
  refine ⟨s₀,ξ₀,C,hs₀,hξ₀,lt_of_lt_of_le (by norm_num : (0:ℝ)<4) hC4,?_⟩
  intro A _ _ w U V hw hws hU hV hUs hVs hl hr ξ hξ hξb hexp
  have hls : ∑ a, left w a = 1 := hws
  have hrs : ∑ a, right w a = 1 := right_sum w hws
  have hmn := mismatch_nonneg w hw
  have hmnL := left_nonneg w hw
  have hmnR := right_nonneg w hw
  have hsmall (hs : mismatch w ≤ s₀) : ∃ a, mass (left w) (outside a) +
      mass (right w) (outside a) ≤ 2*mismatch w := by
    obtain ⟨ha,hb⟩ := hpar (mismatch w) ξ hξb hs
    exact matching_dominant w U V hw hws hU hV hUs hVs hγ hη.le hξ he0 he1
      hl hr hexp ha hb
  have hindL : mismatch (fun p q => left w p*left w q) ≤ 1 := by
    apply mismatch_le_one _ (fun p q => mul_nonneg (hmnL p) (hmnL q))
    simp_rw [← mul_sum, hls, mul_one]
    exact hls
  have hindR : mismatch (fun p q => right w p*right w q) ≤ 1 := by
    apply mismatch_le_one _ (fun p q => mul_nonneg (hmnR p) (hmnR q))
    simp_rw [← mul_sum, hrs, mul_one]
    exact hrs
  constructor
  · intro hs
    obtain ⟨a,ha⟩ := hsmall hs
    exact ⟨a, ha.trans (mul_le_mul_of_nonneg_right (by linarith : 2 ≤ C) hmn)⟩
  by_cases hs : mismatch w ≤ s₀
  · obtain ⟨a,ha⟩ := hsmall hs
    have hl0 := mass_nonneg _ hmnL (outside a)
    have hr0 := mass_nonneg _ hmnR (outside a)
    have hlb := independent_mismatch_le (left w) hmnL hls a
    have hrb := independent_mismatch_le (right w) hmnR hrs a
    have hc := mul_le_mul_of_nonneg_right hC4 hmn
    constructor <;> linarith
  · have hbig : 1 ≤ C*mismatch w := by
      have hgt : s₀ ≤ mismatch w := le_of_lt (lt_of_not_ge hs)
      have hdiv : 1 ≤ mismatch w / s₀ := (le_div_iff₀ hs₀).mpr (by simpa)
      have hc := mul_le_mul_of_nonneg_right hCs hmn
      have hid : mismatch w / s₀ = (1/s₀)*mismatch w := by ring
      rw [hid] at hdiv
      exact hdiv.trans hc
    exact ⟨hindL.trans hbig, hindR.trans hbig⟩

end PlanarUnitDistances.ExpansionConsequences

namespace PlanarUnitDistances.LawExpansion
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q A : Type*} [Fintype P] [Fintype Q] [Fintype A]

lemma push_event {X Y : Type*} [Fintype X] [Fintype Y] (μ : Law X) (f : X → Y) (g : Y → Prop) :
    event (push μ f) g=event μ (fun x => g (f x)) := push_avg μ f _

lemma mass_event (μ : Law P) (F : Finset P) :
    ExpansionConsequences.mass μ.val F=event μ (fun p => p∈F) := by
  unfold ExpansionConsequences.mass event avg
  simp only [mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_of_subset (subset_univ _)]

lemma rect_event (π : Law (P×Q)) (F : Finset P) (G : Finset Q) :
    ExpansionConsequences.rect (fun p q => π.val (p,q)) F G=
      event π (fun pq => pq.1∈F ∧ pq.2∈G) := by
  simp only [ExpansionConsequences.rect,event,avg,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]
  symm
  calc
    _ = ∑p,if p∈F then ∑q∈G,π.val (p,q) else 0 := by
      apply sum_congr rfl
      intro p _
      by_cases hp : p∈F
      · simp only [hp,true_and,↓reduceIte,←sum_filter,filter_mem_eq_of_subset (subset_univ _)]
      · simp [hp]
    _ = _ := by rw [←sum_filter,filter_mem_eq_of_subset (subset_univ _)]

lemma left_val (π : Law (P×Q)) (p : P) :
    ExpansionConsequences.left (fun p q => π.val (p,q)) p=(FiniteStarCoupling.left π).val p := by
  simp only [ExpansionConsequences.left,FiniteStarCoupling.left,push,fiberMass_eq,Fintype.sum_prod_type]
  rw [sum_comm]
  simp
lemma right_val (π : Law (P×Q)) (q : Q) :
    ExpansionConsequences.right (fun p q => π.val (p,q)) q=(FiniteStarCoupling.right π).val q := by
  simp [ExpansionConsequences.right,FiniteStarCoupling.right,push,fiberMass_eq,Fintype.sum_prod_type]
lemma total (π : Law (P×Q)) : ∑p,∑q,π.val (p,q)=1 := by
  simpa only [Fintype.sum_prod_type] using π.total

lemma mismatch_event (π : Law (A×A)) :
    ExpansionConsequences.mismatch (fun a b => π.val (a,b))=event π (fun ab => ab.1≠ab.2) := by
  simp only [ExpansionConsequences.mismatch,event,avg,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]

lemma outside_event (μ : Law A) (a : A) :
    ExpansionConsequences.mass μ.val (ExpansionConsequences.outside a)=event μ (fun x => x≠a) := by
  rw [mass_event]
  simp only [ExpansionConsequences.outside,mem_filter,mem_univ,true_and]

lemma fiber_domination {X Y : Type*} [Fintype X] [Fintype Y] (μ ν : Law X) (f : X → Y)
    {γ : ℝ} (h : ∀x,γ*μ.val x≤ν.val x) (y : Y) : γ*(push μ f).val y≤(push ν f).val y := by
  simp only [push,fiberMass_eq,mul_sum]
  apply sum_le_sum
  intro x _
  split_ifs <;> simp_all

lemma pushed_left (π : Law (P×Q)) (a : P → A) (b : Q → A) (l : A) :
    (FiniteStarCoupling.left (push π (fun pq => (a pq.1,b pq.2)))).val l=
      (push (FiniteStarCoupling.left π) a).val l := by
  change event (push π (fun pq => (a pq.1,b pq.2))) (fun ab => ab.1=l)=event (push π Prod.fst) (fun p => a p=l)
  simp only [push_event]
lemma pushed_right (π : Law (P×Q)) (a : P → A) (b : Q → A) (l : A) :
    (FiniteStarCoupling.right (push π (fun pq => (a pq.1,b pq.2)))).val l=
      (push (FiniteStarCoupling.right π) b).val l := by
  change event (push π (fun pq => (a pq.1,b pq.2))) (fun ab => ab.2=l)=event (push π Prod.snd) (fun q => b q=l)
  simp only [push_event]

theorem matching {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃ s₀ ξ₀ C : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧
    ∀ (P Q A : Type) [Fintype P] [Fintype Q] [Fintype A],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q) (a : P → A) (b : Q → A),
    (∀p,γ*U.val p≤(FiniteStarCoupling.left π).val p) →
    (∀q,γ*W.val q≤(FiniteStarCoupling.right π).val q) →
    ∀ξ : ℝ,0≤ξ → ξ≤ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    (event π (fun pq => a pq.1≠b pq.2)≤ s₀ →
      ∃l,event (FiniteStarCoupling.left π) (fun p => a p≠l)+
        event (FiniteStarCoupling.right π) (fun q => b q≠l)≤C*event π (fun pq => a pq.1≠b pq.2)) := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hmatch⟩ := ExpansionConsequences.uniform_label_matching hγ hη
  refine ⟨s₀,ξ₀,C,hs,hξ,hC,?_⟩
  intro P Q A _ _ _ π U W a b hl hr ξ hξ0 hξb hexp hm
  let σ := push π (fun pq => (a pq.1,b pq.2))
  have he (F G : Finset A) : ExpansionConsequences.rect (fun a b => σ.val (a,b)) F G ≤
      Real.sqrt (ExpansionConsequences.mass (push U a).val F*ExpansionConsequences.mass (push W b).val G)*
      ((ExpansionConsequences.mass (push U a).val F*ExpansionConsequences.mass (push W b).val G)^η+ξ) := by
    simp only [rect_event,mass_event,σ,push_event]
    simpa only [mem_filter,mem_univ,true_and] using hexp (univ.filter (fun p => a p∈F)) (univ.filter (fun q => b q∈G))
  have hb := (hmatch A (fun a b => σ.val (a,b)) (push U a).val (push W b).val
    (fun a b => σ.nonneg (a,b)) (total σ) (push U a).nonneg (push W b).nonneg
    (push U a).total (push W b).total
    (fun l => by rw [left_val,pushed_left]; exact fiber_domination U (FiniteStarCoupling.left π) a hl l)
    (fun l => by rw [right_val,pushed_right]; exact fiber_domination W (FiniteStarCoupling.right π) b hr l)
    ξ hξ0 hξb he).1
  have hm' : ExpansionConsequences.mismatch (fun a b => σ.val (a,b))≤ s₀ := by
    simpa only [mismatch_event,σ,push_event] using hm
  obtain ⟨l,hl⟩ := hb hm'
  refine ⟨l,?_⟩
  have hle : ExpansionConsequences.left (fun a b => σ.val (a,b))=(push (FiniteStarCoupling.left π) a).val := by
    funext l
    rw [left_val]
    exact pushed_left π a b l
  have hre : ExpansionConsequences.right (fun a b => σ.val (a,b))=(push (FiniteStarCoupling.right π) b).val := by
    funext l
    rw [right_val]
    exact pushed_right π a b l
  rw [hle,hre,outside_event,outside_event,push_event,push_event,mismatch_event] at hl
  simpa only [σ,push_event] using hl
end
end PlanarUnitDistances.LawExpansion

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_AbsoluteValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset
noncomputable section

section Entries
variable (K : Type*) [Field K] [NumberField K]

lemma infiniteEntry_count : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K :=
  AlgHom.card ℚ K ℂ

end Entries

end
end PlanarUnitDistances.WeightedAbsoluteValues

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_HeightTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma fract_integrableOn (x a b : ℝ) :
    IntegrableOn (fun u => Int.fract (x+u)) (Icc a b) := by
  apply Integrable.of_bound ((measurable_const.add measurable_id).fract.aestronglyMeasurable) 1
  filter_upwards [] with u
  rw [Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

lemma floor_integrableOn (x a b : ℝ) :
    IntegrableOn (fun u => (⌊x+u⌋ : ℝ)) (Icc a b) := by
  have he : (fun u : ℝ => (⌊x+u⌋ : ℝ)) = fun u => (x+u)-Int.fract (x+u) := by
    funext u
    simp only [Int.fract]
    ring
  rw [he]
  exact (continuous_const.add continuous_id).integrableOn_Icc.sub (fract_integrableOn x a b)

lemma fract_shift_integral (x : ℝ) :
    (∫ u in (0:ℝ)..1, Int.fract (x+u)) = ∫ u in (0:ℝ)..1, Int.fract u := by
  have hp : Function.Periodic (Int.fract : ℝ → ℝ) 1 := Int.fract_add_one
  rw [intervalIntegral.integral_comp_add_left]
  simpa using hp.intervalIntegral_add_eq x 0

lemma floor_difference_integral (x y : ℝ) :
    (∫ u in Icc (0:ℝ) 1, ((⌊y+u⌋:ℝ)-(⌊x+u⌋:ℝ))) = y-x := by
  have he : (fun u : ℝ => ((⌊y+u⌋:ℝ)-(⌊x+u⌋:ℝ))) =
      fun u => (y-x) - (Int.fract (y+u)-Int.fract (x+u)) := by
    funext u
    simp only [Int.fract]
    ring
  have h₁ := integral_sub (μ := volume.restrict (Icc (0:ℝ) 1))
    (show Integrable (fun _ : ℝ => y-x) (volume.restrict (Icc 0 1)) from
      continuous_const.integrableOn_Icc)
    ((fract_integrableOn y 0 1).sub (fract_integrableOn x 0 1))
  have h₂ := integral_sub (fract_integrableOn y 0 1) (fract_integrableOn x 0 1)
  dsimp only [Pi.sub_apply] at h₁ h₂
  rw [he,h₁,h₂]
  have hh (z : ℝ) : (∫ u in Icc (0:ℝ) 1, Int.fract (z+u)) =
      ∫ u in Icc (0:ℝ) 1, Int.fract u := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    exact fract_shift_integral z
  rw [hh y,hh x,sub_self,sub_zero]
  simp

lemma mismatch_integrableOn (x y a b : ℝ) :
    IntegrableOn (mismatch x y) (Icc a b) := by
  have hm : Measurable (mismatch x y) := Measurable.ite
    (measurableSet_eq_fun (measurable_const.add measurable_id).floor
      (measurable_const.add measurable_id).floor) measurable_const measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with u
  unfold mismatch
  split <;> norm_num

lemma mismatch_symm (x y u : ℝ) : mismatch x y u = mismatch y x u := by
  simp only [mismatch,eq_comm]

lemma mismatch_integral_le_abs (x y : ℝ) :
    (∫ u in Icc (0:ℝ) 1, mismatch x y u) ≤ |x-y| := by
  wlog hxy : x ≤ y
  · simpa only [mismatch_symm x y,abs_sub_comm x y] using this y x (le_of_not_ge hxy)
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hxy),← floor_difference_integral x y]
  apply integral_mono (mismatch_integrableOn x y 0 1)
    ((floor_integrableOn y 0 1).sub (floor_integrableOn x 0 1))
  intro u
  have hm := Int.floor_mono (show x+u ≤ y+u by linarith)
  dsimp only [Pi.sub_apply]
  unfold mismatch
  split_ifs with he
  · exact_mod_cast sub_nonneg.mpr hm
  · have hs : ⌊x+u⌋ < ⌊y+u⌋ := lt_of_le_of_ne hm he
    have hz : (1:ℤ) ≤ ⌊y+u⌋-⌊x+u⌋ := by omega
    exact_mod_cast hz

end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma gridLabel_measurable (r : ℝ) (z : ℂ) : Measurable (gridLabel r z) :=
  ((measurable_const.add measurable_fst).floor).prodMk
    ((measurable_const.add measurable_snd).floor)

lemma gridMismatch_measurable (r : ℝ) (z w : ℂ) : Measurable (gridMismatch r z w) :=
  Measurable.ite (measurableSet_eq_fun (gridLabel_measurable r z)
    (gridLabel_measurable r w)) measurable_const measurable_const

lemma gridMismatch_integrable (r : ℝ) (z w : ℂ) :
    Integrable (gridMismatch r z w) squareShift := by
  apply Integrable.of_bound (gridMismatch_measurable r z w).aestronglyMeasurable 1
  filter_upwards [] with u
  unfold gridMismatch
  split <;> norm_num

lemma gridMismatch_le_coordinates (r : ℝ) (z w : ℂ) (u : ℝ × ℝ) :
    gridMismatch r z w u ≤ mismatch (z.re/r) (w.re/r) u.1 +
      mismatch (z.im/r) (w.im/r) u.2 := by
  unfold gridMismatch gridLabel mismatch
  simp only [Prod.mk.injEq]
  split_ifs <;> norm_num at *
  tauto

lemma coordinate_mismatch_measurable (x y : ℝ) : Measurable (mismatch x y) :=
  Measurable.ite (measurableSet_eq_fun (measurable_const.add measurable_id).floor
    (measurable_const.add measurable_id).floor) measurable_const measurable_const

lemma coordinate_mismatch_integrable (x y : ℝ) (i : ℝ × ℝ → ℝ)
    (hi : Measurable i) : Integrable (fun u => mismatch x y (i u)) squareShift := by
  apply Integrable.of_bound ((coordinate_mismatch_measurable x y).comp hi).aestronglyMeasurable 1
  filter_upwards [] with u
  change ‖if ⌊x+i u⌋ = ⌊y+i u⌋ then (0:ℝ) else 1‖ ≤ 1
  split <;> norm_num

lemma integral_mismatch_fst (x y : ℝ) :
    (∫ u, mismatch x y u.1 ∂squareShift) = ∫ u in Icc (0:ℝ) 1, mismatch x y u := by
  rw [squareShift,integral_prod _ (coordinate_mismatch_integrable x y Prod.fst measurable_fst)]
  simp [unitShift]

lemma integral_mismatch_snd (x y : ℝ) :
    (∫ u, mismatch x y u.2 ∂squareShift) = ∫ u in Icc (0:ℝ) 1, mismatch x y u := by
  rw [squareShift,integral_prod _ (coordinate_mismatch_integrable x y Prod.snd measurable_snd)]
  simp [unitShift]

lemma gridMismatch_integral_le {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    (∫ u, gridMismatch r z w u ∂squareShift) ≤ min 1 (2*‖z-w‖/r) := by
  apply le_min
  · calc
      _ ≤ ∫ _u, (1:ℝ) ∂squareShift := integral_mono
        (gridMismatch_integrable r z w) (integrable_const _) (by
          intro u; unfold gridMismatch; split <;> norm_num)
      _ = 1 := by simp
  · have h := integral_mono (gridMismatch_integrable r z w)
      ((coordinate_mismatch_integrable (z.re/r) (w.re/r) Prod.fst measurable_fst).add
      (coordinate_mismatch_integrable (z.im/r) (w.im/r) Prod.snd measurable_snd))
      (gridMismatch_le_coordinates r z w)
    have he := integral_add
      (coordinate_mismatch_integrable (z.re/r) (w.re/r) Prod.fst measurable_fst)
      (coordinate_mismatch_integrable (z.im/r) (w.im/r) Prod.snd measurable_snd)
    dsimp only [Pi.add_apply] at h he
    rw [he,integral_mismatch_fst,integral_mismatch_snd] at h
    calc
      _ ≤ |z.re/r-w.re/r| + |z.im/r-w.im/r| := h.trans
        (add_le_add (mismatch_integral_le_abs _ _) (mismatch_integral_le_abs _ _))
      _ = (|(z-w).re|+|(z-w).im|)/r := by
        rw [← sub_div,← sub_div,abs_div,abs_div,abs_of_pos hr,← add_div]
        rfl
      _ ≤ (‖z-w‖+‖z-w‖)/r := div_le_div_of_nonneg_right
        (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)) hr.le
      _ = _ := by ring

lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x-y| < 1 := by
  have hx₁ := Int.floor_le x
  have hx₂ := Int.lt_floor_add_one x
  have hy₁ := Int.floor_le y
  have hy₂ := Int.lt_floor_add_one y
  rw [← h] at hy₁ hy₂
  rw [abs_lt]
  constructor <;> linarith

lemma norm_le_of_same_grid {r : ℝ} (hr : 0 < r) {z w : ℂ} {u : ℝ × ℝ}
    (h : gridLabel r z u = gridLabel r w u) : ‖z-w‖ ≤ 2*r := by
  have hx := abs_sub_lt_one_of_floor_eq (congrArg Prod.fst h)
  have hy := abs_sub_lt_one_of_floor_eq (congrArg Prod.snd h)
  rw [add_sub_add_right_eq_sub,← sub_div,abs_div,abs_of_pos hr,div_lt_one hr] at hx hy
  calc
    _ ≤ |(z-w).re|+|(z-w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ r+r := add_le_add hx.le hy.le
    _ = 2*r := by ring

end
end PlanarUnitDistances.GridShift

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_States
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.StateConsistency
open MeasureTheory Set Real
open PlanarUnitDistances.GridShift
noncomputable section

lemma error_bounds (n s : ℝ) (z z' w w' : ℂ) (u : Shifts) :
    0 ≤ error n s z z' w w' u ∧ error n s z z' w w' u ≤ 1 := by
  unfold error; split <;> norm_num

lemma measurable_consistent (n : ℝ) (z z' w w' : ℂ) :
    MeasurableSet {x : ℝ × Shifts | consistent n x.1 z z' w w' x.2} := by
  have h (a : ℂ) (negate : Bool) (first : Bool) :
      Measurable (fun x : ℝ × Shifts =>
        gridLabel (exp (if negate then -x.1 else x.1)) a (if first then x.2.1 else x.2.2)) := by
    cases negate <;> cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true, gridLabel] <;> fun_prop
  unfold consistent
  have hA := measurableSet_eq_fun (h z true true) (h z' true true)
  have hB := measurableSet_eq_fun (h w false false) (h w' false false)
  simp only [Bool.false_eq_true,ite_true,ite_false] at hA hB
  convert MeasurableSet.ite (measurableSet_lt measurable_fst (measurable_const (a := n)))
    (hA.inter hB.compl) (hA.compl.inter hB) using 1
  ext x
  by_cases hs : x.1 < n <;> simp [Set.ite,hs]

lemma measurable_error (n : ℝ) (z z' w w' : ℂ) :
    Measurable (fun x : ℝ × Shifts => error n x.1 z z' w w' x.2) :=
  Measurable.ite (measurable_consistent n z z' w w') measurable_const measurable_const

lemma integrable_error (n s : ℝ) (z z' w w' : ℂ) :
    Integrable (error n s z z' w w') shiftLaw := by
  apply Integrable.of_bound ((measurable_error n z z' w w').comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  filter_upwards [] with u
  change ‖error n s z z' w w' u‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (error_bounds n s z z' w w' u).1]
  exact (error_bounds n s z z' w w' u).2

lemma short_jump_z {n s : ℝ} {z z' : ℂ} (hz : ‖z-z'‖ = exp (-n)) :
    2*‖z-z'‖/exp (-s) = 2*exp (s-n) := by
  calc
    _ = 2*(exp (-n)/exp (-s)) := by rw [hz]; ring
    _ = 2*exp ((-n)-(-s)) := by rw [exp_sub]
    _ = _ := by congr 2; ring

lemma short_jump_w {n s : ℝ} {w w' : ℂ} (hw : ‖w-w'‖ = exp n) :
    2*‖w-w'‖/exp s = 2*exp (n-s) := by
  rw [hw,exp_sub]; ring

lemma long_jump_z {n s : ℝ} {z z' : ℂ} (hz : ‖z-z'‖ = exp (-n))
    (h : log 2 < s-n) (u : ℝ × ℝ) :
    gridLabel (exp (-s)) z u ≠ gridLabel (exp (-s)) z' u := by
  intro he
  have hb := norm_le_of_same_grid (exp_pos (-s)) he
  have hl : 2 < exp (s-n) := by
    simpa only [exp_log (by norm_num : (0:ℝ) < 2)] using exp_lt_exp.mpr h
  have hd := short_jump_z hz (s := s)
  have : 2*‖z-z'‖ / exp (-s) ≤ 4 := by
    rw [div_le_iff₀ (exp_pos (-s))]
    nlinarith
  linarith

lemma long_jump_w {n s : ℝ} {w w' : ℂ} (hw : ‖w-w'‖ = exp n)
    (h : log 2 < n-s) (u : ℝ × ℝ) :
    gridLabel (exp s) w u ≠ gridLabel (exp s) w' u := by
  intro he
  have hb := norm_le_of_same_grid (exp_pos s) he
  have hl : 2 < exp (n-s) := by simpa only [exp_log (by norm_num : (0:ℝ) < 2)] using exp_lt_exp.mpr h
  have hd := short_jump_w hw (s := s)
  have : 2*‖w-w'‖ / exp s ≤ 4 := by
    rw [div_le_iff₀ (exp_pos s)]
    nlinarith
  linarith

lemma pointwise_short {n s : ℝ} {z z' w w' : ℂ}
    (hz : ‖z-z'‖ = exp (-n)) (hw : ‖w-w'‖ = exp n)
    (hfar : log 2 < |s-n|) (u : Shifts) :
    error n s z z' w w' u =
      if s < n then gridMismatch (exp (-s)) z z' u.1
      else gridMismatch (exp s) w w' u.2 := by
  by_cases hs : s < n
  · have hw' := long_jump_w hw (by simpa [abs_of_neg (sub_neg.mpr hs)] using hfar) u.2
    simp [error,consistent,hs,hw',gridMismatch]
  · have hz' := long_jump_z hz (by simpa [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hs))] using hfar) u.1
    simp [error,consistent,hs,hz',gridMismatch]

theorem expected_error_le {n s : ℝ} {z z' w w' : ℂ}
    (hz : ‖z-z'‖ = exp (-n)) (hw : ‖w-w'‖ = exp n) :
    (∫ u, error n s z z' w w' u ∂shiftLaw) ≤
      (if |s-n| ≤ log 2 then (1:ℝ) else 0)+2*exp (-|s-n|) := by
  by_cases h : |s-n| ≤ log 2
  · calc
      _ ≤ ∫ _u : Shifts, (1:ℝ) ∂shiftLaw := integral_mono (integrable_error ..)
        (integrable_const _) (fun u => (error_bounds ..).2)
      _ ≤ _ := by simp only [integral_const,probReal_univ,one_smul,ite_eq_left h]; linarith [exp_pos (-|s-n|)]
  · simp only [ite_eq_right h,zero_add]
    simp_rw [pointwise_short hz hw (lt_of_not_ge h)]
    by_cases hs : s < n
    · simp only [ite_eq_left hs]
      rw [shiftLaw,integral_fun_fst]
      simp only [probReal_univ,one_smul]
      exact (gridMismatch_integral_le (exp_pos (-s)) z z').trans <| by
        rw [short_jump_z hz]
        simp [abs_of_neg (sub_neg.mpr hs)]
    · simp only [ite_eq_right hs]
      rw [shiftLaw,integral_fun_snd]
      simp only [probReal_univ,one_smul]
      exact (gridMismatch_integral_le (exp_pos s) w w').trans <| by
        rw [short_jump_w hw]
        simp [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hs))]

lemma exp_abs_integrable : Integrable (fun s : ℝ => exp (-|s|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ))]
  apply IntegrableOn.union
  · apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
    intro x hx
    simp only [mem_Iic] at hx
    simp [abs_of_nonpos (show x ≤ 0 from hx)]
  · apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
    intro x hx
    simp [abs_of_pos (show 0 < x from hx)]

lemma exp_abs_integral : (∫ s : ℝ, exp (-|s|)) = 2 := by
  have h₁ := exp_abs_integrable.integrableOn (s := Iic 0)
  have h₂ := exp_abs_integrable.integrableOn (s := Ioi 0)
  calc
    _ = ∫ s in Iic (0:ℝ) ∪ Ioi 0, exp (-|s|) := by rw [Iic_union_Ioi,Measure.restrict_univ]
    _ = (∫ s in Iic (0:ℝ), exp (-|s|)) + ∫ s in Ioi (0:ℝ), exp (-|s|) :=
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi h₁ h₂
    _ = (∫ s in Iic (0:ℝ), exp s) + ∫ s in Ioi (0:ℝ), exp (-s) := by
      congr 1
      · apply setIntegral_congr_fun measurableSet_Iic
        intro x hx; simp [abs_of_nonpos (show x ≤ 0 from hx)]
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx; simp [abs_of_pos (show 0 < x from hx)]
    _ = 2 := by rw [integral_exp_Iic_zero,integral_exp_neg_Ioi_zero]; norm_num

lemma envelope_eq (n s : ℝ) : envelope n s =
    (if |s-n| ≤ log 2 then (1:ℝ) else 0)+2*exp (-|s-n|) := by
  have he : |s-n| ≤ log 2 ↔ s ∈ Icc (n-log 2) (n+log 2) := by
    rw [abs_le,mem_Icc]; constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp only [envelope,Set.indicator_apply,he]

lemma envelope_nonneg (n s : ℝ) : 0 ≤ envelope n s := by
  rw [envelope_eq]; split <;> positivity

lemma envelope_integrable (n : ℝ) : Integrable (envelope n) := by
  apply Integrable.add
  · exact ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).integrable_indicator measurableSet_Icc
  · exact (exp_abs_integrable.comp_sub_right n).const_mul 2

lemma envelope_integral (n : ℝ) : (∫ s : ℝ, envelope n s) = 2*log 2+4 := by
  have h₁ : Integrable ((Icc (n-log 2) (n+log 2)).indicator (fun _ => (1:ℝ))) :=
    ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).integrable_indicator measurableSet_Icc
  simp only [envelope]
  rw [integral_add h₁ ((exp_abs_integrable.comp_sub_right n).const_mul 2),
    integral_indicator_const 1 measurableSet_Icc,integral_const_mul]
  have he : (∫ s : ℝ, exp (-|s-n|)) = 2 := by
    simpa only [sub_eq_add_neg] using (integral_add_right_eq_self (fun s : ℝ => exp (-|s|)) (-n)).trans exp_abs_integral
  rw [he]
  have hp : (0:ℝ) ≤ log 2 := log_nonneg (by norm_num)
  simp [Real.volume_real_Icc,show n+log 2-(n-log 2) = 2*log 2 by ring,max_eq_left (by positivity : 0 ≤ 2*log 2)]; norm_num

lemma product_error_integrable (n l r : ℝ) (z z' w w' : ℂ) :
    Integrable (fun x : ℝ × Shifts => error n x.1 z z' w w' x.2)
      ((volume.restrict (Icc l r)).prod shiftLaw) := by
  apply Integrable.of_bound (measurable_error n z z' w w').aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (error_bounds ..).1]
  exact (error_bounds ..).2

theorem mean_integrated_error_le {n l r : ℝ} {z z' w w' : ℂ}
    (hz : ‖z-z'‖ = exp (-n)) (hw : ‖w-w'‖ = exp n) :
    (∫ u, ∫ s in Icc l r, error n s z z' w w' u ∂volume ∂shiftLaw) ≤ 2*log 2+4 := by
  rw [← integral_integral_swap (product_error_integrable n l r z z' w w')]
  calc
    _ ≤ ∫ s in Icc l r, envelope n s := integral_mono
      (product_error_integrable n l r z z' w w').integral_prod_left
      (envelope_integrable n).integrableOn (fun s => by rw [envelope_eq]; exact expected_error_le hz hw)
    _ ≤ ∫ s : ℝ, envelope n s := integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (envelope_nonneg n)) (envelope_integrable n)
    _ = _ := envelope_integral n

lemma unit_norms {z z' w w' : ℂ} (h : (z-z')*(w-w')=1) :
    ‖z-z'‖ = exp (-(-log ‖z-z'‖)) ∧ ‖w-w'‖ = exp (-log ‖z-z'‖) := by
  have hz : z-z' ≠ 0 := by intro he; rw [he,zero_mul] at h; exact zero_ne_one h
  have hn : 0 < ‖z-z'‖ := norm_pos_iff.mpr hz
  have hh := congrArg norm h
  rw [norm_mul,norm_one] at hh
  constructor
  · rw [neg_neg,exp_log hn]
  · rw [exp_neg,exp_log hn]
    apply mul_left_cancel₀ (ne_of_gt hn)
    rw [hh,mul_inv_cancel₀ (ne_of_gt hn)]

variable {E : Type*} [Fintype E]

theorem exists_shifts (μ : E → ℝ) (hμ : ∀ e, 0 ≤ μ e) (hμ₁ : ∑ e, μ e = 1)
    (z z' w w' : E → ℂ) (hu : ∀ e, (z e-z' e)*(w e-w' e)=1) (l r : ℝ) :
    ∃ u : Shifts, (∑ e, μ e * ∫ s in Icc l r,
      error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u) ≤ 2*log 2+4 := by
  let F : Shifts → ℝ := fun u => ∑ e, μ e * ∫ s in Icc l r,
    error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u
  have hi (e : E) : Integrable (fun u => ∫ s in Icc l r,
      error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u) shiftLaw :=
    (product_error_integrable _ _ _ _ _ _ _).integral_prod_right
  have hf : Integrable F shiftLaw :=
    integrable_finsetSum _ (fun e _ => (hi e).const_mul (μ e))
  obtain ⟨u,hu'⟩ := exists_le_integral hf
  refine ⟨u,hu'.trans ?_⟩
  change (∫ u, (∑ e, μ e * (∫ s in Icc l r,
    error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u)) ∂shiftLaw) ≤ _
  rw [integral_finsetSum _ (fun e _ => (hi e).const_mul (μ e))]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ e, μ e*(2*log 2+4) := Finset.sum_le_sum (fun e _ =>
      mul_le_mul_of_nonneg_left (mean_integrated_error_le (unit_norms (hu e)).1 (unit_norms (hu e)).2) (hμ e))
    _ = _ := by rw [← Finset.sum_mul,hμ₁,one_mul]

lemma gridLabel_fract_eq_iff (r : ℝ) (z z' : ℂ) (u : ℝ × ℝ) :
    gridLabel r z (Int.fract u.1, Int.fract u.2) =
      gridLabel r z' (Int.fract u.1, Int.fract u.2) ↔
    gridLabel r z u = gridLabel r z' u := by
  have h (x a : ℝ) : ⌊x+Int.fract a⌋ = ⌊x+a⌋-⌊a⌋ := by
    rw [Int.fract,← add_sub_assoc,Int.floor_sub_intCast]
  simp only [gridLabel,Prod.mk.injEq,h,sub_left_inj]

lemma error_fractionalShifts (n s : ℝ) (z z' w w' : ℂ) (u : Shifts) :
    error n s z z' w w' (fractionalShifts u) = error n s z z' w w' u := by
  classical
  simp only [error,consistent,fractionalShifts,ne_eq,gridLabel_fract_eq_iff]

theorem exists_fractionalShifts (μ : E → ℝ) (hμ : ∀ e, 0 ≤ μ e)
    (hμ₁ : ∑ e, μ e = 1) (z z' w w' : E → ℂ)
    (hu : ∀ e, (z e-z' e)*(w e-w' e)=1) (l r : ℝ) :
    ∃ u : Shifts, Fractional u ∧ (∑ e, μ e * ∫ s in Icc l r,
      error (-log ‖z e-z' e‖) s (z e) (z' e) (w e) (w' e) u) ≤ 2*log 2+4 := by
  obtain ⟨u,hu'⟩ := exists_shifts μ hμ hμ₁ z z' w w' hu l r
  refine ⟨fractionalShifts u,?_,?_⟩
  · exact ⟨⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,
      ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,
      ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,
      ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩⟩
  · simpa only [error_fractionalShifts] using hu'

lemma nonarch_unit_scales {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {z z' w w' : K} (h : (z-z')*(w-w')=1) :
    v (z-z') = exp (-(-log (v (z-z')))) ∧ v (w-w') = exp (-log (v (z-z'))) := by
  have hz : z-z' ≠ 0 := by intro he; rw [he,zero_mul] at h; exact zero_ne_one h
  have hn : 0 < v (z-z') := v.pos hz
  have hh := congrArg v h
  rw [v.map_mul,v.map_one] at hh
  constructor
  · rw [neg_neg,exp_log hn]
  · rw [exp_neg,exp_log hn]
    apply mul_left_cancel₀ (ne_of_gt hn)
    rw [hh,mul_inv_cancel₀ (ne_of_gt hn)]

theorem nonarch_consistent_off_boundary {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {z z' w w' : K}
    (hu : (z-z')*(w-w')=1) {s : ℝ} (hs : s ≠ -log (v (z-z'))) :
    nonarchConsistent v hv (-log (v (z-z'))) s z z' w w' := by
  obtain ⟨hz,hw⟩ := nonarch_unit_scales v hu
  unfold nonarchConsistent
  split_ifs with hsn
  · constructor
    · rw [Quotient.eq]
      change v (z-z') ≤ exp (-s)
      rw [hz,exp_le_exp]; linarith
    · rw [ne_eq,Quotient.eq]
      change ¬v (w-w') ≤ exp s
      rw [hw,not_le,exp_lt_exp]; exact hsn
  · constructor
    · rw [ne_eq,Quotient.eq]
      change ¬v (z-z') ≤ exp (-s)
      rw [hz,not_le,exp_lt_exp]
      exact neg_lt_neg (lt_of_le_of_ne (le_of_not_gt hsn) (Ne.symm hs))
    · rw [Quotient.eq]
      change v (w-w') ≤ exp s
      rw [hw,exp_le_exp]; exact le_of_not_gt hsn

end
end PlanarUnitDistances.StateConsistency

namespace PlanarUnitDistances.FiniteStates
open MeasureTheory Set Real
open scoped Classical
noncomputable section
variable {V : Type*}

lemma label_eq_iff (r : Setoid V) (x y : V) : label r x=label r y ↔ r.r x y := by
  constructor
  · intro he
    have hh := congrFun he y
    simpa only [label,r.refl y,decide_true,decide_eq_true_eq] using hh
  · intro h
    funext z
    apply Bool.decide_congr
    exact ⟨fun hx => r.trans (r.symm h) hx,fun hy => r.trans h hy⟩

lemma archState_consistent_iff (z w : V → ℂ) (u : StateConsistency.Shifts) (s n : ℝ) (x y : V) :
    CrossStructure.Consistent (decide (s<n)) (archState z w u s x) (archState z w u s y) ↔
      StateConsistency.consistent n s (z x) (z y) (w x) (w y) u := by
  unfold CrossStructure.Consistent StateConsistency.consistent archState
  simp only [label_eq_iff,archRel,Setoid.ker_def]
  by_cases hs : s<n <;> simp [hs,label_eq_iff,Setoid.ker_def]

lemma finiteState_consistent {K : Type*} [Field K] (z w : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) {x y : V} (hu : (z x-z y)*(w x-w y)=1)
    {s : ℝ} (hs : s≠-log (v (z x-z y))) :
    CrossStructure.Consistent (decide (s< -log (v (z x-z y))))
      (finiteState z w v hv s x) (finiteState z w v hv s y) := by
  have hc := StateConsistency.nonarch_consistent_off_boundary v hv hu hs
  unfold CrossStructure.Consistent finiteState
  simp only [label_eq_iff,finiteRel,Setoid.comap_rel,StateConsistency.localSetoid]
  unfold StateConsistency.nonarchConsistent at hc
  split_ifs at hc with h
  · simp only [h,decide_true,↓reduceIte,ne_eq,label_eq_iff]
    exact ⟨Quotient.exact hc.1,fun he => hc.2 (Quotient.sound he)⟩
  · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte,ne_eq,label_eq_iff]
    exact ⟨fun he => hc.1 (Quotient.sound he),Quotient.exact hc.2⟩
end
end PlanarUnitDistances.FiniteStates

namespace PlanarUnitDistances.FiniteLevels
open MeasureTheory Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSingletonClass J] in
lemma integral_eq (weight : ℝ≥0) (l u : J → ℝ) (f : J × ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀x, |f x| ≤ M) :
    (∫x, f x ∂measure weight l u) =
      (weight : ℝ) * ∑ j, ∫ s in Icc (l j) (u j), f (j,s) := by
  have hm (j : J) : Measurable (fun s : ℝ => (j,s)) :=
    measurable_const.prodMk measurable_id
  have hi (j : J) : Integrable f
      (Measure.map (fun s : ℝ => (j,s)) (volume.restrict (Icc (l j) (u j)))) := by
    apply Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x
  unfold measure
  rw [integral_finsetSum_measure (fun j _ => (hi j).smul_measure_nnreal (c := weight))]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact integral_map (hm j).aemeasurable hf.aestronglyMeasurable

end
end PlanarUnitDistances.FiniteLevels

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LevelStates
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels FiniteStates CrossStructure
open scoped Classical NNReal ENNReal
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

omit [Fintype E] in
lemma edgeError_measurable (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (e : E) :
    Measurable (fun a => edgeError S z w src tgt u a e) := by
  exact (measurable_of_finite (fun bxy : Bool × ((V→Bool)×(V→Bool)) × ((V→Bool)×(V→Bool)) =>
    if Consistent bxy.1 bxy.2.1 bxy.2.2 then (0:ℝ) else 1)).comp
    ((bit_measurable S z src tgt e).prodMk
      ((state_measurable S z w u (src e)).prodMk (state_measurable S z w u (tgt e))))
omit [Fintype V] [Fintype E] in
lemma edgeError_bounds (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) (e : E) :
    0≤edgeError S z w src tgt u a e ∧ edgeError S z w src tgt u a e≤1 := by
  unfold edgeError; split_ifs <;> norm_num

lemma meanError_measurable (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) : Measurable (meanError μ S z w src tgt u) := by
  exact Finset.measurable_sum _ (fun e _ => measurable_const.mul (edgeError_measurable S z w src tgt u e))
omit [Fintype V] in
lemma meanError_bounds (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) :
    0 ≤ meanError μ S z w src tgt u a ∧ meanError μ S z w src tgt u a≤1 := by
  constructor
  · exact avg_nonneg μ (fun e => (edgeError_bounds S z w src tgt u a e).1)
  · exact (avg_mono μ (fun e => (edgeError_bounds S z w src tgt u a e).2)).trans_eq (avg_const _ _)

omit [Fintype V] [Fintype E] in
lemma edgeError_arch (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (σ : K →ₐ[ℚ] ℂ) (s : ℝ) (e : E) :
    edgeError S z w src tgt u (.inl σ,s) e =
      StateConsistency.error (-log ‖σ (z (src e))-σ (z (tgt e))‖) s
        (σ (z (src e))) (σ (z (tgt e))) (σ (w (src e))) (σ (w (tgt e))) (u σ) := by
  simp only [edgeError,bit,state,av,WeightedAbsoluteValues.infiniteEntry_apply,map_sub,
    archState_consistent_iff,StateConsistency.error]

omit [Fintype V] [Fintype E] in
lemma edgeError_finite_ae (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : ↥(finiteSupport K S))
    (e : E) (hu : (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1) :
    (fun s => edgeError S z w src tgt u (.inr v,s) e) =ᵐ[volume] 0 := by
  filter_upwards [volume.ae_ne (-log (WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2
    (z (src e)-z (tgt e))))] with s hs
  have hc := finiteState_consistent z w _
    (WeightedAbsoluteValues.finiteEntry_nonarch K v.val.1 v.val.2) hu hs
  exact ite_eq_left hc

lemma integral_meanError (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (l r : ℝ) :
    (∫s in Icc l r,meanError μ S z w src tgt u (v,s)) =
      ∑e,μ.val e*∫s in Icc l r,edgeError S z w src tgt u (v,s) e := by
  have hi (e : E) : Integrable (fun s => edgeError S z w src tgt u (v,s) e)
      (volume.restrict (Icc l r)) := by
    apply Integrable.mono' (integrable_const (1:ℝ))
      ((edgeError_measurable S z w src tgt u e).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s => by
      change ‖edgeError S z w src tgt u (v,s) e‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (edgeError_bounds S z w src tgt u (v,s) e).1]
      exact (edgeError_bounds S z w src tgt u (v,s) e).2
  unfold meanError avg
  rw [integral_finsetSum _ (fun e _ => (hi e).const_mul (μ.val e))]
  simp only [integral_const_mul]

theorem exists_bounded_states (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (hu : ∀e,(z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1) :
    ∃u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts,
      (∀σ,StateConsistency.Fractional (u σ)) ∧
      (∫a,meanError μ S z w src tgt u a ∂FiniteLevels.measure
        (⟨(Module.finrank ℚ K : ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩ : ℝ≥0)
        (fun v => -radius K S v) (radius K S)) ≤ 2*log 2+4 := by
  have hh (σ : K →ₐ[ℚ] ℂ) := StateConsistency.exists_fractionalShifts μ.val μ.nonneg μ.total
    (fun e => σ (z (src e))) (fun e => σ (z (tgt e)))
    (fun e => σ (w (src e))) (fun e => σ (w (tgt e)))
    (fun e => by simpa only [map_mul,map_sub,map_one] using congrArg σ (hu e))
    (-radius K S (.inl σ)) (radius K S (.inl σ))
  choose u hf hb using hh
  refine ⟨u,hf,?_⟩
  refine (FiniteLevels.integral_eq (J := Place K S)
    (⟨(Module.finrank ℚ K : ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩ : ℝ≥0)
    (fun v => -radius K S v) (radius K S) _ (meanError_measurable μ S z w src tgt u) 1
    (fun a => by
      rw [abs_of_nonneg (meanError_bounds μ S z w src tgt u a).1]
      exact (meanError_bounds μ S z w src tgt u a).2)).trans_le ?_
  have hv (v : ↥(finiteSupport K S)) : (∫s in Icc (-radius K S (.inr v)) (radius K S (.inr v)),
      meanError μ S z w src tgt u (.inr v,s))=0 := by
    rw [integral_meanError]
    apply sum_eq_zero
    intro e _
    rw [integral_congr_ae (ae_restrict_of_ae (edgeError_finite_ae S z w src tgt u v e (hu e)))]
    simp only [Pi.zero_apply,integral_zero,mul_zero]
  change (Module.finrank ℚ K:ℝ)⁻¹ * (∑v : (K →ₐ[ℚ] ℂ) ⊕ ↥(finiteSupport K S),_)≤_
  rw [Fintype.sum_sum_type]
  simp only [hv,sum_const_zero,add_zero]
  have hm := sum_le_sum (s:=univ) (fun σ _ => hb σ)
  simp only [sum_const,card_univ,nsmul_eq_mul,WeightedAbsoluteValues.infiniteEntry_count] at hm
  have harch (σ : K →ₐ[ℚ] ℂ) := integral_meanError μ S z w src tgt u (.inl σ)
    (-radius K S (.inl σ)) (radius K S (.inl σ))
  simp only [edgeError_arch] at harch
  simp_rw [harch]
  have hd : 0<(Module.finrank ℚ K:ℝ) := by exact_mod_cast (Module.finrank_pos : 0<Module.finrank ℚ K)
  calc
    _ ≤ (Module.finrank ℚ K:ℝ)⁻¹*((Module.finrank ℚ K:ℝ)*(2*log 2+4)) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hd.le)
    _ = _ := by field_simp
end
end PlanarUnitDistances.LevelStates

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma bit_nonneg (a s : ℝ) : 0 ≤ bit a s := by unfold bit; split <;> norm_num
lemma bit_le_one (a s : ℝ) : bit a s ≤ 1 := by unfold bit; split <;> norm_num

variable {E : Type*} [Fintype E]

lemma frequency_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (a : E → ℝ) (s : ℝ) :
    0 ≤ frequency p a s := Finset.sum_nonneg fun e _ => mul_nonneg (hp e) (bit_nonneg _ _)

lemma frequency_le_one (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) : frequency p a s ≤ 1 := by
  unfold frequency
  calc
    _ ≤ ∑ e, p e := Finset.sum_le_sum fun e _ => mul_le_of_le_one_right (hp e) (bit_le_one _ _)
    _ = 1 := hs

end
end PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.LevelScale
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels
open scoped Classical NNReal
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [Fintype E]

lemma prob_bounds (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) :
    0 ≤ prob μ S d a ∧ prob μ S d a ≤ 1 :=
  ⟨ThresholdProfiles.frequency_nonneg _ μ.nonneg _ _,
   ThresholdProfiles.frequency_le_one _ μ.nonneg μ.total _ _⟩
lemma minority_bounds (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) :
    0 ≤ minority μ S d a ∧ minority μ S d a ≤ 1 := by
  have h := prob_bounds μ S d a
  unfold minority
  exact ⟨le_min h.1 (sub_nonneg.mpr h.2),(min_le_left _ _).trans h.2⟩
end
end PlanarUnitDistances.LevelScale

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]

lemma support_avg (μ : Law X) (f : X → ℝ) : avg (support μ) (fun x => f x.val)=avg μ f := by
  change (∑x : {x : X // 0<μ.val x},μ.val x.val*f x.val) = ∑x,μ.val x*f x
  rw [←sum_subtype (univ.filter (fun x => 0<μ.val x)) (fun x => by simp) (fun x => μ.val x*f x),sum_filter]
  apply sum_congr rfl
  intro x _
  split_ifs with hx
  · rfl
  · rw [le_antisymm (le_of_not_gt hx) (μ.nonneg x),zero_mul]
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Predictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset MeasureTheory
open scoped Classical
noncomputable section
variable {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C]

lemma uniform_avg [Nonempty X] (f : X → ℝ) :
    avg (uniform X) f = (∑ x, f x) / Fintype.card X := by
  simp [avg,uniform,div_eq_mul_inv,mul_comm,sum_mul]

lemma uniform_equiv [Nonempty X] [Nonempty Y] (e : X ≃ Y) (f : Y → ℝ) :
    avg (uniform X) (fun x => f (e x)) = avg (uniform Y) f := by
  rw [uniform_avg,uniform_avg,e.sum_comp,Fintype.card_congr e]

lemma uniform_pair [Nonempty X] [Nonempty Y] (f : X×Y → ℝ) :
    avg (uniform (X×Y)) f = avg (uniform X) (fun x => avg (uniform Y) (fun y => f (x,y))) := by
  simp only [uniform_avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← sum_div,div_div]
  ring

omit [Fintype Y] in
lemma uniform_eval [DecidableEq X] [Nonempty C] (x : X) (f : C → ℝ) :
    avg (uniform (X → C)) (fun h => f (h x)) = avg (uniform C) f := by
  classical
  let e := Equiv.piSplitAt x (fun _ => C)
  have h := uniform_equiv e (fun z => f z.1)
  change avg (uniform (X → C)) (fun h => f (h x)) = _ at h
  rw [h, uniform_pair]
  simp_rw [avg_const]

omit [Fintype Y] in
lemma uniform_eval_two [DecidableEq X] [Nonempty C] (x y : X) (hxy : x ≠ y) (f : C → C → ℝ) :
    avg (uniform (X → C)) (fun h => f (h x) (h y)) =
      avg (uniform C) (fun a => avg (uniform C) (fun b => f a b)) := by
  classical
  let e := Equiv.piSplitAt x (fun _ => C)
  let y' : {z : X // z ≠ x} := ⟨y,hxy.symm⟩
  have h := uniform_equiv e (fun z => f z.1 (z.2 y'))
  change avg (uniform (X → C)) (fun h => f (h x) (h y)) = _ at h
  rw [h,uniform_pair]
  apply avg_congr
  intro a
  exact uniform_eval y' (f a)

omit [Fintype Y] in
lemma uniform_collision [DecidableEq X] [Nonempty C] (x y : X) (hxy : x ≠ y) :
    event (uniform (X → C)) (fun h => h x=h y) = (Fintype.card C : ℝ)⁻¹ := by
  unfold event
  have he := uniform_eval_two x y hxy (fun a b : C => if a=b then 1 else 0)
  rw [he]
  have h : ∀ a : C, avg (uniform C) (fun b => if a=b then 1 else 0) =
      (Fintype.card C : ℝ)⁻¹ := by
    intro a
    simp [uniform_avg]
  simp_rw [h]
  exact avg_const _ _

lemma integral_pmf [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Law X) (f : X → ℝ) :
    (∫ x,f x ∂μ.pmf.toMeasure) = avg μ f := by
  rw [PMF.integral_eq_sum]
  simp [avg,μ.nonneg]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.HashFeatures
open Finset Real
open scoped RealInnerProductSpace Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

lemma single_inner {T : Type*} [Fintype T] [DecidableEq T] (x y : T) (a b : ℝ) :
    (∑ i, Pi.single y b i * Pi.single x a i) = if x=y then a*b else 0 := by
  simp only [Pi.single_apply,ite_mul,mul_ite,zero_mul,mul_zero]
  by_cases h : x=y
  · subst y; simp [mul_comm]
  · simp [h]

lemma inner_vector (x y : A×B) (a b c d e f : ℝ) :
    inner ℝ (vector x a b c) (vector y d e f) =
      (if x.1=y.1 then a*d else 0)+(if x.2=y.2 then b*e else 0)+
      (if x=y then c*f else 0) := by
  classical
  rw [PiLp.inner_apply]
  simp only [vector,WithLp.ofLp_toLp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    RCLike.inner_apply,conj_trivial]
  rw [single_inner,single_inner,single_inner]
  ring

lemma norm_vector_sq (x : A×B) (a b c : ℝ) : ‖vector x a b c‖^2 = a^2+b^2+c^2 := by
  rw [← real_inner_self_eq_norm_sq,inner_vector]
  simp only [ite_true]
  ring

lemma norm_feature (x : A×B) : ‖vector x 1 1 1‖=sqrt 3 := by
  have h := norm_vector_sq x 1 1 1
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith [norm_nonneg (vector x 1 1 1),sqrt_nonneg 3]
lemma norm_test (x : A×B) : ‖vector x 1 1 (-2)‖=sqrt 6 := by
  have h := norm_vector_sq x 1 1 (-2)
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  nlinarith [norm_nonneg (vector x 1 1 (-2)),sqrt_nonneg 6]

lemma strict_cross_inner (x y : A×B) :
    inner ℝ (vector x 1 1 1) (vector y 1 1 (-2)) =
      if (x.1=y.1 ∧ x.2≠y.2) ∨ (x.1≠y.1 ∧ x.2=y.2) then 1 else 0 := by
  classical
  rw [inner_vector]
  by_cases h₁ : x.1=y.1 <;> by_cases h₂ : x.2=y.2
  · have he : x=y := Prod.ext h₁ h₂
    subst y
    norm_num
  · have hn : x≠y := fun h => h₂ (congrArg Prod.snd h)
    simp [h₁,h₂,hn]
  · have hn : x≠y := fun h => h₁ (congrArg Prod.fst h)
    simp [h₁,h₂,hn]
  · have hn : x≠y := fun h => h₁ (congrArg Prod.fst h)
    simp [h₁,h₂,hn]

lemma prediction_constant : 4*sqrt 3*sqrt 6 < (18:ℝ) := by
  have h₁ := sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h₂ := sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have hp : (4*sqrt 3*sqrt 6)^2 = 288 := by rw [mul_pow,mul_pow,h₁,h₂]; norm_num
  have hn : 0 ≤ 4*sqrt 3*sqrt 6 := by positivity
  nlinarith
end
end PlanarUnitDistances.HashFeatures

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma avg_comm (μ : Law X) (ν : Law Y) (f : X → Y → ℝ) :
    avg μ (fun x => avg ν (f x)) = avg ν (fun y => avg μ (fun x => f x y)) := by
  simp only [avg,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring
lemma abs_avg_le (μ : Law X) (f : X → ℝ) : |avg μ f| ≤ avg μ (fun x => |f x|) := by
  calc
    _ ≤ ∑ x,|μ.val x*f x| := abs_sum_le_sum_abs _ _
    _ = _ := by simp [avg,abs_mul,abs_of_nonneg,μ.nonneg]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.Hashing
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [Nonempty C]

omit [Fintype A] [Fintype B] [Fintype C] [Nonempty C] in
lemma error_pointwise (h : Hash A B C) (x y : A×B) :
    |indicator (state h x) (state h y) - indicator x y| ≤
      (if x.1≠y.1 ∧ h.1 x.1=h.1 y.1 then 1 else 0) +
      (if x.2≠y.2 ∧ h.2 x.2=h.2 y.2 then 1 else 0) := by
  unfold indicator Adj state
  dsimp only
  by_cases h₁ : x.1=y.1 <;> by_cases h₂ : x.2=y.2 <;>
    by_cases k₁ : h.1 x.1=h.1 y.1 <;> by_cases k₂ : h.2 x.2=h.2 y.2 <;>
      simp_all

lemma coord_error {D : Type*} [Fintype D] [DecidableEq D] (x y : D) :
    avg (uniform (D → C)) (fun h => if x≠y ∧ h x=h y then 1 else 0) ≤
      (Fintype.card C : ℝ)⁻¹ := by
  by_cases hxy : x=y
  · simp only [hxy,ne_eq,not_true_eq_false,false_and,ite_false,avg_const]
    positivity
  · simp only [hxy,ne_eq,not_false_eq_true,true_and]
    rw [avg_ite,uniform_collision x y hxy]

lemma error_bound (x y : A×B) :
    avg (law : Law (Hash A B C)) (fun h => |indicator (state h x) (state h y)-indicator x y|)
      ≤ 2/(Fintype.card C : ℝ) := by
  refine (avg_mono law (fun h => error_pointwise h x y)).trans ?_
  rw [avg_add]
  change avg (pair (uniform (A → C)) (uniform (B → C))) (fun h => if x.1≠y.1 ∧ h.1 x.1=h.1 y.1 then 1 else 0) +
    avg (pair (uniform (A → C)) (uniform (B → C))) (fun h => if x.2≠y.2 ∧ h.2 x.2=h.2 y.2 then 1 else 0) ≤ _
  rw [pair_fst (uniform (A → C)) (uniform (B → C))
    (fun h : A → C => if x.1≠y.1 ∧ h x.1=h y.1 then 1 else 0),
    pair_snd (uniform (A → C)) (uniform (B → C))
    (fun h : B → C => if x.2≠y.2 ∧ h x.2=h y.2 then 1 else 0)]
  have h₁ := coord_error (C := C) x.1 y.1
  have h₂ := coord_error (C := C) x.2 y.2
  linarith [show 2/(Fintype.card C : ℝ) = (Fintype.card C : ℝ)⁻¹+
      (Fintype.card C : ℝ)⁻¹ by ring]

lemma averaged_error (x y : A×B) :
    |avg (law : Law (Hash A B C)) (fun h => indicator (state h x) (state h y))-indicator x y|
      ≤ 2/(Fintype.card C : ℝ) := by
  rw [← avg_const (law : Law (Hash A B C)) (indicator x y),← avg_sub]
  exact (abs_avg_le law _).trans (error_bound x y)
end
end PlanarUnitDistances.Hashing

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

lemma abs_avg_sub_le (μ : Law X) {f g : X → ℝ} {c : ℝ} (h : ∀ x,|f x-g x| ≤ c) :
    |avg μ f-avg μ g| ≤ c := by
  rw [← avg_sub]
  exact (abs_avg_le μ _).trans (avg_le_const μ h)
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CrossPrediction
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q H A B C T : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype C] [Fintype T]
  [DecidableEq H] [DecidableEq A] [DecidableEq B] [Nonempty C]

omit [Fintype H] in
lemma push_mass (μ : Law P) (h : P → H) (a : H) :
    FiniteInformation.push μ.val h a = fiberMass μ h a := by
  rw [fiberMass_eq]
  unfold FiniteInformation.push
  apply sum_congr rfl
  intro x _
  split_ifs <;> rfl

omit [Fintype H] in
lemma posterior_cond (μ : Law P) (h : P → H) (p : P) (hp : 0 < μ.val p) (r : P) :
    FiniteInformation.posterior μ.val h (h p) r = (cond μ h (h p)).val r := by
  have hm : 0 < fiberMass μ h (h p) := hp.trans_le (atom_le_fiber μ h p)
  simp only [FiniteInformation.posterior,push_mass,FiniteLaw.cond,hm,↓reduceDIte]
  split_ifs <;> simp

lemma actual_hash_error (κ : Law Q) (w : Q → Law P) (X : P → A×B) (Z : Q → A×B) :
    |avg (Hashing.law : Law (Hashing.Hash A B C))
      (fun u => actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z))-actual κ w X Z|
      ≤ 2/(Fintype.card C : ℝ) := by
  unfold actual
  rw [avg_comm]
  simp_rw [avg_comm (Hashing.law : Law (Hashing.Hash A B C))]
  apply abs_avg_sub_le
  intro q
  apply abs_avg_sub_le
  intro p
  exact Hashing.averaged_error (X p) (Z q)

omit [Fintype H] [DecidableEq H] in
lemma predicted_hash_error (κ : Law Q) (w : Q → Law P) (h : P → H)
    (X : P → A×B) (Z : Q → A×B) :
    |avg (Hashing.law : Law (Hashing.Hash A B C))
      (fun u => predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z))-
          predicted κ w h X Z| ≤ 2/(Fintype.card C : ℝ) := by
  unfold predicted
  rw [avg_comm]
  simp_rw [avg_comm (Hashing.law : Law (Hashing.Hash A B C))]
  apply abs_avg_sub_le
  intro q
  apply abs_avg_sub_le
  intro p
  apply abs_avg_sub_le
  intro r
  exact Hashing.averaged_error (X r) (Z q)

lemma discrepancy_eq (κ : Law Q) (w : Q → Law P) (h : P → H)
    (hμ : ∀ p,0 < (mixture κ w).val p) (X : P → A×B) (Z : Q → A×B) :
    FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) h X
      (fun x => HashFeatures.vector x 1 1 1) (fun q => HashFeatures.vector (Z q) 1 1 (-2)) =
      |actual κ w X Z-predicted κ w h X Z| := by
  have hm : FiniteInformation.marginal κ.val (fun q => (w q).val) = (mixture κ w).val := rfl
  have hi : ∀ x y : A×B, inner ℝ (HashFeatures.vector x 1 1 1)
      (HashFeatures.vector y 1 1 (-2)) = Hashing.indicator x y := by
    intro x y
    rw [HashFeatures.strict_cross_inner]
    unfold Hashing.indicator StrictCross.Adj
    split_ifs <;> rfl
  unfold FiniteInformation.testDiscrepancy
  rw [hm]
  simp_rw [FiniteInformation.mean_posterior,posterior_cond _ _ _ (hμ _),sum_inner,
    real_inner_smul_left,inner_sub_left,sum_inner,real_inner_smul_left,
    hi]
  simp only [actual,predicted,avg]
  congr 1
  simp only [mul_sub,sum_sub_distrib]
omit [Fintype H] [DecidableEq H] in
lemma hash_transfer (κ : Law Q) (w : Q → Law P) (h : P → H)
    (X : P → A×B) (Z : Q → A×B) :
    actual κ w X Z-predicted κ w h X Z ≤
      avg (Hashing.law : Law (Hashing.Hash A B C)) (fun u =>
        |actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z)-
          predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z)|)+
        4/(Fintype.card C : ℝ) := by
  have ha := actual_hash_error (C := C) κ w X Z
  have hp := predicted_hash_error (C := C) κ w h X Z
  have he := avg_mono (Hashing.law : Law (Hashing.Hash A B C)) (fun u =>
    le_abs_self (actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z)-
      predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z)))
  rw [avg_sub] at he
  have ha' := (abs_le.mp ha).1
  have hp' := (abs_le.mp hp).2
  simp only [div_eq_mul_inv] at ha' hp' ⊢
  linarith

open MeasureTheory Real
lemma history_singleton (D : Type*) [MeasurableSpace D] [MeasurableSingletonClass D] (n : ℕ) :
    MeasurableSingletonClass (FiniteInformation.History D n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (MeasurableSingletonClass (FiniteInformation.History D n × D))

theorem exists_cross_history (κ : Law Q) (w : Q → Law P)
    (hμ : ∀ p,0 < (mixture κ w).val p) (τ : Law T)
    (X : T → P → A×B) (Z : T → Q → A×B) (K : ℕ) (hK : 0 < K) :
    ∃ n < K, ∃ h : P → FiniteInformation.History (C×C) n,
      (univ.image h).card ≤ (Fintype.card C)^(2*K) ∧
      avg τ (fun t => actual κ w (X t) (Z t)-predicted κ w h (X t) (Z t)) ≤
        4/(Fintype.card C : ℝ)+18*(FiniteInformation.KL
          (FiniteInformation.wedge κ.val (fun q => (w q).val))
          (fun pr : P×P => (mixture κ w).val pr.1 * (mixture κ w).val pr.2)/(K:ℝ))^(1/4:ℝ) := by
  classical
  let : MeasurableSpace (C×C) := ⊤
  let : MeasurableSpace (T × Hashing.Hash A B C) := ⊤
  let σ : Law (T × Hashing.Hash A B C) := pair τ Hashing.law
  let code := fun tu : T × Hashing.Hash A B C => Hashing.state tu.2 ∘ X tu.1
  let feature := fun _ : T × Hashing.Hash A B C => fun c : C×C => HashFeatures.vector c 1 1 1
  let test := fun tu : T × Hashing.Hash A B C => fun q =>
    HashFeatures.vector (Hashing.state tu.2 (Z tu.1 q)) 1 1 (-2)
  have hδ : ∀ n, Measurable (fun z : (P → FiniteInformation.History (C×C) n) ×
      (T × Hashing.Hash A B C) =>
      FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) z.1
        (code z.2) (feature z.2) (test z.2)) := by
    intro n
    let := history_singleton (C×C) n
    exact measurable_of_finite _
  obtain ⟨n,hn,h,hcard,hbound⟩ := FiniteInformation.exists_prediction_history
    (ν := σ.pmf.toMeasure) κ.val (fun q => (w q).val) κ.nonneg
    (fun q => (w q).nonneg) κ.total (fun q => (w q).total)
    code feature test (fun _ => measurable_of_finite _) hδ
    (sqrt_nonneg 3) (sqrt_nonneg 6)
    (fun _ c => (HashFeatures.norm_feature c).le)
    (fun tu q => (HashFeatures.norm_test (Hashing.state tu.2 (Z tu.1 q))).le) K hK
  refine ⟨n,hn,h,?_,?_⟩
  · refine hcard.trans ?_
    rw [Fintype.card_prod,← pow_two,← pow_mul]
    exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  · rw [integral_pmf,pair_avg] at hbound
    dsimp [code,feature,test] at hbound
    simp_rw [discrepancy_eq κ w h hμ] at hbound
    have he := avg_mono τ (fun t => hash_transfer (C := C) κ w h (X t) (Z t))
    rw [avg_add,avg_const] at he
    have hnD : 0 ≤ (FiniteInformation.KL
        (FiniteInformation.wedge κ.val (fun q => (w q).val))
        (fun pr : P×P => (mixture κ w).val pr.1 * (mixture κ w).val pr.2)/(K:ℝ))^(1/4:ℝ) :=
      rpow_nonneg (div_nonneg (FiniteInformation.KL_nonneg _ _
        (FiniteInformation.wedge_nonneg _ _ κ.nonneg (fun q => (w q).nonneg))
        (fun pr => mul_nonneg ((mixture κ w).nonneg pr.1) ((mixture κ w).nonneg pr.2))
        (FiniteInformation.wedge_sum _ _ κ.total (fun q => (w q).total))
        (by rw [Fintype.sum_prod_type,← sum_mul_sum,(mixture κ w).total,one_mul])
        (FiniteInformation.wedge_ac _ _ κ.nonneg (fun q => (w q).nonneg)))
        (Nat.cast_nonneg K)) _
    have hc := mul_le_mul_of_nonneg_right HashFeatures.prediction_constant.le hnD
    change _ ≤ 4*sqrt 3*sqrt 6*(_/(K:ℝ))^(1/4:ℝ) at hbound
    change _ ≤ 4*sqrt 3*sqrt 6*
      (FiniteInformation.KL (FiniteInformation.wedge κ.val (fun q => (w q).val))
        (fun pr : P×P => (mixture κ w).val pr.1*(mixture κ w).val pr.2)/(K:ℝ))^(1/4:ℝ) at hbound
    refine he.trans ?_
    rw [add_comm (4/(Fintype.card C : ℝ))]
    exact add_le_add_left (hbound.trans hc) _
end
end PlanarUnitDistances.CrossPrediction

namespace PlanarUnitDistances.FiniteLaw
open MeasureTheory Finset Set
open scoped Classical
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma fromMeasure_avg (μ : Measure S) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ) (f : S → ℝ) :
    avg (fromMeasure μ hμ) f=(∫s,f s ∂μ)/μ.real Set.univ := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [avg,fromMeasure,smul_eq_mul]
  rw [Finset.sum_div]
  apply sum_congr rfl; intro s _; ring

variable {Ω : Type*} [MeasurableSpace Ω]

lemma compress_avg (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ)
    (c : Ω → S) (hc : Measurable c) (f : S → ℝ) :
    avg (compress μ hμ c hc) f=(∫s,f (c s) ∂μ)/μ.real Set.univ := by
  rw [compress,fromMeasure_avg,map_real_univ μ c hc,
    integral_map hc.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scale
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LogHistory
open Filter
noncomputable section

lemma length_pos (M : ℕ) (t : ℝ) : 0<length M t := Nat.succ_pos _

end
end PlanarUnitDistances.LogHistory

namespace PlanarUnitDistances.IncidenceScale
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence
open scoped Classical
noncomputable section
variable (s : Sequence)
lemma positive (n : ℕ) (p : s.P n) : 0<(left (graph s n)).val p := by
  rw [graph,GeometricLaw.left_eq]
  exact div_pos ((s.good n).point_degree_pos p) (s.good n).positive
lemma support (n : ℕ) (p : s.P n) (q : s.Q n) (h : 0<(graph s n).val (p,q)) :
    GeometricLaw.E (s.P n) (s.Q n) p q := by
  change 0<IncidenceEntropy.indicator (GeometricLaw.E (s.P n) (s.Q n)) p q/_ at h
  by_contra hn
  simp [IncidenceEntropy.indicator,hn] at h
lemma information_eq (n : ℕ) : BoundedScaleFinite.information (graph s n)=
    IncidenceSequence.information (s.P n) (s.Q n) := by
  unfold BoundedScaleFinite.information IncidenceSequence.information
  rw [graph,GeometricLaw.wedge_eq _ _ _ ((s.good n).center_degree_pos)]
  simp only [GeometricLaw.graph,UniformGraphLaw.left_eq]
end
end PlanarUnitDistances.IncidenceScale

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_RareEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.RareMass
open FiniteLaw CrossStructure RareScore LevelScores
open scoped Classical
noncomputable section
variable {A B E : Type*} [Fintype E]

lemma coordinate_mismatch {D : Type*} (r b : Bool) (x y : D×D)
    (h : nonsharedCoord r x≠nonsharedCoord r y) : b=r ∨ ¬Consistent b x y := by
  cases r <;> cases b <;> simp_all [nonsharedCoord,Consistent]

lemma minority_mass (μ : Law E) (b : E → Bool) :
    event μ (fun e => b e=minority (event μ (fun e => b e=true)))=
      min (event μ (fun e => b e=true)) (1-event μ (fun e => b e=true)) := by
  let p := event μ (fun e => b e=true)
  have hcomp : event μ (fun e => b e=false)=1-p := by
    change _=1-event μ (fun e => b e=true)
    rw [←event_compl]
    apply avg_congr
    intro e
    cases b e <;> simp
  change event μ (fun e => b e=minority p)=min p (1-p)
  by_cases hp : p<1/2
  · rw [minority,show decide (p<1/2)=true from decide_eq_true hp,min_eq_left (by linarith)]
  · rw [minority,show decide (p<1/2)=false from decide_eq_false hp,hcomp,min_eq_right (by linarith)]

theorem minority_le_exceptions (μ : Law E) (b : E → Bool) (x y : E → A×B) (l : A×B) :
    let p := event μ (fun e => b e=true)
    min p (1-p) ≤ event μ (fun e => exceptional (minority p) l (x e))+
      event μ (fun e => exceptional (minority p) l (y e))+
      event μ (fun e => ¬Consistent (b e) (x e) (y e)) := by
  dsimp only
  rw [←minority_mass μ b]
  have h := event_mono μ (fun e (hb : b e=minority (event μ (fun e => b e=true))) =>
    show (exceptional (minority (event μ (fun e => b e=true))) l (x e) ∨
      exceptional (minority (event μ (fun e => b e=true))) l (y e)) ∨
      ¬Consistent (b e) (x e) (y e) from by
      by_cases hc : Consistent (b e) (x e) (y e)
      · exact Or.inl (minority_exception hc hb)
      · exact Or.inr hc)
  exact h.trans ((event_union_le μ _ _).trans (add_le_add (event_union_le μ _ _) le_rfl))

lemma mismatch_le_minority_error {D : Type*} (μ : Law E) (b : E → Bool) (x y : E → D×D) :
    let p := event μ (fun e => b e=true)
    event μ (fun e => nonsharedCoord (minority p) (x e)≠nonsharedCoord (minority p) (y e)) ≤
      min p (1-p)+event μ (fun e => ¬Consistent (b e) (x e) (y e)) := by
  dsimp only
  rw [←minority_mass μ b]
  exact (event_mono μ (fun e h => coordinate_mismatch _ _ _ _ h)).trans (event_union_le μ _ _)
end
end PlanarUnitDistances.RareMass

namespace PlanarUnitDistances.RareLabels
open FiniteLaw FiniteStarCoupling LevelScores RareScore RareMass
open scoped Classical
noncomputable section
variable {P Q A : Type*} [Fintype P] [Fintype Q] [Fintype A]

omit [Fintype A] in
lemma exception_diag (r : Bool) (l : A) (x : A×A) :
    exceptional r (l,l) x ↔ nonsharedCoord r x≠l := by cases r <;> simp [exceptional,nonsharedCoord]

theorem dominant {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧
    ∀ (P Q A : Type) [Fintype P] [Fintype Q] [Fintype A],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,γ*U.val p≤(left π).val p) → (∀q,γ*W.val q≤(right π).val q) →
    ∀ξ : ℝ,0≤ξ → ξ≤ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀(bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A),
    minorityMass π bit+error π bit x y≤ s₀ →
    ∃l : A×A,event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (x p))+
      event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (y q))≤
        C*(minorityMass π bit+error π bit x y) := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hm⟩ := LawExpansion.matching hγ hη
  refine ⟨s₀,ξ₀,C,hs,hξ,hC,?_⟩
  intro P Q A _ _ _ π U W hl hr ξ hξ0 hξb hexp bit x y hsmall
  let r := minority (event π (fun pq => bit pq.1 pq.2=true))
  have hd := mismatch_le_minority_error π (fun pq => bit pq.1 pq.2) (fun pq => x pq.1) (fun pq => y pq.2)
  change event π (fun pq => nonsharedCoord r (x pq.1)≠nonsharedCoord r (y pq.2))≤
    minorityMass π bit+error π bit x y at hd
  obtain ⟨l,hl⟩ := hm P Q A π U W (fun p => nonsharedCoord r (x p)) (fun q => nonsharedCoord r (y q))
    hl hr ξ hξ0 hξb hexp (hd.trans hsmall)
  refine ⟨(l,l),?_⟩
  simp only [exception_diag]
  exact hl.trans (mul_le_mul_of_nonneg_left hd hC.le)

omit [Fintype A] in
lemma minority_le (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) (l : A×A) :
    minorityMass π bit≤
    event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (x p))+
    event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (y q))+
    error π bit x y := by
  simpa only [left,right,LawExpansion.push_event,minorityMass,error] using
    minority_le_exceptions π (fun pq => bit pq.1 pq.2) (fun pq => x pq.1) (fun pq => y pq.2) l

end
end PlanarUnitDistances.RareLabels

namespace PlanarUnitDistances.LawRare
open Finset FiniteLaw LawExpansion FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma event_domination (μ ν : Law P) {γ : ℝ} (h : ∀p,γ*μ.val p≤ν.val p) (F : P → Prop) :
    γ*event μ F≤event ν F := by
  unfold event avg
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  by_cases hp : F p <;> simp [hp,h p]

theorem small_rect (π : Law (P×Q)) (U : Law P) (W : Law Q) {γ η ξ a : ℝ}
    (hγ : 0<γ) (hη : 0≤η) (hξ : 0≤ξ)
    (hl : ∀p,γ*U.val p≤(left π).val p) (hr : ∀q,γ*W.val q≤(right π).val q)
    (hexp : ∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ))
    (F : Finset P) (G : Finset Q) (hF : event (left π) (fun p => p∈F)≤a) :
    event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      (((a/γ)^η+ξ)/γ)*Real.sqrt (event (left π) (fun p => p∈F)*event (right π) (fun q => q∈G)) := by
  let u := event U (fun p => p∈F)
  let v := event W (fun q => q∈G)
  let h := event (left π) (fun p => p∈F)
  let k := event (right π) (fun q => q∈G)
  have hu : 0≤u := event_nonneg _ _
  have hv : 0≤v := event_nonneg _ _
  have hh : 0≤h := event_nonneg _ _
  have hk : 0≤k := event_nonneg _ _
  have hul : γ*u≤h := event_domination U (left π) hl _
  have hvr : γ*v≤k := event_domination W (right π) hr _
  have hp := mul_le_mul hul hvr (mul_nonneg hγ.le hv) hh
  have hs : γ*Real.sqrt (u*v)≤Real.sqrt (h*k) := by
    apply (sq_le_sq₀ (mul_nonneg hγ.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hu hv),Real.sq_sqrt (mul_nonneg hh hk)]
    nlinarith
  have huv : u*v≤a/γ := by
    have ha : u≤a/γ := (le_div_iff₀ hγ).mpr (by linarith)
    exact (mul_le_of_le_one_right hu (event_le_one W _)).trans ha
  have he := Real.rpow_le_rpow (mul_nonneg hu hv) huv hη
  have han : 0≤(a/γ)^η+ξ := add_nonneg (Real.rpow_nonneg (div_nonneg (hh.trans hF) hγ.le) _) hξ
  have hs' : Real.sqrt (u*v)≤Real.sqrt (h*k)/γ := (le_div_iff₀ hγ).mpr (by nlinarith)
  calc
    _ ≤ Real.sqrt (u*v)*((u*v)^η+ξ) := hexp F G
    _ ≤ Real.sqrt (u*v)*((a/γ)^η+ξ) := mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ ≤ (Real.sqrt (h*k)/γ)*((a/γ)^η+ξ) := mul_le_mul_of_nonneg_right hs' han
    _ = _ := by ring

lemma sqrt_le_half_sum {h k : ℝ} (hh : 0≤h) (hk : 0≤k) : Real.sqrt (h*k)≤(h+k)/2 := by
  have hs := Real.sq_sqrt (mul_nonneg hh hk)
  have hn := Real.sqrt_nonneg (h*k)
  nlinarith [sq_nonneg (h-k)]

theorem edge_rare (π : Law (P×Q)) (F : Finset P) (G : Finset Q) {θ : ℝ} (hθ : 0≤θ)
    (h : event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      θ*Real.sqrt (event (left π) (fun p => p∈F)*event (right π) (fun q => q∈G))) :
    event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      θ/2*(event (left π) (fun p => p∈F)+event (right π) (fun q => q∈G)) := by
  have h' := mul_le_mul_of_nonneg_left (sqrt_le_half_sum (event_nonneg (left π) (fun p => p∈F)) (event_nonneg (right π) (fun q => q∈G))) hθ
  calc
    _ ≤ θ*Real.sqrt _ := h
    _ ≤ θ*((event (left π) (fun p => p∈F)+event (right π) (fun q => q∈G))/2) := h'
    _ = _ := by ring
end
end PlanarUnitDistances.LawRare

namespace PlanarUnitDistances.LawWedges
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma conditional_eq (π : Law (P×Q)) (F : Finset P) {q : Q} (hq : 0<(right π).val q) :
    ExpansionConsequences.conditional (fun p q => π.val (p,q)) F q=event (col π q) (fun p => p∈F) := by
  simp only [ExpansionConsequences.conditional,LawExpansion.right_val]
  rw [←LawExpansion.mass_event]
  simp only [ExpansionConsequences.mass,col_val π hq,sum_div]

lemma wedgeMass_eq (π : Law (P×Q)) (F : Finset P) :
    ExpansionConsequences.wedgeMass (fun p q => π.val (p,q)) F=
      avg (right π) (fun q => (event (col π q) (fun p => p∈F))^2) := by
  unfold ExpansionConsequences.wedgeMass avg
  apply sum_congr rfl
  intro q _
  rw [LawExpansion.right_val]
  by_cases hq : 0<(right π).val q
  · rw [conditional_eq π F hq]
  · have hz := le_antisymm (le_of_not_gt hq) ((right π).nonneg q)
    simp only [hz,zero_mul]

theorem rare (π : Law (P×Q)) (F : Finset P) {θ d : ℝ} (hθ : 0≤θ) (hd : 0<d)
    (hexp : ∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      θ*Real.sqrt (event (left π) (fun p => p∈F)*event (right π) (fun q => q∈G))) :
    avg (right π) (fun q => (event (col π q) (fun p => p∈F))^2)≤
      (d+θ/Real.sqrt d)*event (left π) (fun p => p∈F) := by
  have h := ExpansionConsequences.wedge_rare (fun p q => π.val (p,q)) (fun p q => π.nonneg (p,q)) F hθ hd
  have hl : ExpansionConsequences.left (fun p q => π.val (p,q))=(left π).val := funext (LawExpansion.left_val π)
  have hr : ExpansionConsequences.right (fun p q => π.val (p,q))=(right π).val := funext (LawExpansion.right_val π)
  simp only [LawExpansion.rect_event,hl,hr,LawExpansion.mass_event] at h
  simpa only [wedgeMass_eq π F] using h hexp

lemma pair_event_sq (μ : Law P) (F : P → Prop) :
    event (pair μ μ) (fun pp => F pp.1 ∧ F pp.2)=(event μ F)^2 := by
  have h := pair_prod μ μ (fun p => if F p then 1 else 0) (fun p => if F p then 1 else 0)
  have he : event (pair μ μ) (fun pp => F pp.1 ∧ F pp.2)=
      avg (pair μ μ) (fun pp => (if F pp.1 then 1 else 0)*(if F pp.2 then 1 else 0)) := by
    apply avg_congr
    intro pp
    split_ifs <;> simp_all
  rw [he,h]
  simp only [event,pow_two]
end
end PlanarUnitDistances.LawWedges

namespace PlanarUnitDistances.RareMoments
open Finset FiniteLaw FiniteStarCoupling RareLabels LevelScores RareScore
open scoped Classical
noncomputable section
variable {P Q A : Type} [Fintype P] [Fintype Q] [Fintype A]

omit [Fintype A] in
theorem joint_wedge (π : Law (P×Q)) (U : Law P) (W : Law Q) {γ η ξ a d : ℝ}
    (hγ : 0<γ) (hη : 0≤η) (hξ : 0≤ξ) (ha : 0≤a) (hd : 0<d)
    (hl : ∀p,γ*U.val p≤(left π).val p) (hr : ∀q,γ*W.val q≤(right π).val q)
    (hexp : ∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ))
    (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) (l : A×A)
    (hx : hp π bit x l≤a) :
    joint π bit x y l≤(((a/γ)^η+ξ)/γ)/2*(hp π bit x l+hq π bit y l) ∧
    wedge π bit x l≤(d+(((a/γ)^η+ξ)/γ)/Real.sqrt d)*hp π bit x l := by
  let F := univ.filter (fun p => exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x p))
  let G := univ.filter (fun q => exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (y q))
  have hF : event (left π) (fun p => p∈F)≤a := by simpa only [F,mem_filter,mem_univ,true_and,hp] using hx
  have ht : 0≤((a/γ)^η+ξ)/γ := div_nonneg
    (add_nonneg (Real.rpow_nonneg (div_nonneg ha hγ.le) _) hξ) hγ.le
  have he := LawRare.edge_rare π F G ht (LawRare.small_rect π U W hγ hη hξ hl hr hexp F G hF)
  have hw := LawWedges.rare π F ht hd (fun G => LawRare.small_rect π U W hγ hη hξ hl hr hexp F G hF)
  simp only [F,G,mem_filter,mem_univ,true_and] at he hw
  constructor
  · exact he
  · calc
      _ = avg (right π) (fun q => (event (col π q) (fun p =>
          exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x p)))^2) := by
        apply avg_congr
        intro q
        exact LawWedges.pair_event_sq (col π q) (fun p =>
          exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x p))
      _ ≤ _ := hw

theorem uniform {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧
    ∀(P Q A : Type) [Fintype P] [Fintype Q] [Fintype A],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,γ*U.val p≤(left π).val p) → (∀q,γ*W.val q≤(right π).val q) →
    ∀ξ : ℝ,0≤ξ → ξ≤ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ ε τ d : ℝ,0≤ε → 0≤τ → 0<d → ε+τ≤ s₀ →
    ∀(bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A),
    minorityMass π bit≤ε → error π bit x y≤τ →
    ∃l : A×A,
      hp π bit x l+hq π bit y l≤C*(minorityMass π bit+error π bit x y) ∧
      minorityMass π bit≤hp π bit x l+hq π bit y l+error π bit x y ∧
      joint π bit x y l≤((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(hp π bit x l+hq π bit y l) ∧
      wedge π bit x l≤(d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*hp π bit x l := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hm⟩ := RareLabels.dominant hγ hη
  refine ⟨s₀,ξ₀,C,hs,hξ,hC,?_⟩
  intro P Q A _ _ _ π U W hl hr ξ hξ0 hξb hexp ε τ d hε hτ hd hsum bit x y hf he
  obtain ⟨l,hdom⟩ := hm P Q A π U W hl hr ξ hξ0 hξb hexp bit x y (by linarith)
  have hb : hp π bit x l≤C*(ε+τ) := by
    have hq0 : 0≤hq π bit y l := event_nonneg _ _
    have hh : C*(minorityMass π bit+error π bit x y)≤C*(ε+τ) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    change hp π bit x l+hq π bit y l≤_ at hdom
    linarith
  obtain ⟨hj,hw⟩ := joint_wedge π U W hγ hη.le hξ0 (mul_nonneg hC.le (add_nonneg hε hτ)) hd
    hl hr hexp bit x y l hb
  exact ⟨l,hdom,RareLabels.minority_le π bit x y l,hj,hw⟩
end
end PlanarUnitDistances.RareMoments

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]
lemma event_markov (μ : Law X) (f : X → ℝ) (hf : ∀x,0≤f x) {ε : ℝ} (hε : 0<ε) :
    event μ (fun x => ε<f x)≤avg μ f/ε := by
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]; unfold event; rw [←avg_smul]
  apply avg_mono
  intro x
  split_ifs with h
  · simpa using h.le
  · simpa using hf x
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.LevelBookkeeping
open Finset FiniteLaw FiniteStarCoupling RareLabels RareMoments RareScore
open scoped Classical
noncomputable section
variable {D P Q A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype A]

omit [Fintype D] [Fintype A] in
lemma minority_nonneg (π : Law (P×Q)) (b : P → Q → Bool) : 0 ≤ minorityMass π b :=
  le_min (event_nonneg _ _) (sub_nonneg.mpr (event_le_one _ _))
omit [Fintype D] [Fintype A] in
lemma not_common (π : Law (P×Q)) (b : P → Q → Bool) {ε : ℝ}
    (h : ¬PlaceScore.common ε (event π (fun pq => b pq.1 pq.2=true))) : minorityMass π b < ε := by
  unfold PlaceScore.common at h
  unfold minorityMass
  rcases not_and_or.mp h with h | h
  · exact (min_le_left _ _).trans_lt (lt_of_not_ge h)
  · exact (min_le_right _ _).trans_lt (by linarith)

theorem select {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧
    ∀(D P Q A : Type) [Fintype D] [Fintype P] [Fintype Q] [Fintype A] [Nonempty A],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,γ*U.val p ≤ (left π).val p) → (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ ε τ d : ℝ,0 ≤ ε → 0 ≤ τ → 0<d → ε+τ ≤ s₀ →
    ∀(b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A),
    ∃l : D → A×A,∀s, goodRare ε τ π (b s) (x s) (y s) →
      hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s) ≤ C*(minorityMass π (b s)+error π (b s) (x s) (y s)) ∧
      minorityMass π (b s) ≤ hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)+error π (b s) (x s) (y s) ∧
      joint π (b s) (x s) (y s) (l s) ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)) ∧
      wedge π (b s) (x s) (l s) ≤ (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*hp π (b s) (x s) (l s) := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hh⟩ := RareMoments.uniform hγ hη
  refine ⟨s₀,ξ₀,C,hs,hξ,hC,?_⟩
  intro D P Q A _ _ _ _ _ π U W hl hr ξ hξ0 hξb hexp ε τ d hε hτ hd hsum b x y
  have he : ∀s,∃l : A×A, goodRare ε τ π (b s) (x s) (y s) →
      hp π (b s) (x s) l+hq π (b s) (y s) l ≤ C*(minorityMass π (b s)+error π (b s) (x s) (y s)) ∧
      minorityMass π (b s) ≤ hp π (b s) (x s) l+hq π (b s) (y s) l+error π (b s) (x s) (y s) ∧
      joint π (b s) (x s) (y s) l ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(hp π (b s) (x s) l+hq π (b s) (y s) l) ∧
      wedge π (b s) (x s) l ≤ (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*hp π (b s) (x s) l := by
    intro s
    by_cases hg : goodRare ε τ π (b s) (x s) (y s)
    · obtain ⟨l,hl⟩ := hh P Q A π U W hl hr ξ hξ0 hξb hexp ε τ d hε hτ hd hsum
        (b s) (x s) (y s) (not_common π (b s) hg.1).le hg.2
      exact ⟨l,fun _ => hl⟩
    · exact ⟨Classical.choice inferInstance,fun h => False.elim (hg h)⟩
  choose l hl using he
  exact ⟨l,hl⟩

omit [Fintype A] in

theorem widths (σ : Law D) (π : Law (P×Q)) (b : D → P → Q → Bool)
    (x : D → P → A×A) (y : D → Q → A×A) {ε τ : ℝ} (hε : 0<ε) (hτ : 0<τ) :
    event σ (fun s => PlaceScore.common ε (event π (fun pq => b s pq.1 pq.2=true))) ≤
      avg σ (fun s => minorityMass π (b s))/ε ∧
    event σ (fun s => damaged ε τ π (b s) (x s) (y s)) ≤
      avg σ (fun s => error π (b s) (x s) (y s))/τ := by
  constructor
  · apply (le_div_iff₀ hε).mpr
    rw [mul_comm]
    unfold event
    rw [←avg_smul]
    apply avg_mono
    intro s
    split_ifs with hs
    · rw [mul_one]
      have he : ε ≤ event π (fun pq => b s pq.1 pq.2=true) ∧
        event π (fun pq => b s pq.1 pq.2=true) ≤ 1-ε := hs
      exact le_min he.1 (by linarith [he.2])
    · simpa using minority_nonneg π (b s)
  · refine (event_mono σ (fun s hs => hs.2)).trans ?_
    exact event_markov σ (fun s => error π (b s) (x s) (y s)) (fun _ => event_nonneg _ _) hτ

omit [Fintype A] in

theorem moments (σ : Law D) (π : Law (P×Q)) (b : D → P → Q → Bool)
    (x : D → P → A×A) (y : D → Q → A×A) (l : D → A×A) {ε τ C θ ψ : ℝ}
    (hC : 0 ≤ C)
    (h : ∀s,goodRare ε τ π (b s) (x s) (y s) →
      hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s) ≤ C*(minorityMass π (b s)+error π (b s) (x s) (y s)) ∧
      joint π (b s) (x s) (y s) (l s) ≤ θ*(hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)) ∧
      wedge π (b s) (x s) (l s) ≤ ψ*hp π (b s) (x s) (l s)) :
    let R := fun s => goodRare ε τ π (b s) (x s) (y s)
    let HP := avg σ (fun s => if R s then hp π (b s) (x s) (l s) else 0)
    let HQ := avg σ (fun s => if R s then hq π (b s) (y s) (l s) else 0)
    HP+HQ ≤ C*(avg σ (fun s => minorityMass π (b s))+avg σ (fun s => error π (b s) (x s) (y s))) ∧
    avg σ (fun s => if R s then joint π (b s) (x s) (y s) (l s) else 0) ≤ θ*(HP+HQ) ∧
    avg σ (fun s => if R s then wedge π (b s) (x s) (l s) else 0) ≤ ψ*HP := by
  dsimp only
  constructor
  · rw [←avg_add,←avg_add,←avg_smul]
    apply avg_mono
    intro s
    split_ifs with hs
    · exact (h s hs).1
    · simpa only [zero_add,error] using mul_nonneg hC (add_nonneg (minority_nonneg π (b s))
        (event_nonneg π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))))
  constructor
  · rw [←avg_add,←avg_smul]
    apply avg_mono
    intro s
    split_ifs with hs
    · exact (h s hs).2.1
    · simp
  · rw [←avg_smul]
    apply avg_mono
    intro s
    split_ifs with hs
    · exact (h s hs).2.2
    · simp
end
end PlanarUnitDistances.LevelBookkeeping

namespace PlanarUnitDistances.FiniteLaw
open scoped Classical
noncomputable section
variable {D : Type*} [Fintype D]
lemma cut_le_avg (σ : Law D) (c : D → Prop) (f : D → ℝ) (hf : ∀s,0 ≤ f s) : cut σ c f ≤ avg σ f :=
  avg_mono σ (fun s => by split_ifs <;> first | exact le_rfl | exact hf s)
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ActualScoreBook
open MeasureTheory FiniteLaw LevelSnapshot ActualSlots ScoreBook FiniteStarCoupling RareRows RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

lemma average (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) (F : Data V (P×Q) → ℝ) :
    (∫a,F (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a) ∂LevelScale.measure S)=
      mass S*avg (make S z w x y u π h ε good label hm).levels F := by
  have he := compress_avg (LevelScale.measure S) hm
    (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u)
    (measurable_snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u) F
  exact (mul_comm _ _).trans ((eq_div_iff hm.ne').mp he) |>.symm

end
end PlanarUnitDistances.ActualScoreBook

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
omit [Fintype Y] in
lemma fiber_average (μ : Law X) (φ : X → Y) (y : Y) (f : X → ℝ) :
    fiberMass μ φ y*avg (cond μ φ y) f=avg μ (fun x => if φ x=y then f x else 0) := by
  simp only [avg,mul_sum,←mul_assoc,cond_weight]
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp
lemma cut_average (μ : Law X) (c : X → Prop) (f : X → ℝ) :
    event μ c*avg (cond μ (fun x => decide (c x)) true) f=avg μ (fun x => if c x then f x else 0) := by
  simpa only [fiberMass,decide_eq_true_eq] using fiber_average μ (fun x => decide (c x)) true f
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.GraphPrediction
open Finset FiniteLaw FiniteStarCoupling CommonTemplate CrossPrediction CrossSampling StrictCross
open scoped Classical
noncomputable section
variable {P Q A B H D C : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype H] [Fintype D] [Fintype C] [Nonempty C]

lemma mixture_col (π : Law (P×Q)) : mixture (right π) (col π)=left π := by
  apply law_ext
  intro p
  simp only [mixture,avg,col_weight,FiniteStarCoupling.left_val]

omit [Fintype H] in
lemma prediction_eq (π : Law (P×Q)) (h : P → H) (x : P → A×B) (y : Q → A×B) :
    predictionError π h x y=1-predicted (right π) (col π) h x y := by
  unfold predicted
  rw [mixture_col,col_avg]
  unfold predictionError
  rw [avg_sub,avg_const]
  congr 1
  apply avg_congr
  intro pq
  simp only [crossMass,posteriorState,event,push_avg,Hashing.indicator]

omit [Fintype A] [Fintype B] in
lemma actual_error (π : Law (P×Q)) (b : P → Q → Bool) (x : P → A×B) (y : Q → A×B) :
    1-actual (right π) (col π) x y ≤
      event π (fun pq => ¬CrossStructure.Consistent (b pq.1 pq.2) (x pq.1) (y pq.2)) := by
  unfold actual
  rw [col_avg,←avg_const π 1,←avg_sub]
  apply avg_mono
  intro pq
  have hc (h : CrossStructure.Consistent (b pq.1 pq.2) (x pq.1) (y pq.2)) : Adj (x pq.1) (y pq.2) := by
    cases hb : b pq.1 pq.2
    · exact Or.inr (by simpa [hb,CrossStructure.Consistent] using h)
    · exact Or.inl (by simpa [hb,CrossStructure.Consistent] using h)
  dsimp [Hashing.indicator]
  by_cases h : CrossStructure.Consistent (b pq.1 pq.2) (x pq.1) (y pq.2)
  · simp [h,hc h]
  · simp only [h,not_false_eq_true,ite_true]
    split_ifs <;> norm_num

theorem exists_common_history (σ : Law D) (π : Law (P×Q)) (hμ : ∀p,0<(left π).val p)
    (c : D → Prop) (b : D → P → Q → Bool) (x : D → P → A×B) (y : D → Q → A×B)
    (K : ℕ) (hK : 0<K) :
    ∃ n<K,∃h : P → FiniteInformation.History (C×C) n,
      (univ.image h).card ≤ (Fintype.card C)^(2*K) ∧
      avg σ (fun s => if c s then predictionError π h (x s) (y s) else 0) ≤
        avg σ (fun s => if c s then event π (fun pq =>
          ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2)) else 0)+
        event σ c*(4/(Fintype.card C:ℝ)+18*(FiniteInformation.KL
          (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
          (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)/(K:ℝ))^(1/4:ℝ)) := by
  let ν := cond σ (fun s => decide (c s)) true
  obtain ⟨n,hn,h,hcard,hb⟩ := exists_cross_history (C := C) (right π) (col π)
    (by simpa only [mixture_col] using hμ) ν x y K hK
  rw [mixture_col] at hb
  refine ⟨n,hn,h,hcard,?_⟩
  have he := avg_mono ν (f := fun s => predictionError π h (x s) (y s))
    (g := fun s => event π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))+
      (actual (right π) (col π) (x s) (y s)-predicted (right π) (col π) h (x s) (y s))) (fun s => by
    have ha := actual_error π (b s) (x s) (y s)
    rw [prediction_eq π h (x s) (y s)]
    exact (show 1-predicted (right π) (col π) h (x s) (y s) ≤
      event π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))+
      (actual (right π) (col π) (x s) (y s)-predicted (right π) (col π) h (x s) (y s)) by linarith))
  rw [avg_add] at he
  have hh := mul_le_mul_of_nonneg_left (he.trans (add_le_add_right hb _)) (event_nonneg σ c)
  rw [mul_add] at hh
  simp only [ν,cut_average] at hh
  exact hh
end
end PlanarUnitDistances.GraphPrediction

namespace PlanarUnitDistances.LawStable
open Finset FiniteLaw StarScore FiniteStarCoupling LawExpansion
open scoped Classical
noncomputable section
variable {X P Q : Type*} [Fintype X] [Fintype P] [Fintype Q]

lemma minority_le_half (μ : Law X) (b : X → Bool) : minorityFrequency μ b ≤ 1/2 := by
  unfold minorityFrequency
  have h₁ := min_le_left (frequency μ b) (1-frequency μ b)
  have h₂ := min_le_right (frequency μ b) (1-frequency μ b)
  linarith
lemma minority_event (μ : Law X) (b : X → Bool) (l : Bool) :
    minorityFrequency μ b ≤ event μ (fun x => b x≠l) := by
  have hf : event μ (fun x => b x≠true)=1-frequency μ b := by
    simpa only [frequency,ne_eq] using event_compl μ (fun x => b x=true)
  cases l
  · have he : event μ (fun x => b x≠false)=frequency μ b := by
      apply avg_congr
      intro x
      cases b x <;> simp
    rw [he]
    exact min_le_left _ _
  · rw [hf]
    exact min_le_right _ _
lemma majority_error (μ : Law X) (b : X → Bool) :
    event μ (fun x => b x≠majority μ b)=minorityFrequency μ b := by
  have he : event μ (fun x => b x≠majority μ b)=
      event μ (fun x => b x=LevelScores.minority (frequency μ b)) := by
    apply avg_congr
    intro x
    simp only [majority]
    have hb : ∀u v : Bool,u≠(!v) ↔ u=v := by decide
    simp only [hb]
    split_ifs <;> rfl
  rw [he]
  exact RareMass.minority_mass μ b
lemma majority_le_variation (μ : Law X) (b : X → Bool) :
    event μ (fun x => b x≠majority μ b) ≤ variation μ b := by
  rw [majority_error]
  unfold minorityFrequency variation
  have h₀ := frequency_nonneg μ b
  have h₁ := frequency_le_one μ b
  by_cases h : frequency μ b ≤ 1/2
  · rw [min_eq_left (by linarith)]
    nlinarith
  · rw [min_eq_right (by linarith)]
    nlinarith

theorem stable {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃ ξ₀ C : ℝ,0<ξ₀ ∧ 0<C ∧
    ∀ (P Q : Type) [Fintype P] [Fintype Q],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q) (b : P → Q → Bool),
    (∀p,γ*U.val p ≤ (left π).val p) →
    (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    minorityFrequency π (fun pq => b pq.1 pq.2) ≤ C*(VP π b+VQ π b) := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hmatch⟩ := matching hγ hη
  refine ⟨ξ₀,max (C+1) (1/(2*s₀)),hξ,lt_of_lt_of_le (by linarith) (le_max_left _ _),?_⟩
  intro P Q _ _ π U W b hl hr ξ hξ0 hξb hexp
  let a := fun p => majority (row π p) (b p)
  let d := fun q => majority (col π q) (fun p => b p q)
  have hp : event π (fun pq => b pq.1 pq.2≠a pq.1) ≤ VP π b := by
    rw [←row_event π (fun p q => b p q≠a p)]
    exact avg_mono (left π) (fun p => majority_le_variation (row π p) (b p))
  have hq : event π (fun pq => b pq.1 pq.2≠d pq.2) ≤ VQ π b := by
    rw [←col_event π (fun p q => b p q≠d q)]
    exact avg_mono (right π) (fun q => majority_le_variation (col π q) (fun p => b p q))
  have hvp : 0 ≤ VP π b := avg_nonneg _ (fun p => variation_nonneg _ _)
  have hvq : 0 ≤ VQ π b := avg_nonneg _ (fun q => variation_nonneg _ _)
  have hm : event π (fun pq => a pq.1≠d pq.2) ≤ VP π b+VQ π b := by
    refine (event_mono π (fun pq h => show b pq.1 pq.2≠a pq.1 ∨ b pq.1 pq.2≠d pq.2 from ?_)).trans
      ((event_union_le π _ _).trans (add_le_add hp hq))
    by_contra! he
    exact h (he.1.symm.trans he.2)
  by_cases hv : VP π b+VQ π b ≤ s₀
  · obtain ⟨l,he⟩ := hmatch P Q Bool π U W a d hl hr ξ hξ0 hξb hexp (hm.trans hv)
    have hleft := event_nonneg (right π) (fun q => d q≠l)
    have he' : event π (fun pq => a pq.1≠l) ≤ C*(VP π b+VQ π b) := by
      have ha : event π (fun pq => a pq.1≠l)=event (left π) (fun p => a p≠l) :=
        (push_event π Prod.fst (fun p => a p≠l)).symm
      rw [ha]
      have hh := mul_le_mul_of_nonneg_left hm hC.le
      linarith
    have hevent : event π (fun pq => b pq.1 pq.2≠l) ≤ (C+1)*(VP π b+VQ π b) := by
      have hh := (event_mono π (fun pq (h : b pq.1 pq.2≠l) =>
        show b pq.1 pq.2≠a pq.1 ∨ a pq.1≠l from by
          by_contra! he; exact h (he.1.trans he.2))).trans (event_union_le π _ _)
      nlinarith
    exact (minority_event π (fun pq => b pq.1 pq.2) l).trans (hevent.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hvp hvq)))
  · have hs' : 0<2*s₀ := by linarith
    have hh : 1/2 ≤ (1/(2*s₀))*(VP π b+VQ π b) := by
      have he : (VP π b+VQ π b)/(2*s₀)= (1/(2*s₀))*(VP π b+VQ π b) := by ring
      rw [←he]
      apply (le_div_iff₀ hs').mpr
      linarith
    exact (minority_le_half π (fun pq => b pq.1 pq.2)).trans (hh.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg hvp hvq)))
end
end PlanarUnitDistances.LawStable

namespace PlanarUnitDistances.SelectedBook
open FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook LevelBookkeeping
open scoped Classical
noncomputable section

theorem constants {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C L : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧ 0<L ∧
    ∀(D P Q A T : Type) [Fintype D] [Fintype P] [Fintype Q] [Fintype A]
      [Nonempty A] [Fintype T] [Nonempty T],
    ∀(σ : Law D) (π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,0<(left π).val p) →
    (∀p,γ*U.val p ≤ (left π).val p) → (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ ε τ d : ℝ,0 ≤ ε → 0 ≤ τ → 0<d → ε+τ ≤ s₀ →
    ∀(b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A),
    ∀K : ℕ,0<K → ∃n<K,∃h : P → FiniteInformation.History (T×T) n,∃l : D → A×A,
      (Finset.univ.image h).card ≤ (Fintype.card T)^(2*K) ∧
      (∀s,minorityMass π (b s) ≤ L*(FiniteStarCoupling.VP π (b s)+FiniteStarCoupling.VQ π (b s))) ∧
      (∀s,goodRare ε τ π (b s) (x s) (y s) →
        hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s) ≤ C*(minorityMass π (b s)+error π (b s) (x s) (y s)) ∧
        minorityMass π (b s) ≤ hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)+error π (b s) (x s) (y s) ∧
        joint π (b s) (x s) (y s) (l s) ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)) ∧
        wedge π (b s) (x s) (l s) ≤ (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*hp π (b s) (x s) (l s)) ∧
      cut σ (fun s => PlaceScore.common ε (StarScore.frequency π (fun pq => b s pq.1 pq.2)))
        (fun s => CommonTemplate.predictionError π h (x s) (y s)) ≤
        avg σ (fun s => error π (b s) (x s) (y s))+
        event σ (fun s => PlaceScore.common ε (StarScore.frequency π (fun pq => b s pq.1 pq.2)))*
          (4/(Fintype.card T:ℝ)+18*(FiniteInformation.KL
            (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
            (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)/(K:ℝ))^(1/4:ℝ)) := by
  obtain ⟨s₀,ξ₁,C,hs,hξ₁,hC,hr⟩ := LevelBookkeeping.select hγ hη
  obtain ⟨ξ₂,L,hξ₂,hL,hstable⟩ := LawStable.stable hγ hη
  refine ⟨s₀,min ξ₁ ξ₂,C,L,hs,lt_min hξ₁ hξ₂,hC,hL,?_⟩
  intro D P Q A T _ _ _ _ _ _ _ σ π U W hμ hl hr' ξ hξ0 hξ hexp ε τ d hε hτ hd hsum b x y K hK
  obtain ⟨l,hl⟩ := hr D P Q A π U W hl hr' ξ hξ0 (hξ.trans (min_le_left _ _)) hexp ε τ d hε hτ hd hsum b x y
  obtain ⟨n,hn,h,hcard,hpred⟩ := GraphPrediction.exists_common_history (C := T) σ π hμ
    (fun s => PlaceScore.common ε (StarScore.frequency π (fun pq => b s pq.1 pq.2))) b x y K hK
  refine ⟨n,hn,h,l,hcard,?_,hl,?_⟩
  · intro s
    exact hstable P Q π U W (b s) ‹∀p,γ*U.val p ≤ (left π).val p› hr' ξ hξ0
      (hξ.trans (min_le_right _ _)) hexp
  · exact hpred.trans (add_le_add (cut_le_avg σ _ _ (fun s => event_nonneg π _)) le_rfl)
end
end PlanarUnitDistances.SelectedBook

namespace PlanarUnitDistances.PreparedSelection
open FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook LevelBookkeeping
open scoped Classical
noncomputable section

theorem constants {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C L : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧ 0<L ∧
    ∀(D P Q A T : Type) [Fintype D] [Fintype P] [Fintype Q] [Fintype A]
      [Nonempty A] [Fintype T] [Nonempty T],
    ∀(σ : Law D) (π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,0<(left π).val p) →
    (∀p,γ*U.val p ≤ (left π).val p) → (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ ε τ d : ℝ,0<ε → 0<τ → 0<d → ε+τ ≤ s₀ →
    ∀(b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A),
    ∀K : ℕ,0<K → ∃n<K,∃h : P → FiniteInformation.History (T×T) n,∃l : D → A×A,
      let B : Book D P Q (FiniteInformation.History (T×T) n) A :=
        ⟨σ,π,b,x,y,h,ε,(fun s => error π (b s) (x s) (y s)≤τ),l⟩
      (Fintype.card (FiniteInformation.History (T×T) n)) ≤ (Fintype.card T)^(2*K) ∧
      (∀s,minorityMass π (b s) ≤ L*(VP π (b s)+VQ π (b s))) ∧
      (∀s,B.R s → minorityMass π (b s) ≤ hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)+error π (b s) (x s) (y s)) ∧
      B.WC ≤ B.S/ε ∧ B.WB ≤ B.M/τ ∧ B.HP+B.HQ ≤ C*(B.S+B.M) ∧
      B.J ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(B.HP+B.HQ) ∧
      cut σ B.R (fun s => wedge π (b s) (x s) (l s)) ≤
        (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*B.HP ∧
      B.EP ≤ B.M+B.WC*(4/(Fintype.card T:ℝ)+18*(FiniteInformation.KL (FiniteInformation.wedge (right π).val (fun q => (col π q).val)) (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)/(K:ℝ))^(1/4:ℝ)) := by
  obtain ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,hh⟩ := SelectedBook.constants hγ hη
  refine ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,?_⟩
  intro D P Q A T _ _ _ _ _ _ _ σ π U W hμ hl hr ξ hξ0 hξb hexp ε τ d hε hτ hd hsum b x y K hK
  obtain ⟨n,hn,h,l,_,hst,hl',hpred⟩ := hh D P Q A T σ π U W hμ hl hr ξ hξ0 hξb hexp
    ε τ d hε.le hτ.le hd hsum b x y K hK
  let B : Book D P Q (FiniteInformation.History (T×T) n) A :=
    ⟨σ,π,b,x,y,h,ε,(fun s => error π (b s) (x s) (y s)≤τ),l⟩
  have hw := widths σ π b x y hε hτ
  have hm := moments σ π b x y l hC.le
    (fun s hs => ⟨(hl' s hs).1,(hl' s hs).2.2.1,(hl' s hs).2.2.2⟩)
  refine ⟨n,hn,h,l,?_,hst,?_,hw.1,?_,hm.1,hm.2.1,hm.2.2,hpred⟩
  · rw [FiniteInformation.history_card,Fintype.card_prod,←pow_two,←pow_mul]
    exact Nat.pow_le_pow_right (Fintype.card_pos) (Nat.mul_le_mul_left 2 hn.le)
  · intro s hs
    exact (hl' s hs).2.1
  · change event σ (fun s => ¬PlaceScore.common ε (event π (fun pq => b s pq.1 pq.2 = true)) ∧ ¬error π (b s) (x s) (y s)≤τ) ≤ (avg σ (fun s => error π (b s) (x s) (y s)))/τ
    simpa only [LevelBookkeeping.damaged,not_le] using hw.2
end
end PlanarUnitDistances.PreparedSelection

namespace PlanarUnitDistances.LevelStates
open MeasureTheory Set Real FiniteLaw PlaceLevels
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

theorem exists_bounded_states_support (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (hu : ∀e,0<μ.val e → (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1) :
    ∃u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts,
      (∀σ,StateConsistency.Fractional (u σ)) ∧
      (∫a,meanError μ S z w src tgt u a ∂LevelScale.measure S) ≤ 2*log 2+4 := by
  obtain ⟨u,hf,hb⟩ := exists_bounded_states (support μ) S z w
    (fun e => src e.val) (fun e => tgt e.val) (fun e => hu e.val e.property)
  refine ⟨u,hf,?_⟩
  convert hb using 1
  apply integral_congr_ae
  filter_upwards [] with a
  exact (support_avg μ (edgeError S z w src tgt u a)).symm
end
end PlanarUnitDistances.LevelStates

namespace PlanarUnitDistances.ActualPreparation
open MeasureTheory FiniteLaw LevelSnapshot ActualScoreBook ScoreBook
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

lemma scale_le_mass (π : Law (P×Q)) (S : Finset K) (d : P×Q → K) :
    LevelScale.scale π S d ≤ mass S := by
  calc
    _ ≤ ∫_a : PlaceLevels.Place K S×ℝ,(1:ℝ) ∂LevelScale.measure S :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun a => (LevelScale.minority_bounds π S d a).1))
        (integrable_const 1) (Filter.Eventually.of_forall (fun a => (LevelScale.minority_bounds π S d a).2))
    _ = _ := by simp [mass]

omit [Fintype V] in
lemma frequency (π : Law (P×Q)) (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : PlaceLevels.Place K S×ℝ) :
    RareLabels.minorityMass π (fun p q => (snapshot S z w (fun pq : P×Q => x pq.1)
      (fun pq : P×Q => y pq.2) u a).1 (p,q))=
    LevelScale.minority π S (fun pq => z (x pq.1)-z (y pq.2)) a := by
  unfold RareLabels.minorityMass LevelScale.minority
  apply congrArg (fun t : ℝ => min t (1-t))
  unfold LevelScale.prob ThresholdProfiles.frequency event avg
  apply Finset.sum_congr rfl
  intro e _
  apply congrArg (fun r : ℝ => π.val e*r)
  simp only [snapshot, LevelStates.bit, ThresholdProfiles.bit, LevelScale.cut, decide_eq_true_eq]
  rfl

omit [Fintype V] in
lemma inconsistency (π : Law (P×Q)) (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : PlaceLevels.Place K S×ℝ) :
    RareLabels.error π (fun p q => (snapshot S z w (fun pq : P×Q => x pq.1)
      (fun pq : P×Q => y pq.2) u a).1 (p,q))
      (fun p => (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a).2 (x p))
      (fun q => (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a).2 (y q))=
    LevelStates.meanError π S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a := by
  unfold RareLabels.error event LevelStates.meanError
  apply avg_congr
  intro pq
  simp only [snapshot,LevelStates.edgeError]
  split_ifs <;> simp_all

theorem states (π : Law (P×Q)) (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hS : 0<LevelScale.scale π S (fun pq => z (x pq.1)-z (y pq.2))) :
    ∃hm : 0 < mass S, ∃u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts,
      (∀σ,StateConsistency.Fractional (u σ)) ∧
      ∀(h : P → H) (ε : ℝ) (good : Data V (P×Q) → Prop)
        (label : Data V (P×Q) → (V → Bool)×(V → Bool)),
      let B := make S z w x y u π h ε good label hm
      mass S*B.S=LevelScale.scale π S (fun pq => z (x pq.1)-z (y pq.2)) ∧
      mass S*B.M ≤ 2*Real.log 2+4 := by
  have hm := hS.trans_le (scale_le_mass π S _)
  obtain ⟨u,hf,hb⟩ := LevelStates.exists_bounded_states_support π S z w
    (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) (fun pq hh => hu pq.1 pq.2 hh)
  refine ⟨hm,u,hf,?_⟩
  intro h ε good label
  dsimp only
  have ha := average S z w x y u π h ε good label hm
  constructor
  · change mass S*avg (make S z w x y u π h ε good label hm).levels
        (fun s => RareLabels.minorityMass π (fun p q => s.1 (p,q)))=_
    rw [←ha (fun s => RareLabels.minorityMass π (fun p q => s.1 (p,q)))]
    exact integral_congr_ae (Filter.Eventually.of_forall (frequency π S z w x y u))
  · change mass S*avg (make S z w x y u π h ε good label hm).levels
        (fun s => RareLabels.error π (fun p q => s.1 (p,q)) (fun p => s.2 (x p)) (fun q => s.2 (y q)))≤_
    rw [←ha (fun s => RareLabels.error π (fun p q => s.1 (p,q))
      (fun p => s.2 (x p)) (fun q => s.2 (y q)))]
    simpa only [inconsistency] using hb
end
end PlanarUnitDistances.ActualPreparation

namespace PlanarUnitDistances.ActualPrepared
open MeasureTheory FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  LevelSnapshot ActualScoreBook LevelBookkeeping
open scoped Classical
noncomputable section

theorem constants {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) :
    ∃s₀ ξ₀ C L : ℝ,0 < s₀ ∧ 0 < ξ₀ ∧ 0 < C ∧ 0 < L ∧
    ∀(K V P Q : Type) [Field K] [NumberField K] [Fintype V] [Fintype P] [Fintype Q],
    ∀(S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
      (π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p q,0 < π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1) →
    (∀p,0 < (left π).val p) →
    (∀p,γ*U.val p ≤ (left π).val p) → (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ε τ d : ℝ,0 < ε → 0 < τ → 0 < d → ε+τ ≤ s₀ →
    0 < LevelScale.scale π S (fun pq => z (x pq.1)-z (y pq.2)) →
    ∀m N : ℕ,0 < m → 0 < N →
    ∃hm : 0 < mass S,∃u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts,
    ∃n < N,∃h : P → FiniteInformation.History (Fin m×Fin m) n,
    ∃l : Data V (P×Q) → (V → Bool)×(V → Bool),
      let good := fun a : Data V (P×Q) => error π (fun p q => a.1 (p,q))
        (fun p => a.2 (x p)) (fun q => a.2 (y q)) ≤ τ
      let B := make S z w x y u π h ε good l hm
      (∀σ,StateConsistency.Fractional (u σ)) ∧
      mass S*B.S=LevelScale.scale π S (fun pq => z (x pq.1)-z (y pq.2)) ∧
      mass S*B.M ≤ 2*Real.log 2+4 ∧
      Fintype.card (FiniteInformation.History (Fin m×Fin m) n) ≤ m^(2*N) ∧
      (∀a,minorityMass π (B.bit a) ≤ L*(VP π (B.bit a)+VQ π (B.bit a))) ∧
      (∀a,B.R a → minorityMass π (B.bit a) ≤ hp π (B.bit a) (B.point a) (l a)+
        hq π (B.bit a) (B.center a) (l a)+error π (B.bit a) (B.point a) (B.center a)) ∧
      B.WC ≤ B.S/ε ∧ B.WB ≤ B.M/τ ∧ B.HP+B.HQ ≤ C*(B.S+B.M) ∧
      B.J ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(B.HP+B.HQ) ∧
      cut B.levels B.R (fun a => wedge π (B.bit a) (B.point a) (l a)) ≤
        (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*B.HP ∧
      B.EP ≤ B.M+B.WC*(4/(m:ℝ)+18*(FiniteInformation.KL
        (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
          (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)/(N:ℝ))^(1/4:ℝ)) := by
  obtain ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,hsel⟩ := PreparedSelection.constants hγ hη
  refine ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,?_⟩
  intro K V P Q _ _ _ _ _ S z w x y π U W hu hp hU hW ξ hξ0 hξb hexp ε τ d hε hτ hd hsum hscale m N hm hN
  obtain ⟨hM,u,hfrac,hstate⟩ := ActualPreparation.states (H:=Unit) π S z w x y hu hscale
  let B₀ := make S z w x y u π (fun _ => ()) ε (fun _ => True) (fun _ => (fun _ => false,fun _ => false)) hM
  let : NeZero m := ⟨by omega⟩
  obtain ⟨n,hn,h,l,hcard,hstable,hrare,hWC,hWB,hH,hJ,hwed,hEP⟩ :=
    hsel (Data V (P×Q)) P Q (V → Bool) (Fin m) B₀.levels π U W hp hU hW
      ξ hξ0 hξb hexp ε τ d hε hτ hd hsum
      (fun a p q => a.1 (p,q)) (fun a p => a.2 (x p)) (fun a q => a.2 (y q)) N hN
  refine ⟨hM,u,n,hn,h,l,hfrac,?_,?_,?_,hstable,hrare,hWC,hWB,hH,hJ,hwed,?_⟩
  · exact (hstate (fun _ => ()) ε (fun _ => True) (fun _ => (fun _ => false,fun _ => false))).1
  · exact (hstate (fun _ => ()) ε (fun _ => True) (fun _ => (fun _ => false,fun _ => false))).2
  · simpa only [Fintype.card_fin] using hcard
  · simpa only [Fintype.card_fin, B₀, make] using hEP
end
end PlanarUnitDistances.ActualPrepared

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Profiles
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceBook
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale ActualScoreBook LevelSnapshot BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params) (i : ℕ)
lemma length_pos : 0 < length s a i := LogHistory.length_pos _ _

variable {s a i}

attribute [local instance] OAI.PlanarUnitDistances.IncidenceBook.instFintypeSumSubtypePlaneMemFinsetPQ
local instance instFintypeProdSubtypePlaneMemFinsetPQ_r3490a1_1 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
theorem constants_oai (s : Sequence) :
    ∃s₀ C L : ℝ,0 < s₀ ∧ 0 < C ∧ 0 < L ∧
      ∀a : Params,2*a.epsilon ≤ s₀ → ∀ᶠi in atTop,∃R : Realization s a i,R.Valid C L := by
  obtain ⟨s₀,ξ₀,C,L,hs,hξ,hC,hL,h⟩ := ActualPrepared.constants
    (by norm_num : (0:ℝ) < 27/50) (by norm_num : (0:ℝ) < 1/25)
  refine ⟨s₀,C,L,hs,hC,hL,?_⟩
  intro a ha
  filter_upwards [s.error_limit.eventually_le_const hξ,(scale_limit s).eventually_gt_atTop 0] with i hi hscale
  let M := model s i
  have ht := h M.field (s.P i⊕s.Q i) (s.P i) (s.Q i) M.support M.z M.w
    Sum.inl Sum.inr (graph s i)
    (GeometricLaw.counting (s.P i) (GeometricLaw.card_pos _ _ (s.good i).positive).1)
    (GeometricLaw.counting (s.Q i) (GeometricLaw.card_pos _ _ (s.good i).positive).2)
    (fun p q hp => M.unit_identity p q (support s i p q hp)) (positive s i)
    (fun p => by
      rw [graph,GeometricLaw.left_eq]
      simpa only [GeometricLaw.counting,mul_one_div] using (s.good i).atomP p p.property)
    (fun q => by
      rw [graph,GeometricLaw.right_eq]
      simpa only [GeometricLaw.counting,mul_one_div] using (s.good i).atomQ q q.property)
    (s.ξ i) (s.good i).error_nonneg hi
    (GeometricLaw.expansion _ _ (s.good i).positive (s.good i).expansion)
    a.epsilon a.epsilon a.d a.epsilon_pos a.epsilon_pos a.d_pos (by linarith) hscale
    a.m (length s a i) a.m_pos (length_pos s a i)
  obtain ⟨hm,u,n,hn,g,l,hfrac,hS,hM,hcard,hstable,hrare,hWC,hWB,hH,hJ,hW,hEP⟩ := ht
  let R : Realization s a i := ⟨n,hn,hm,u,g,l⟩
  have hR : R.Valid C L := by
    as_aux_lemma =>
      refine ⟨hfrac,hS,hM,hcard,hstable,hrare,hWC,hWB,hH,hJ,hW,?_⟩
      have he := information_eq s i
      dsimp only [BoundedScaleFinite.information] at he
      rw [he] at hEP
      exact hEP
  exact ⟨R,hR⟩
end
end PlanarUnitDistances.IncidenceBook

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.IncidenceBook.constants_oai := @OAI.PlanarUnitDistances.IncidenceBook.constants_oai
