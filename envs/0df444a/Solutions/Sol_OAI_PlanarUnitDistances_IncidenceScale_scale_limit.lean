-- Prove2me | solution 1 for OAI.PlanarUnitDistances.IncidenceScale.scale_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T03:03:29.400729+00:00
-- url     : https://prove2.me/submissions/cbcdcdd0-7a1f-4dfe-a193-2a1019d437da

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000

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
lemma pair_union (μ : Law X) (P : X → Prop) :
    event (pair μ μ) (fun x => P x.1 ∨ P x.2)  ≤  2*event μ P := by
  classical
  have h := event_union_le (pair μ μ) (fun x => P x.1) (fun x => P x.2)
  have h₁ : event (pair μ μ) (fun x => P x.1) = event μ P := by
    rw [← avg_ite (pair μ μ) (fun x => P x.1), ← avg_ite μ P]
    exact pair_fst μ μ (fun x => if P x then 1 else 0)
  have h₂ : event (pair μ μ) (fun x => P x.2) = event μ P := by
    rw [← avg_ite (pair μ μ) (fun x => P x.2), ← avg_ite μ P]
    exact pair_snd μ μ (fun x => if P x then 1 else 0)
  rw [h₁,h₂] at h
  linarith
end
end PlanarUnitDistances.FiniteLaw

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

lemma cond_tower (μ : Law X) (φ : X → Y) (f : X → ℝ) :
    avg (push μ φ) (fun y => avg (cond μ φ y) f) = avg μ f := by
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
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma event_congr (μ : Law X) {P Q : X → Prop} (h : ∀ x,P x ↔ Q x) :
    event μ P=event μ Q := le_antisymm (event_mono μ (fun x => (h x).mp))
      (event_mono μ (fun x => (h x).mpr))

lemma event_true (μ : Law X) : event μ (fun _ => True)=1 := by
  simp [event,avg_const]
lemma event_false (μ : Law X) : event μ (fun _ => False)=0 := by
  simp [event,avg_const]

lemma event_exists_le (μ : Law X) (P : I → X → Prop) :
    event μ (fun x => ∃ i,P i x) ≤ ∑ i,event μ (P i) := by
  classical
  unfold event avg
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
  dsimp only
  split_ifs with hx
  · obtain ⟨i,hi⟩ := hx
    have := single_le_sum (s := univ) (f := fun i => if P i x then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa only [hi,ite_true] using this
  · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma avg_sum (μ : Law X) (f : I → X → ℝ) :
    avg μ (fun x => ∑ i,f i x) = ∑ i,avg μ (f i) := by
  simp only [avg,mul_sum]
  rw [sum_comm]

end
end PlanarUnitDistances.FiniteLaw

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

lemma dependent_avg (μ : Law X) (ν : X → Law Y) (f : X×Y → ℝ) :
    avg (dependent μ ν) f = avg μ (fun x => avg (ν x) (fun y => f (x,y))) := by
  simp [avg,dependent,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma mix_avg (μ : Law X) (ν : X → Law Y) (f : Y → ℝ) :
    avg (mix μ ν) f = avg μ (fun x => avg (ν x) f) := by
  simp only [avg,mix,sum_mul,mul_sum,mul_assoc]
  rw [sum_comm]

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
lemma row_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (left π).val p*(row π p).val q=π.val (p,q) := by
  simp only [row,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.2=q then fiberMass π Prod.fst p*(cond π Prod.fst p).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma col_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (right π).val q*(col π q).val p=π.val (p,q) := by
  simp only [col,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.1=p then fiberMass π Prod.snd q*(cond π Prod.snd q).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma row_val (π : Law (P×Q)) {p : P} (hp : 0<(left π).val p) (q : Q) :
    (row π p).val q=π.val (p,q)/(left π).val p := by
  apply (eq_div_iff hp.ne').mpr
  simpa only [mul_comm] using row_weight π p q
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

namespace PlanarUnitDistances.IncidenceEntropy
open Finset Real FiniteInformation
variable {P Q : Type*} [Fintype P] [Fintype Q]

omit [Fintype Q] in
lemma degree_nonneg (E : P → Q → Prop) (q : Q) : 0 ≤ degree E q :=
  sum_nonneg fun p _ => indicator_nonneg E p q

lemma edgeCount_nonneg (E : P → Q → Prop) : 0 ≤ edgeCount E :=
  sum_nonneg fun q _ => degree_nonneg E q

lemma wedge_nonneg (E : P → Q → Prop) (x : P × P) : 0 ≤ wedge E x := by
  unfold wedge
  exact sum_nonneg fun q _ => div_nonneg
    (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
    (mul_nonneg (edgeCount_nonneg E) (degree_nonneg E _))

lemma pointLaw_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) : ∑ p, pointLaw E p = 1 := by
  unfold pointLaw
  rw [← sum_div, sum_comm]
  exact div_self hE

lemma wedge_fst (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) (p : P) :
    ∑ r, wedge E (p,r) = pointLaw E p := by
  unfold wedge pointLaw
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro q _
  dsimp only
  rw [← sum_div, ← mul_sum]
  change indicator E p q * degree E q / (edgeCount E * degree E q) = _
  exact mul_div_mul_right _ _ (hd q)

lemma wedge_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) (hd : ∀ q, degree E q ≠ 0) :
    ∑ x, wedge E x = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [wedge_fst E hd]
  exact pointLaw_sum E hE

end PlanarUnitDistances.IncidenceEntropy

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
lemma row_eq (E : P → Q → Prop) (hE : 0<edgeCount E) {p : P}
    (hp : 0<∑q,indicator E p q) (q : Q) :
    (row (law E hE) p).val q=indicator E p q/(∑q,indicator E p q) := by
  rw [row_val (law E hE) (by rw [left_eq]; exact div_pos hp hE),left_eq]
  change (indicator E p q/edgeCount E)/((∑q,indicator E p q)/edgeCount E)=_
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
lemma row_le (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) (q : Q)
    (hp : 0<CircleIncidence.degree Q p) :
    (row (graph P Q he) p).val q ≤ 1/CircleIncidence.degree Q p := by
  rw [graph,UniformGraphLaw.row_eq _ _ (by rw [row_count]; exact hp),row_count]
  apply div_le_div_of_nonneg_right _ hp.le
  unfold IncidenceEntropy.indicator
  split_ifs <;> norm_num

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

lemma Good.information_nonneg {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) : 0 ≤ information P Q := by
  have he : IncidenceEntropy.edgeCount (GeometricLaw.E P Q) ≠ 0 := by
    rw [GeometricLaw.edgeCount_eq]; exact h.positive.ne'
  have hd : ∀q : Q,IncidenceEntropy.degree (GeometricLaw.E P Q) q ≠ 0 := by
    intro q; rw [GeometricLaw.degree_eq]; exact (h.center_degree_pos q).ne'
  have hp : ∀p : P,0 < IncidenceEntropy.pointLaw (GeometricLaw.E P Q) p := by
    intro p
    rw [IncidenceEntropy.pointLaw,GeometricLaw.row_count,GeometricLaw.edgeCount_eq]
    exact div_pos (h.point_degree_pos p) h.positive
  exact FiniteInformation.KL_nonneg _ _ (IncidenceEntropy.wedge_nonneg _)
    (fun pr => (mul_pos (hp pr.1) (hp pr.2)).le) (IncidenceEntropy.wedge_sum _ he hd)
    (by rw [Fintype.sum_prod_type,←Finset.sum_mul_sum,IncidenceEntropy.pointLaw_sum _ he,one_mul])
    (fun pr _ => (mul_pos (hp pr.1) (hp pr.2)).ne')

lemma Sequence.tendsto (s : Sequence) : Tendsto s.t atTop atTop :=
  tendsto_atTop_mono (fun i => (by linarith [s.large i] : (i:ℝ) ≤ s.t i))
    tendsto_natCast_atTop_atTop

lemma Sequence.accuracy_limit : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma Sequence.error_limit (s : Sequence) : Tendsto s.ξ atTop (nhds 0) :=
  squeeze_zero (fun i => (s.good i).error_nonneg) (fun i => (s.good i).error_le)
    Sequence.accuracy_limit

lemma Sequence.information_limit (s : Sequence) :
    Tendsto (fun i => information (s.P i) (s.Q i)/Real.log (s.t i)) atTop (nhds 0) := by
  apply squeeze_zero (fun i => div_nonneg (s.good i).information_nonneg
    (Real.log_nonneg (by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i])))
    (fun i => (s.good i).info) Sequence.accuracy_limit

end
end PlanarUnitDistances.IncidenceSequence

namespace PlanarUnitDistances.CommonFieldModel
open scoped Classical
noncomputable section
variable (P Q : Finset Plane)

variable {P Q}

namespace Model
variable (M : Model P Q)
lemma point_injective : Function.Injective (M.z ∘ Sum.inl) := by
  intro p r h
  apply Subtype.val_injective
  apply UnitCodegree.zCoordinate.injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inl] using hh
lemma center_injective : Function.Injective (M.z ∘ Sum.inr) := by
  intro q r h
  apply Subtype.val_injective
  apply UnitCodegree.zCoordinate.injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inr] using hh
lemma unit_identity (p : P) (q : Q) (h : dist (p:Plane) (q:Plane)=1) :
    (M.z (.inl p)-M.z (.inr q))*(M.w (.inl p)-M.w (.inr q))=1 := by
  apply Subtype.val_injective
  change ((M.z (.inl p):ℂ)-(M.z (.inr q):ℂ))*((M.w (.inl p):ℂ)-(M.w (.inr q):ℂ))=1
  simp only [M.z_eq,M.w_eq,location,Sum.elim_inl,Sum.elim_inr]
  exact UnitCodegree.unit_distance_equation _ _ (by
    rw [UnitCodegree.zCoordinate.dist_map,dist_comm]; exact h)

lemma sub_mem (v r : P⊕Q) : M.z v-M.z r ∈ M.support :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(v,r),Finset.mem_univ _,rfl⟩))
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

namespace PlanarUnitDistances.LabelFromMatching
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q A : Type} [Fintype P] [Fintype Q] [Fintype A]

omit [Fintype A] in
lemma pair_mismatch (μ : Law P) (a : P → A) (l : A) :
    event (pair μ μ) (fun pp => a pp.1 ≠ a pp.2)  ≤  2*event μ (fun p => a p ≠ l) := by
  classical
  calc
    _  ≤  event (pair μ μ) (fun pp => a pp.1 ≠ l ∨ a pp.2 ≠ l) :=
      event_mono _ (fun pp h => by by_contra hn; simp only [not_or,not_not] at hn; exact h (hn.1.trans hn.2.symm))
    _ ≤ _ := pair_union μ (fun p => a p ≠ l)

omit [Fintype A] in
lemma control {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (π : Law (P×Q)) (a : P → A) (b : Q → A)
    (hm : event π (fun pq => a pq.1 ≠ b pq.2) ≤ s →
      ∃l,event (left π) (fun p => a p ≠ l)+event (right π) (fun q => b q ≠ l) ≤ C*event π (fun pq => a pq.1 ≠ b pq.2)) :
    event (pair (left π) (left π)) (fun pp => a pp.1 ≠ a pp.2)  ≤
      (2*C+1/s)*event π (fun pq => a pq.1 ≠ b pq.2) := by
  have h0 := event_nonneg π (fun pq => a pq.1 ≠ b pq.2)
  by_cases h : event π (fun pq => a pq.1 ≠ b pq.2) ≤ s
  · obtain ⟨l,hl⟩ := hm h
    have hb := pair_mismatch (left π) a l
    have hz := event_nonneg (right π) (fun q => b q ≠ l)
    have hi : 0 ≤ (1/s)*event π (fun pq => a pq.1 ≠ b pq.2) := mul_nonneg (by positivity) h0
    nlinarith
  · have hb := event_le_one (pair (left π) (left π)) (fun pp => a pp.1 ≠ a pp.2)
    have hd : 1 ≤ (1/s)*event π (fun pq => a pq.1 ≠ b pq.2) := by rw [one_div,mul_comm,←div_eq_mul_inv]; exact (le_div_iff₀ hs).2 (by linarith)
    have hc : 0 ≤ 2*C*event π (fun pq => a pq.1 ≠ b pq.2) := by positivity
    nlinarith

end
end PlanarUnitDistances.LabelFromMatching

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

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma abs_log_eq_posLog_add (r : ℝ) : |log r| = log⁺ r + log⁺ r⁻¹ := by
  have h := (half_mul_log_add_log_abs (x := r))
  have h' := (posLog_sub_posLog_inv (x := r))
  linarith

lemma weighted_abs_log_eq_twice {x : K} (_hx : x ≠ 0) :
    ((∑ σ : K →ₐ[ℚ] ℂ, |log (infiniteEntry K σ x)|) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), |log (finiteEntry K v.1 v.2 x)|)) /
        (Module.finrank ℚ K : ℝ) = 2 * exactHeight K x := by
  have harch : (∑ σ : K →ₐ[ℚ] ℂ, |log (infiniteEntry K σ x)|) =
    (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
      (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x⁻¹)) := by
    simp only [abs_log_eq_posLog_add, map_inv₀,sum_add_distrib]
  have hfin : (∑ᶠ v : Nat.Primes × Gal(K/ℚ), |log (finiteEntry K v.1 v.2 x)|) =
    (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x⁻¹)) := by
    simp only [abs_log_eq_posLog_add]
    simpa only [map_inv₀] using
      finsum_add_distrib (finite_posLog_support K x) (finite_posLog_support K x⁻¹)
  rw [harch,hfin]
  have := exactHeight_inv K x
  unfold exactHeight at this ⊢
  simp only [add_div] at this ⊢
  linarith

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

lemma tail_le_gridMismatch {r : ℝ} (hr : 0 < r) (z w : ℂ) (u : ℝ × ℝ) :
    (if 2*r < ‖z-w‖ then (1:ℝ) else 0) ≤ gridMismatch r z w u := by
  unfold gridMismatch
  split_ifs with hd hg
  · exact (not_le_of_gt hd (norm_le_of_same_grid hr hg)).elim
  all_goals norm_num

end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set Real
noncomputable section

lemma kernel_continuous (a : ℝ) : Continuous (fun s : ℝ => min 1 (a*exp (-s))) :=
  continuous_const.min (continuous_const.mul (Real.continuous_exp.comp continuous_neg))

lemma exp_neg_posLog_control {a : ℝ} (ha : 0 ≤ a) : a*exp (-log⁺ a) ≤ 1 := by
  rw [posLog_eq_log_max_one ha,exp_neg,exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
  rw [← div_eq_mul_inv,div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
  exact le_max_right _ _

lemma kernel_integral_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    (∫ s in (0:ℝ)..T, min 1 (a*exp (-s))) ≤ log⁺ a+1 := by
  have hk (x y : ℝ) : IntervalIntegrable (fun s => min 1 (a*exp (-s))) volume x y :=
    (kernel_continuous a).intervalIntegrable x y
  have he : Continuous (fun s : ℝ => a*exp (-s)) := continuous_const.mul (Real.continuous_exp.comp continuous_neg)
  by_cases h : T ≤ log⁺ a
  · calc
      _ ≤ ∫ _s in (0:ℝ)..T, (1:ℝ) := intervalIntegral.integral_mono_on hT
        (hk _ _) (continuous_const.intervalIntegrable _ _) (fun s _ => min_le_left _ _)
      _ = T := by simp
      _ ≤ log⁺ a+1 := by linarith
  · have hc : log⁺ a ≤ T := (lt_of_not_ge h).le
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := log⁺ a) (c := T) (hk _ _) (hk _ _)]
    have h₁ : (∫ s in (0:ℝ)..log⁺ a, min 1 (a*exp (-s))) ≤ log⁺ a := by
      calc
        _ ≤ ∫ _s in (0:ℝ)..log⁺ a, (1:ℝ) := intervalIntegral.integral_mono_on posLog_nonneg
          (hk _ _) (continuous_const.intervalIntegrable _ _) (fun s _ => min_le_left _ _)
        _ = log⁺ a := by simp
    have h₂ : (∫ s in log⁺ a..T, min 1 (a*exp (-s))) ≤ 1 := by
      calc
        _ ≤ ∫ s in log⁺ a..T, a*exp (-s) := intervalIntegral.integral_mono_on hc
          (hk _ _) (he.intervalIntegrable _ _) (fun s _ => min_le_right _ _)
        _ = a*(exp (-log⁺ a)-exp (-T)) := by
          rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp]
        _ ≤ a*exp (-log⁺ a) := by nlinarith [exp_pos (-T)]
        _ ≤ 1 := exp_neg_posLog_control ha
    linarith

lemma kernel_setIntegral_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    (∫ s in Icc 0 T, min 1 (a*exp (-s))) ≤ log⁺ a+1 := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT]
  exact kernel_integral_le ha hT

lemma tail_iff_threshold {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    exp s < a ↔ s < log⁺ a := by
  by_cases h : a ≤ 1
  · have hp : log⁺ a = 0 := (posLog_eq_zero_iff _).mpr (by rwa [abs_of_nonneg ha])
    have he : 1 ≤ exp s := (one_le_exp_iff).mpr hs
    simp only [hp]
    constructor <;> intro hc <;> linarith
  · have hp : log⁺ a = log a := posLog_eq_log (by rw [abs_of_nonneg ha]; linarith)
    rw [hp,lt_log_iff_exp_lt (by linarith)]

lemma tail_integrableOn (a T : ℝ) :
    IntegrableOn (fun s : ℝ => if exp s < a then (1:ℝ) else 0) (Icc 0 T) := by
  apply Integrable.of_bound (Measurable.ite
    (measurableSet_lt measurable_exp measurable_const) measurable_const measurable_const).aestronglyMeasurable 1
  filter_upwards [] with s
  split <;> norm_num

lemma tail_setIntegral {a T : ℝ} (ha : 0 ≤ a) (hT : log⁺ a ≤ T) :
    (∫ s in Icc 0 T, if exp s < a then (1:ℝ) else 0) = log⁺ a := by
  have he : ∀ s ∈ Icc 0 T, (if exp s < a then (1:ℝ) else 0) =
      (Ico (0:ℝ) (log⁺ a)).indicator (fun _ => (1:ℝ)) s := by
    intro s hs
    simp only [tail_iff_threshold ha hs.1]
    simp [Set.indicator,hs.1]
  rw [setIntegral_congr_fun measurableSet_Icc he,integral_indicator_const (1:ℝ) measurableSet_Ico,
    measureReal_restrict_apply measurableSet_Ico]
  have hh : Ico (0:ℝ) (log⁺ a) ⊆ Icc 0 T := fun s hs => ⟨hs.1,hs.2.le.trans hT⟩
  rw [inter_eq_left.mpr hh,Real.volume_real_Ico]
  simp [Real.posLog_nonneg,smul_eq_mul]

end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.LocalHeightTransfer
open MeasureTheory Set Real Finset
open PlanarUnitDistances.GridShift
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]

lemma label_control_any {A : Type} [DecidableEq A] {C : ℝ} {w : P → Q → ℝ}
    (hc : LabelControl C w) (L : P ⊕ Q → A) :
    (∑ p, ∑ p', left w p * left w p' * dis (L (.inl p)) (L (.inl p'))) ≤
      C * ∑ p, ∑ q, w p q * dis (L (.inl p)) (L (.inr q)) := by
  classical
  let : Fintype (Set.range L) := Fintype.ofFinite _
  let f : P ⊕ Q → ℕ := fun x => (Fintype.equivFin (Set.range L) ⟨L x,mem_range_self x⟩).val
  have he (x y : P ⊕ Q) : f x = f y ↔ L x = L y := by
    simp only [f,Fin.val_inj,(Fintype.equivFin (Set.range L)).injective.eq_iff,Subtype.mk.injEq]
  simpa only [dis,he] using hc f

omit [Fintype P] in
lemma left_nonneg {w : P → Q → ℝ} (hw : ∀ p q, 0 ≤ w p q) (p : P) :
    0 ≤ left w p := sum_nonneg fun q _ => hw p q

lemma grid_level {C : ℝ} {w : P → Q → ℝ} (hC : 0 ≤ C)
    (hw : ∀ p q, 0 ≤ w p q) (hc : LabelControl C w)
    (z : P ⊕ Q → ℂ) (s : ℝ) :
    (∑ p, ∑ p', left w p * left w p' *
      (if 2*exp s < ‖z (.inl p)-z (.inl p')‖ then (1:ℝ) else 0)) ≤
    C * ∑ p, ∑ q, w p q * min 1 (2*‖z (.inl p)-z (.inr q)‖*exp (-s)) := by
  classical
  let f (u : ℝ × ℝ) := ∑ p, ∑ p', left w p * left w p' *
    gridMismatch (exp s) (z (.inl p)) (z (.inl p')) u
  let g (u : ℝ × ℝ) := ∑ p, ∑ q, w p q *
    gridMismatch (exp s) (z (.inl p)) (z (.inr q)) u
  have hf : Integrable f squareShift := integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun p' _ => (gridMismatch_integrable _ _ _).const_mul _
  have hg : Integrable g squareShift := integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun q _ => (gridMismatch_integrable _ _ _).const_mul _
  have hfg (u : ℝ × ℝ) : f u ≤ C*g u := by
    simpa only [f,g,dis,gridMismatch] using
      label_control_any hc (fun x => gridLabel (exp s) (z x) u)
  have hlow (u : ℝ × ℝ) : (∑ p, ∑ p', left w p * left w p' *
      (if 2*exp s < ‖z (.inl p)-z (.inl p')‖ then (1:ℝ) else 0)) ≤ f u := by
    apply sum_le_sum; intro p _; apply sum_le_sum; intro p' _
    exact mul_le_mul_of_nonneg_left (tail_le_gridMismatch (exp_pos s) _ _ u)
      (mul_nonneg (left_nonneg hw _) (left_nonneg hw _))
  have hig : (∫ u, g u ∂squareShift) =
      ∑ p, ∑ q, w p q * ∫ u, gridMismatch (exp s) (z (.inl p)) (z (.inr q)) u ∂squareShift := by
    simp only [g,integral_finsetSum _ (fun p _ => integrable_finsetSum _
      (fun q _ => (gridMismatch_integrable _ _ _).const_mul _)),
      integral_finsetSum _ (fun q _ => (gridMismatch_integrable _ _ _).const_mul _),
      integral_const_mul]
  have hupper : (∫ u, g u ∂squareShift) ≤
      ∑ p, ∑ q, w p q * min 1 (2*‖z (.inl p)-z (.inr q)‖*exp (-s)) := by
    rw [hig]
    apply sum_le_sum; intro p _; apply sum_le_sum; intro q _
    apply mul_le_mul_of_nonneg_left _ (hw p q)
    simpa only [exp_neg,div_eq_mul_inv] using gridMismatch_integral_le (exp_pos s)
      (z (.inl p)) (z (.inr q))
  calc
    _ = ∫ _u, (∑ p, ∑ p', left w p * left w p' *
      (if 2*exp s < ‖z (.inl p)-z (.inl p')‖ then (1:ℝ) else 0)) ∂squareShift := by simp
    _ ≤ ∫ u, f u ∂squareShift := integral_mono (integrable_const _) hf hlow
    _ ≤ ∫ u, C*g u ∂squareShift := integral_mono hf (hg.const_mul C) hfg
    _ = C * ∫ u, g u ∂squareShift := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper hC

lemma weighted_tails_integrable {A : Type*} [Fintype A] (w x : A → ℝ) (T : ℝ) :
    IntegrableOn (fun s => ∑ a, w a * if exp s < x a then (1:ℝ) else 0) (Icc 0 T) :=
  integrable_finsetSum _ fun a _ => (tail_integrableOn (x a) T).const_mul (w a)

lemma weighted_tails_integral {A : Type*} [Fintype A] (w x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a) {T : ℝ} (hT : ∀ a, log⁺ (x a) ≤ T) :
    (∫ s in Icc 0 T, ∑ a, w a * if exp s < x a then (1:ℝ) else 0) =
      ∑ a, w a * log⁺ (x a) := by
  rw [integral_finsetSum _ (fun a _ => (tail_integrableOn (x a) T).const_mul (w a))]
  apply sum_congr rfl; intro a _
  rw [integral_const_mul,tail_setIntegral (hx a) (hT a)]

lemma weighted_kernel_integrable {A : Type*} [Fintype A] (w x : A → ℝ) (T : ℝ) :
    IntegrableOn (fun s => ∑ a, w a * min 1 (x a*exp (-s))) (Icc 0 T) :=
  integrable_finsetSum _ fun a _ => ((kernel_continuous (x a)).integrableOn_Icc).const_mul (w a)

lemma weighted_kernel_integral_le {A : Type*} [Fintype A] (w x : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hx : ∀ a, 0 ≤ x a) {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in Icc 0 T, ∑ a, w a * min 1 (x a*exp (-s))) ≤
      ∑ a, w a * (log⁺ (x a)+1) := by
  rw [integral_finsetSum _ (fun a _ => ((kernel_continuous (x a)).integrableOn_Icc).const_mul (w a))]
  apply sum_le_sum; intro a _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (kernel_setIntegral_le (hx a) hT) (hw a)

lemma log_two_control (a : ℝ) : log⁺ a ≤ log⁺ (a/2)+log 2 := by
  have h : a = a/2*2 := by ring
  calc
    _ = log⁺ (a/2*2) := congrArg (fun x => log⁺ x) h
    _ ≤ log⁺ (a/2)+log⁺ (2:ℝ) := posLog_mul
    _ = _ := by rw [posLog_eq_log (by norm_num : (1:ℝ) ≤ |2|)]

lemma archimedean_transfer {C : ℝ} {w : P → Q → ℝ} (hC : 0 ≤ C)
    (hw : ∀ p q, 0 ≤ w p q) (hs : ∑ p, ∑ q, w p q = 1)
    (hc : LabelControl C w) (z : P ⊕ Q → ℂ) :
    (∑ p, ∑ p', left w p * left w p' * log⁺ ‖z (.inl p)-z (.inl p')‖) ≤
    C * ((∑ p, ∑ q, w p q * log⁺ ‖z (.inl p)-z (.inr q)‖)+log 2+1)+log 2 := by
  classical
  let a : P × P → ℝ := fun x => ‖z (.inl x.1)-z (.inl x.2)‖/2
  let b : P × Q → ℝ := fun x => 2*‖z (.inl x.1)-z (.inr x.2)‖
  let v : P × P → ℝ := fun x => left w x.1 * left w x.2
  let e : P × Q → ℝ := fun x => w x.1 x.2
  obtain ⟨T,hT⟩ := Finite.exists_le (fun x : P × P => log⁺ (a x))
  let D := max 0 T
  have hD : 0 ≤ D := le_max_left _ _
  have ha (x) : 0 ≤ a x := div_nonneg (norm_nonneg _) (by norm_num)
  have hb (x) : 0 ≤ b x := mul_nonneg (by norm_num) (norm_nonneg _)
  have he (x) : 0 ≤ e x := hw _ _
  have hv (x) : 0 ≤ v x := mul_nonneg (left_nonneg hw _) (left_nonneg hw _)
  have hl (s : ℝ) : (∑ x, v x * if exp s < a x then (1:ℝ) else 0) ≤
      C * ∑ x, e x * min 1 (b x*exp (-s)) := by
    simpa only [Fintype.sum_prod_type,a,b,v,e,lt_div_iff₀ (by norm_num : (0:ℝ)<2),
      mul_comm (exp s) 2] using grid_level hC hw hc z s
  have hi := setIntegral_mono_on (weighted_tails_integrable v a D)
    ((weighted_kernel_integrable e b D).const_mul C) measurableSet_Icc (fun s _ => hl s)
  rw [weighted_tails_integral v a ha (fun x => (hT x).trans (le_max_right _ _)),
    integral_const_mul] at hi
  have hib := hi.trans (mul_le_mul_of_nonneg_left
    (weighted_kernel_integral_le e b he hb hD) hC)
  have hsum : ∑ p, left w p = 1 := hs
  have hvsum : ∑ x, v x = 1 := by
    simp only [v,Fintype.sum_prod_type,← mul_sum,hsum,mul_one]
  have hesum : ∑ x, e x = 1 := by
    change (∑ x : P × Q, w x.1 x.2) = 1
    rw [Fintype.sum_prod_type]; exact hs
  have haBound : (∑ p, ∑ p', left w p * left w p' * log⁺ ‖z (.inl p)-z (.inl p')‖) ≤
      (∑ x, v x * log⁺ (a x))+log 2 := by
    calc
      _ ≤ ∑ p, ∑ p', left w p * left w p' * (log⁺ (a (p,p'))+log 2) := by
        apply sum_le_sum; intro p _; apply sum_le_sum; intro p' _
        exact mul_le_mul_of_nonneg_left (log_two_control _) (hv (p,p'))
      _ = _ := by
        rw [← Fintype.sum_prod_type (fun x : P × P => v x*(log⁺ (a x)+log 2))]
        simp only [mul_add,sum_add_distrib,← sum_mul,hvsum,one_mul]
  have hbBound : (∑ x, e x*(log⁺ (b x)+1)) ≤
      (∑ p, ∑ q, w p q*log⁺ ‖z (.inl p)-z (.inr q)‖)+log 2+1 := by
    calc
      _ ≤ ∑ x, e x * (log⁺ ‖z (.inl x.1)-z (.inr x.2)‖+log 2+1) := by
        apply sum_le_sum; intro x _; apply mul_le_mul_of_nonneg_left _ (he x)
        have hp : log⁺ (b x) ≤ log⁺ ‖z (.inl x.1)-z (.inr x.2)‖+log 2 := by
          have h := posLog_mul (x := 2) (y := ‖z (.inl x.1)-z (.inr x.2)‖)
          rw [posLog_eq_log (by norm_num : (1:ℝ) ≤ |2|)] at h
          simpa only [b,add_comm] using h
        linarith
      _ = _ := by
        simp only [mul_add,sum_add_distrib,← sum_mul,mul_one,hesum,one_mul]
        rw [Fintype.sum_prod_type]
  linarith [mul_le_mul_of_nonneg_left hbBound hC]

lemma nonarchimedean_level {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) {C : ℝ} {w : P → Q → ℝ}
    (hc : LabelControl C w) (z : P ⊕ Q → K) (s : ℝ) :
    (∑ p, ∑ p', left w p * left w p' *
      (if exp s < v (z (.inl p)-z (.inl p')) then (1:ℝ) else 0)) ≤
    C * ∑ p, ∑ q, w p q *
      (if exp s < v (z (.inl p)-z (.inr q)) then (1:ℝ) else 0) := by
  classical
  let R : Setoid (P ⊕ Q) :=
    { r := fun x y => v (z x-z y) ≤ exp s
      iseqv := ⟨by intro x; simpa using (exp_pos s).le,
        by intro x y h; rwa [v.map_sub],
        by
          intro x y z' h₁ h₂
          have he : z x-z z' = (z x-z y)+(z y-z z') := by ring
          rw [he]
          exact (hv _ _).trans (max_le h₁ h₂)⟩ }
  have he (x y : P ⊕ Q) : dis (Quotient.mk R x) (Quotient.mk R y) =
      (if exp s < v (z x-z y) then (1:ℝ) else 0) := by
    simp only [dis,Quotient.eq]
    change (if v (z x-z y) ≤ exp s then (0:ℝ) else 1) = _
    split_ifs <;> norm_num at * <;> linarith
  simpa only [he] using label_control_any hc (Quotient.mk R)

lemma nonarchimedean_transfer {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) {C : ℝ} {w : P → Q → ℝ}
    (hc : LabelControl C w) (z : P ⊕ Q → K) :
    (∑ p, ∑ p', left w p * left w p' * log⁺ (v (z (.inl p)-z (.inl p')))) ≤
    C * ∑ p, ∑ q, w p q * log⁺ (v (z (.inl p)-z (.inr q))) := by
  classical
  let a : P × P → ℝ := fun x => v (z (.inl x.1)-z (.inl x.2))
  let b : P × Q → ℝ := fun x => v (z (.inl x.1)-z (.inr x.2))
  let μ : P × P → ℝ := fun x => left w x.1 * left w x.2
  let e : P × Q → ℝ := fun x => w x.1 x.2
  obtain ⟨T,hT⟩ := Finite.exists_le (fun x : P × P => log⁺ (a x))
  obtain ⟨S,hS⟩ := Finite.exists_le (fun x : P × Q => log⁺ (b x))
  let D := max T S
  have hl (s : ℝ) : (∑ x, μ x * if exp s < a x then (1:ℝ) else 0) ≤
      C * ∑ x, e x * if exp s < b x then (1:ℝ) else 0 := by
    simpa only [Fintype.sum_prod_type,a,b,μ,e] using nonarchimedean_level v hv hc z s
  have hi := setIntegral_mono_on (weighted_tails_integrable μ a D)
    ((weighted_tails_integrable e b D).const_mul C) measurableSet_Icc (fun s _ => hl s)
  rw [weighted_tails_integral μ a (fun x => v.nonneg _) (fun x => (hT x).trans (le_max_left _ _)),
    integral_const_mul,weighted_tails_integral e b (fun x => v.nonneg _)
      (fun x => (hS x).trans (le_max_right _ _))] at hi
  simpa only [Fintype.sum_prod_type,a,b,μ,e] using hi

lemma control_nonneg {C : ℝ} {w : P → Q → ℝ}
    (hs : ∑ p, ∑ q, w p q = 1) (hc : LabelControl C w) : 0 ≤ C := by
  have h := hc (fun x => match x with | .inl _ => 0 | .inr _ => 1)
  simpa only [dis,ite_true,mul_zero,sum_const_zero,show (0:ℕ) ≠ 1 by omega,ite_false,mul_one,hs] using h

end
end PlanarUnitDistances.LocalHeightTransfer

namespace PlanarUnitDistances.HeightTransfer
open Finset Real
open PlanarUnitDistances.WeightedAbsoluteValues
open PlanarUnitDistances.LocalHeightTransfer
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in
lemma weighted_finite_support {A : Type*} [Fintype A] (w : A → ℝ) (x : A → K) :
    Function.HasFiniteSupport (fun v : Nat.Primes × Gal(K/ℚ) =>
      ∑ a, w a*log⁺ (finiteEntry K v.1 v.2 (x a))) :=
  Function.HasFiniteSupport.sum (fun a => (finite_posLog_support K (x a)).mul_right (fun _ => w a)) univ

omit [IsGalois ℚ K] in
lemma weighted_height_identity {A : Type*} [Fintype A] (w : A → ℝ) (x : A → K) :
    (∑ a, w a * exactHeight K (x a)) =
      ((∑ σ : K →ₐ[ℚ] ℂ, ∑ a, w a*log⁺ (infiniteEntry K σ (x a))) +
       (∑ᶠ v : Nat.Primes × Gal(K/ℚ), ∑ a, w a*log⁺ (finiteEntry K v.1 v.2 (x a)))) /
        (Module.finrank ℚ K : ℝ) := by
  classical
  have ha : (∑ σ : K →ₐ[ℚ] ℂ, ∑ a, w a*log⁺ (infiniteEntry K σ (x a))) =
      ∑ a, w a*∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ (x a)) := by
    rw [sum_comm]; simp only [mul_sum]
  have hf : (∑ᶠ v : Nat.Primes × Gal(K/ℚ), ∑ a, w a*log⁺ (finiteEntry K v.1 v.2 (x a))) =
      ∑ a, w a*∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 (x a)) := by
    have hfs (a : A) : Function.HasFiniteSupport
        (fun v : Nat.Primes × Gal(K/ℚ) => w a * log⁺ (finiteEntry K v.1 v.2 (x a))) :=
      (finite_posLog_support K (x a)).mul_right (fun _ => w a)
    have hi := finsum_sum_comm (α := Nat.Primes × Gal(K/ℚ)) (β := A) (M := ℝ)
      univ (fun (v : Nat.Primes × Gal(K/ℚ)) (a : A) => w a*log⁺ (finiteEntry K v.1 v.2 (x a)))
      (fun a _ => hfs a)
    change (∑ᶠ v : Nat.Primes × Gal(K/ℚ), ∑ a, w a*log⁺ (finiteEntry K v.1 v.2 (x a))) =
      ∑ a, ∑ᶠ v : Nat.Primes × Gal(K/ℚ), w a*log⁺ (finiteEntry K v.1 v.2 (x a)) at hi
    rw [hi]
    apply sum_congr rfl; intro a _
    exact (mul_finsum _ _).symm
  rw [ha,hf,← sum_add_distrib,sum_div]
  apply sum_congr rfl; intro a _
  rw [← mul_add,mul_div_assoc]
  rfl

variable {P Q : Type} [Fintype P] [Fintype Q]

omit [IsGalois ℚ K] in
theorem height_transfer {C : ℝ} {w : P → Q → ℝ}
    (hw : ∀ p q, 0 ≤ w p q) (hs : ∑ p, ∑ q, w p q = 1)
    (hc : LabelControl C w) (U : P ⊕ Q → K) :
    (∑ p, ∑ p', left w p * left w p' * exactHeight K (U (.inl p)-U (.inl p'))) ≤
    ((C+1)*(log 2+2)) * ((∑ p, ∑ q, w p q*exactHeight K (U (.inl p)-U (.inr q)))+1) := by
  classical
  have hC := control_nonneg hs hc
  let a : P × P → K := fun x => U (.inl x.1)-U (.inl x.2)
  let b : P × Q → K := fun x => U (.inl x.1)-U (.inr x.2)
  let μ : P × P → ℝ := fun x => left w x.1 * left w x.2
  let e : P × Q → ℝ := fun x => w x.1 x.2
  let A : (K →ₐ[ℚ] ℂ) → ℝ := fun σ => ∑ x, μ x*log⁺ (infiniteEntry K σ (a x))
  let B : (K →ₐ[ℚ] ℂ) → ℝ := fun σ => ∑ x, e x*log⁺ (infiniteEntry K σ (b x))
  let F : Nat.Primes × Gal(K/ℚ) → ℝ := fun v => ∑ x, μ x*log⁺ (finiteEntry K v.1 v.2 (a x))
  let G : Nat.Primes × Gal(K/ℚ) → ℝ := fun v => ∑ x, e x*log⁺ (finiteEntry K v.1 v.2 (b x))
  have harch (σ : K →ₐ[ℚ] ℂ) : A σ ≤ C*(B σ+log 2+1)+log 2 := by
    simpa only [A,B,a,b,μ,e,Fintype.sum_prod_type,infiniteEntry_apply,map_sub] using
      archimedean_transfer hC hw hs hc (fun v => σ (U v))
  have hfinite (v : Nat.Primes × Gal(K/ℚ)) : F v ≤ C*G v := by
    simpa only [F,G,a,b,μ,e,Fintype.sum_prod_type] using
      nonarchimedean_transfer (finiteEntry K v.1 v.2) (finiteEntry_nonarch K v.1 v.2) hc U
  have ha : (∑ σ, A σ) ≤ C*(∑ σ, B σ) +
      (Module.finrank ℚ K : ℝ)*(C*(log 2+1)+log 2) := by
    calc
      _ ≤ ∑ σ, (C*(B σ+log 2+1)+log 2) := sum_le_sum fun σ _ => harch σ
      _ = _ := by
        simp only [mul_add,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_univ,infiniteEntry_count]
        ring
  have hf : (∑ᶠ v, F v) ≤ C*∑ᶠ v, G v := by
    have h := finsum_le_finsum' (weighted_finite_support K μ a)
      ((weighted_finite_support K e b).mul_right (fun _ => C)) hfinite
    simpa only [Pi.mul_apply,← mul_finsum,F,G] using h
  have ht : (∑ x, μ x*exactHeight K (a x)) ≤ C*(∑ x, e x*exactHeight K (b x))+
      C*(log 2+1)+log 2 := by
    rw [weighted_height_identity,weighted_height_identity]
    change ((∑ σ,A σ)+(∑ᶠ v,F v))/(Module.finrank ℚ K : ℝ) ≤
      C*(((∑ σ,B σ)+(∑ᶠ v,G v))/(Module.finrank ℚ K : ℝ))+C*(log 2+1)+log 2
    have hp := finrank_pos K
    calc
      _ ≤ (C*(∑ σ,B σ)+(Module.finrank ℚ K : ℝ)*(C*(log 2+1)+log 2)+
          C*(∑ᶠ v,G v))/(Module.finrank ℚ K : ℝ) :=
        div_le_div_of_nonneg_right (add_le_add ha hf) hp.le
      _ = _ := by field_simp; ring
  have he_nonneg : 0 ≤ ∑ x, e x*exactHeight K (b x) := sum_nonneg fun x _ =>
    mul_nonneg (hw _ _) (exactHeight_nonneg K _)
  have hl : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hprod : 0 ≤ C*log (2:ℝ) := mul_nonneg hC hl
  have hconst : C ≤ (C+1)*(log 2+2) := by nlinarith
  have hend : (∑ x, μ x*exactHeight K (a x)) ≤
      ((C+1)*(log 2+2))*((∑ x,e x*exactHeight K (b x))+1) := by
    have hm := mul_le_mul_of_nonneg_right hconst he_nonneg
    nlinarith only [ht,hm,hC,hl]
  simpa only [Fintype.sum_prod_type,a,b,μ,e] using hend

end
end PlanarUnitDistances.HeightTransfer

namespace PlanarUnitDistances.GlobalLabelControl
open FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section

theorem constants {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃ξ₀ C : ℝ,0<ξ₀ ∧ 0<C ∧
    ∀(P Q : Type) [Fintype P] [Fintype Q],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,γ*U.val p≤(left π).val p) → (∀q,γ*W.val q≤(right π).val q) →
    ∀ξ,0≤ξ → ξ≤ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    LocalHeightTransfer.LabelControl C (fun p q => π.val (p,q)) := by
  obtain ⟨s,ξ₀,C,hs,hξ,hC,hm⟩ := LawExpansion.matching hγ hη
  refine ⟨ξ₀,2*C+1/s,hξ,by positivity,?_⟩
  intro P Q _ _ π U W hl hr ξ hξ0 hξb hexp L
  let A := Set.range L
  let : Fintype A := Fintype.ofFinite A
  let f : P⊕Q → A := fun v => ⟨L v,Set.mem_range_self v⟩
  have heq (v r : P⊕Q) : f v ≠ f r ↔ L v ≠ L r := by
    simp only [f,ne_eq,Subtype.mk.injEq]
  have hh := LabelFromMatching.control hs hC.le π (f ∘ Sum.inl) (f ∘ Sum.inr)
    (hm P Q A π U W (f ∘ Sum.inl) (f ∘ Sum.inr) hl hr ξ hξ0 hξb hexp)
  simp only [Function.comp_apply,heq] at hh
  have hlv (p : P) : LocalHeightTransfer.left (fun p q => π.val (p,q)) p=(left π).val p :=
    LawExpansion.left_val π p
  simpa only [event,avg,pair,Fintype.sum_prod_type,LocalHeightTransfer.dis,
    hlv,mul_ite,mul_one,mul_zero,ite_not] using hh
end
end PlanarUnitDistances.GlobalLabelControl

namespace PlanarUnitDistances.ActualHeightTransfer
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]

lemma pair_height (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    {C : ℝ} (π : Law (P×Q)) (hc : LocalHeightTransfer.LabelControl C (fun p q => π.val (p,q)))
    (U : P⊕Q  →  K) :
    avg (pair (left π) (left π)) (fun pp => WeightedAbsoluteValues.exactHeight K (U (.inl pp.1)-U (.inl pp.2)))  ≤
    ((C+1)*(Real.log 2+2))*(avg π (fun pq => WeightedAbsoluteValues.exactHeight K (U (.inl pq.1)-U (.inr pq.2)))+1) := by
  have hb:=HeightTransfer.height_transfer K (fun p q => π.nonneg (p,q)) (LawExpansion.total π) hc U
  have hl (p : P) : LocalHeightTransfer.left (fun p q => π.val (p,q)) p=(left π).val p := LawExpansion.left_val π p
  simpa only [avg,pair,Fintype.sum_prod_type,hl] using hb
end
end PlanarUnitDistances.ActualHeightTransfer

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
variable {X : Type*} [Fintype X]
lemma exists_le_average (μ : Law X) (f : X → ℝ) : ∃x,f x≤avg μ f := by
  classical
  have : Nonempty X := by
    by_contra hn
    have : IsEmpty X := not_nonempty_iff.mp hn
    have hh:=μ.total
    simp at hh
  obtain ⟨x,_,hx⟩:=exists_min_image univ f univ_nonempty
  exact ⟨x,(avg_const μ (f x)).symm.trans_le (avg_mono μ (fun y => hx y (mem_univ y)))⟩
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_States
attribute [-instance] _root_.OAI.PlanarUnitDistances.LevelScale.instIsFiniteMeasureProdPlaceRealMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.NormalizedCoordinates
open Finset FiniteLaw FiniteStarCoupling WeightedAbsoluteValues
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma center_height (π : Law (P×Q)) (z : P⊕Q → K) (a : K) :
    avg (right π) (fun q => exactHeight K (z (.inr q)-a)) ≤
      Real.log 2+avg (left π) (fun p => exactHeight K (z (.inl p)-a))+
        avg π (fun pq => exactHeight K (z (.inl pq.1)-z (.inr pq.2))) := by
  have hb:=avg_mono π (fun pq => exactHeight_add_le K (z (.inl pq.1)-a) (-(z (.inl pq.1)-z (.inr pq.2))))
  have he (pq : P×Q) : (z (.inl pq.1)-a)+(-(z (.inl pq.1)-z (.inr pq.2)))=z (.inr pq.2)-a := by ring
  simp only [he,exactHeight_neg,avg_add,avg_const] at hb
  simpa only [left,right,push_avg] using hb

theorem translate (π : Law (P×Q)) {C S : ℝ}
    (hc : LocalHeightTransfer.LabelControl C (fun p q => π.val (p,q)))
    (z w : P⊕Q → K)
    (hz : avg π (fun pq => exactHeight K (z (.inl pq.1)-z (.inr pq.2)))≤S)
    (hw : avg π (fun pq => exactHeight K (w (.inl pq.1)-w (.inr pq.2)))≤S) :
    ∃p₀ : P,
      avg (left π) (fun p => exactHeight K (z (.inl p)-z (.inl p₀))+exactHeight K (w (.inl p)-w (.inl p₀)))+
      avg (right π) (fun q => exactHeight K (z (.inr q)-z (.inl p₀))+exactHeight K (w (.inr q)-w (.inl p₀)))+
      avg π (fun pq => exactHeight K (z (.inl pq.1)-z (.inr pq.2))+exactHeight K (w (.inl pq.1)-w (.inr pq.2))) ≤
        4*((C+1)*(Real.log 2+2))*(S+1)+4*S+2*Real.log 2 := by
  let μ:=left π
  let F : P → ℝ:=fun r => avg μ (fun p => exactHeight K (z (.inl p)-z (.inl r))+exactHeight K (w (.inl p)-w (.inl r)))
  obtain ⟨p₀,hp⟩:=exists_le_average μ F
  have hF : avg μ F=
      avg (pair μ μ) (fun pp => exactHeight K (z (.inl pp.1)-z (.inl pp.2)))+
      avg (pair μ μ) (fun pp => exactHeight K (w (.inl pp.1)-w (.inl pp.2))) := by
    rw [←avg_add,pair_avg]
    simp only [F,avg,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    ring
  rw [hF] at hp
  have hC:=LocalHeightTransfer.control_nonneg (LawExpansion.total π) hc
  have hL : 0≤(C+1)*(Real.log 2+2) := mul_nonneg (by linarith) (by have := Real.log_nonneg (show (1:ℝ)≤2 by norm_num); linarith)
  have hpz:=(ActualHeightTransfer.pair_height K π hc z).trans (mul_le_mul_of_nonneg_left (show _ ≤ S+1 by linarith) hL)
  have hpw:=(ActualHeightTransfer.pair_height K π hc w).trans (mul_le_mul_of_nonneg_left (show _ ≤ S+1 by linarith) hL)
  have hqz:=center_height K π z (z (.inl p₀))
  have hqw:=center_height K π w (w (.inl p₀))
  refine ⟨p₀,?_⟩
  simp only [avg_add] at *
  dsimp only [F,μ] at hp
  simp only [avg_add] at hp
  linarith
end
end PlanarUnitDistances.NormalizedCoordinates

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

namespace PlanarUnitDistances.PlaceLevels
open Finset Real WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

lemma log_off_support {S : Finset K} {x : K} (hx : x∈S)
    {v : Nat.Primes × Gal(K/ℚ)} (hv : v∉finiteSupport K S) :
    log (finiteEntry K v.1 v.2 x)=0 := by
  by_cases h0 : x=0
  · simp [h0]
  have hp : v.1.val ∉ rootDenominators K x ∪ rootDenominators K x⁻¹ := by
    intro hh
    apply hv
    exact mem_biUnion.mpr ⟨x,hx,mem_product.mpr ⟨mem_subtype.mpr hh,mem_univ _⟩⟩
  rw [finiteEntry_eq_one_off_support K h0 _ _ hp,log_one]

lemma log_le_radius {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    |log (av K v x)|≤radius K S v := by
  exact single_le_sum (fun y _ => abs_nonneg (log (av K v y))) hx
lemma threshold_in_range {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    -radius K S v ≤ -log (av K v x) ∧ -log (av K v x) ≤ radius K S v := by
  have h := abs_le.mp (log_le_radius K hx v)
  constructor <;> linarith
end
end PlanarUnitDistances.PlaceLevels

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma bit_nonneg (a s : ℝ) : 0 ≤ bit a s := by unfold bit; split <;> norm_num
lemma bit_le_one (a s : ℝ) : bit a s ≤ 1 := by unfold bit; split <;> norm_num
lemma bit_measurable (a : ℝ) : Measurable (bit a) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

lemma bit_integrableOn (a l u : ℝ) : IntegrableOn (bit a) (Icc l u) := by
  have he : bit a = (Iio a).indicator (fun _ => (1 : ℝ)) := by
    funext s; simp [bit,Set.indicator]
  rw [he]
  exact (show Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc l u))
    from continuous_const.integrableOn_Icc).indicator measurableSet_Iio

lemma abs_bit_sub_eq (a b s : ℝ) :
    |bit a s - bit b s| = (Ico (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) s := by
  by_cases ha : s < a <;> by_cases hb : s < b <;>
    simp [bit,ha,hb,Set.indicator,mem_Ico]

lemma bit_sub_integral {l u a b : ℝ} (hla : l ≤ a) (hua : a ≤ u)
    (hlb : l ≤ b) (hub : b ≤ u) :
    ∫ s in Icc l u, |bit a s - bit b s| = |a-b| := by
  simp_rw [abs_bit_sub_eq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  rw [measureReal_restrict_apply measurableSet_Ico]
  have hsub : Ico (min a b) (max a b) ⊆ Icc l u := by
    intro s hs
    exact ⟨(le_min hla hlb).trans hs.1, hs.2.le.trans (max_le hua hub)⟩
  rw [inter_eq_left.mpr hsub,Real.volume_real_Ico]
  simp [smul_eq_mul,max_sub_min_eq_abs,abs_sub_comm]

lemma bit_mismatch (a b s : ℝ) :
    |bit a s - bit b s| = bit a s + bit b s - 2*bit a s*bit b s := by
  unfold bit
  split <;> split <;> norm_num

variable {E : Type*} [Fintype E]

lemma frequency_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (a : E → ℝ) (s : ℝ) :
    0 ≤ frequency p a s := Finset.sum_nonneg fun e _ => mul_nonneg (hp e) (bit_nonneg _ _)

lemma frequency_le_one (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) : frequency p a s ≤ 1 := by
  unfold frequency
  calc
    _ ≤ ∑ e, p e := Finset.sum_le_sum fun e _ => mul_le_of_le_one_right (hp e) (bit_le_one _ _)
    _ = 1 := hs

lemma frequency_measurable (p : E → ℝ) (a : E → ℝ) : Measurable (frequency p a) := by
  unfold frequency
  exact Finset.measurable_sum Finset.univ fun e _ =>
    measurable_const.mul (bit_measurable (a e))

lemma minority_integrableOn (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (l u : ℝ) :
    IntegrableOn (minority p a) (Icc l u) := by
  have hm : Measurable (minority p a) :=
    (frequency_measurable p a).min (measurable_const.sub (frequency_measurable p a))
  apply Integrable.of_bound hm.aestronglyMeasurable (1 : ℝ)
  filter_upwards [] with s
  change |min (frequency p a s) (1-frequency p a s)| ≤ 1
  rw [abs_of_nonneg (le_min (frequency_nonneg p hp a s)
    (sub_nonneg.mpr (frequency_le_one p hp hs a s)))]
  exact (min_le_left _ _).trans (frequency_le_one p hp hs a s)

lemma independent_mismatch (p : E → ℝ) (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) :
    (∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) =
      2*frequency p a s*(1-frequency p a s) := by
  simp_rw [bit_mismatch]
  simp_rw [mul_sub,mul_add]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have h₁ : (∑ e, ∑ f, p e*p f*bit (a e) s) = frequency p a s := by
    simp_rw [mul_right_comm (p _) (p _) (bit _ _),← Finset.mul_sum,hs,mul_one]
    rfl
  have h₂ : (∑ e, ∑ f, p e*p f*bit (a f) s) = frequency p a s := by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul,hs,one_mul]
    rfl
  have h₃ : (∑ e, ∑ f, p e*p f*(2*bit (a e) s*bit (a f) s)) =
      2*frequency p a s*frequency p a s := by
    have he (e f : E) : p e*p f*(2*bit (a e) s*bit (a f) s) =
        (2*(p e*bit (a e) s))*(p f*bit (a f) s) := by ring
    simp_rw [he,← Finset.mul_sum,← Finset.sum_mul]
    unfold frequency
    rw [← Finset.mul_sum]
  rw [h₁,h₂,h₃]
  ring

lemma mismatch_le_twice_minority (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) :
    (∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) ≤ 2*minority p a s := by
  rw [independent_mismatch p hs a s,minority,mul_min_of_nonneg _ _ (by norm_num)]
  have h0 := frequency_nonneg p hp a s
  have h1 := frequency_le_one p hp hs a s
  apply le_min <;> nlinarith [sq_nonneg (frequency p a s),sq_nonneg (1-frequency p a s)]

lemma pair_integrableOn (c a b l u : ℝ) :
    IntegrableOn (fun s => c * |bit a s-bit b s|) (Icc l u) :=
  ((bit_integrableOn a l u).sub (bit_integrableOn b l u)).abs.const_mul c

lemma mismatch_integrableOn (p a : E → ℝ) (l u : ℝ) :
    IntegrableOn (fun s => ∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) (Icc l u) := by
  exact integrable_finsetSum Finset.univ fun e _ =>
    integrable_finsetSum Finset.univ fun f _ => pair_integrableOn _ _ _ _ _

lemma integrated_mismatch (p a : E → ℝ) {l u : ℝ}
    (hla : ∀ e, l ≤ a e) (hua : ∀ e, a e ≤ u) :
    (∫ s in Icc l u, ∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) =
      ∑ e, ∑ f, p e*p f*|a e-a f| := by
  rw [integral_finsetSum Finset.univ (fun e _ =>
    integrable_finsetSum Finset.univ fun f _ => pair_integrableOn _ _ _ _ _)]
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_finsetSum Finset.univ (fun f _ => pair_integrableOn _ _ _ _ _)]
  apply Finset.sum_congr rfl
  intro f _
  rw [integral_const_mul,bit_sub_integral (hla e) (hua e) (hla f) (hua f)]

lemma expected_distance_le (p a : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) {l u : ℝ} (hla : ∀ e, l ≤ a e) (hua : ∀ e, a e ≤ u) :
    (∑ e, ∑ f, p e*p f*|a e-a f|) ≤ 2 * ∫ s in Icc l u, minority p a s := by
  rw [← integrated_mismatch p a hla hua,← integral_const_mul]
  exact integral_mono (mismatch_integrableOn p a l u)
    ((minority_integrableOn p hp hs a l u).const_mul 2)
    (mismatch_le_twice_minority p hp hs a)

end
end PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.WeightedAbsoluteValues
open MeasureTheory Set Finset Real
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
variable {E : Type*} [Fintype E]

omit [NumberField K] [IsGalois ℚ K] in
lemma log_quotient_distance (v : AbsoluteValue K ℝ) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    |-log (v x) - -log (v y)| = |log (v (x/y))| := by
  rw [map_div₀,log_div ((v.pos hx).ne') ((v.pos hy).ne')]
  rw [show -log (v x) - -log (v y) = -(log (v x)-log (v y)) by ring,abs_neg]

omit [Fintype E] in
lemma profile_pair_height (d : E → K) (hd : ∀ e, d e ≠ 0) (e f : E) :
    ((∑ σ : K →ₐ[ℚ] ℂ, |archThreshold K d σ e-archThreshold K d σ f|) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), |finiteThreshold K d v e-finiteThreshold K d v f|)) /
      (Module.finrank ℚ K : ℝ) = 2*exactHeight K (d e/d f) := by
  simp only [archThreshold,finiteThreshold,log_quotient_distance K _ (hd e) (hd f)]
  exact weighted_abs_log_eq_twice K (div_ne_zero (hd e) (hd f))

omit [IsGalois ℚ K] in
lemma exists_normalizing_edge (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (d : E → K) {S : ℝ}
    (hS : (∑ e, ∑ f, p e*p f*exactHeight K (d e/d f)) ≤ S) :
    ∃ f, (∑ e, p e*exactHeight K (d e/d f)) ≤ S := by
  classical
  have hne : Nonempty E := by
    by_contra h
    have : IsEmpty E := not_nonempty_iff.mp h
    simp at hs
  obtain ⟨f,_,hf⟩ := exists_min_image univ (fun f => ∑ e, p e*exactHeight K (d e/d f))
    univ_nonempty
  refine ⟨f,le_trans ?_ hS⟩
  calc
    _ = ∑ j, p j * (∑ e, p e*exactHeight K (d e/d f)) := by rw [← sum_mul,hs,one_mul]
    _ ≤ ∑ j, p j * (∑ e, p e*exactHeight K (d e/d j)) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf j (mem_univ _)) (hp j)
    _ = _ := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro j _
      ring

end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.LevelScale
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels
open scoped Classical NNReal
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [Fintype E]

lemma prob_bounds (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) :
    0 ≤ prob μ S d a ∧ prob μ S d a ≤ 1 :=
  ⟨ThresholdProfiles.frequency_nonneg _ μ.nonneg _ _,
   ThresholdProfiles.frequency_le_one _ μ.nonneg μ.total _ _⟩
lemma prob_measurable (μ : Law E) (S : Finset K) (d : E → K) : Measurable (prob μ S d) := by
  exact FiniteLevels.measurable_pieces (fun v => ThresholdProfiles.frequency μ.val (cut S d v))
    (fun v => ThresholdProfiles.frequency_measurable _ _)
lemma minority_measurable (μ : Law E) (S : Finset K) (d : E → K) : Measurable (minority μ S d) :=
  (prob_measurable μ S d).min (measurable_const.sub (prob_measurable μ S d))
lemma minority_bounds (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) :
    0 ≤ minority μ S d a ∧ minority μ S d a ≤ 1 := by
  have h := prob_bounds μ S d a
  unfold minority
  exact ⟨le_min h.1 (sub_nonneg.mpr h.2),(min_le_left _ _).trans h.2⟩
lemma scale_eq (μ : Law E) (S : Finset K) (d : E → K) :
    scale μ S d = (Module.finrank ℚ K : ℝ)⁻¹ *
      ∑v : Place K S,∫s in Icc (-radius K S v) (radius K S v),
        ThresholdProfiles.minority μ.val (cut S d v) s := by
  exact FiniteLevels.integral_eq (weight K) _ _ _ (minority_measurable μ S d) 1
    (fun a => by rw [abs_of_nonneg (minority_bounds μ S d a).1]; exact (minority_bounds μ S d a).2)

omit [Fintype E] in
lemma pair_distance [IsGalois ℚ K] (S : Finset K) (d : E → K) (hd : ∀e,d e≠0)
    (hm : ∀e,d e∈S) (e f : E) :
    (∑v : Place K S,|cut S d v e-cut S d v f|)/(Module.finrank ℚ K : ℝ) =
      2*WeightedAbsoluteValues.exactHeight K (d e/d f) := by
  have hf : (∑v : ↥(finiteSupport K S),
      |cut S d (.inr v) e-cut S d (.inr v) f|) =
      ∑ᶠv : Nat.Primes × Gal(K/ℚ),
        |WeightedAbsoluteValues.finiteThreshold K d v e-WeightedAbsoluteValues.finiteThreshold K d v f| := by
    change (∑v : ↥(finiteSupport K S),
      |WeightedAbsoluteValues.finiteThreshold K d v.val e-WeightedAbsoluteValues.finiteThreshold K d v.val f|)=_
    rw [Finset.sum_coe_sort (finiteSupport K S) (fun v =>
      |WeightedAbsoluteValues.finiteThreshold K d v e-WeightedAbsoluteValues.finiteThreshold K d v f|)]
    symm
    apply finsum_eq_sum_of_support_subset
    intro v hv
    by_contra hn
    apply hv
    simp only [WeightedAbsoluteValues.finiteThreshold,log_off_support K (hm e) hn,
      log_off_support K (hm f) hn,neg_zero,sub_self,abs_zero]
  rw [Fintype.sum_sum_type,hf]
  exact WeightedAbsoluteValues.profile_pair_height K d hd e f

theorem expected_height_le_scale [IsGalois ℚ K] (μ : Law E) (S : Finset K) (d : E → K)
    (hd : ∀e,d e≠0) (hm : ∀e,d e∈S) :
    avg (pair μ μ) (fun ef => WeightedAbsoluteValues.exactHeight K (d ef.1/d ef.2)) ≤
      scale μ S d := by
  have he (v : Place K S) := ThresholdProfiles.expected_distance_le μ.val (cut S d v)
    μ.nonneg μ.total (fun e => (threshold_in_range K (hm e) v).1)
      (fun e => (threshold_in_range K (hm e) v).2)
  have h := sum_le_sum (s:=univ) (fun v _ => he v)
  have hi : 0≤ (Module.finrank ℚ K : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left h hi
  have hp : (Module.finrank ℚ K : ℝ)⁻¹ *
      (∑v : Place K S,∑e,∑f,μ.val e*μ.val f*|cut S d v e-cut S d v f|) =
      2*avg (pair μ μ) (fun ef => WeightedAbsoluteValues.exactHeight K (d ef.1/d ef.2)) := by
    have hs : (∑v : Place K S,∑e,∑f,μ.val e*μ.val f*|cut S d v e-cut S d v f|) =
        ∑e,∑f,μ.val e*μ.val f*∑v : Place K S,|cut S d v e-cut S d v f| := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e _
      rw [sum_comm]
      simp only [mul_sum]
    rw [hs,pair_avg]
    unfold avg
    simp_rw [mul_sum,← mul_assoc]
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro f _
    have ht := pair_distance S d hd hm e f
    rw [div_eq_mul_inv] at ht
    calc
      _ = μ.val e*μ.val f*((∑v : Place K S,|cut S d v e-cut S d v f|)*(Module.finrank ℚ K:ℝ)⁻¹) := by simp only [sum_mul,mul_sum]; apply sum_congr rfl; intro v _; ring
      _ = _ := by rw [ht]; ring
  rw [hp,← mul_sum] at h
  rw [scale_eq]
  nlinarith only [h]

lemma exists_normalizing_edge [IsGalois ℚ K] (μ : Law E) (S : Finset K) (d : E → K)
    (hd : ∀e,d e≠0) (hm : ∀e,d e∈S) :
    ∃f,avg μ (fun e => WeightedAbsoluteValues.exactHeight K (d e/d f))≤ scale μ S d := by
  apply WeightedAbsoluteValues.exists_normalizing_edge K μ.val μ.nonneg μ.total d
  have h := expected_height_le_scale μ S d hd hm
  rw [pair_avg] at h
  unfold avg at h
  simp_rw [mul_sum,← mul_assoc] at h
  exact h
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

namespace PlanarUnitDistances.LevelScale
open FiniteLaw MeasureTheory PlaceLevels
open scoped Classical
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [Fintype E]

lemma scale_support (μ : Law E) (S : Finset K) (d : E → K) :
    scale (support μ) S (fun e => d e.val)=scale μ S d := by
  unfold scale
  apply integral_congr_ae
  filter_upwards [] with a
  have hf : prob (support μ) S (fun e => d e.val) a=prob μ S d a :=
    support_avg μ (fun e => ThresholdProfiles.bit (cut S d a.1 e) a.2)
  simp only [minority,hf]

theorem exists_normalizing_edge_support [IsGalois ℚ K] (μ : Law E) (S : Finset K) (d : E → K)
    (hd : ∀e,0<μ.val e → d e≠0) (hm : ∀e,0<μ.val e → d e∈S) :
    ∃f,0<μ.val f ∧ avg μ (fun e => WeightedAbsoluteValues.exactHeight K (d e/d f))≤ scale μ S d := by
  obtain ⟨f,hf⟩ := exists_normalizing_edge (support μ) S (fun e => d e.val)
    (fun e => hd e.val e.property) (fun e => hm e.val e.property)
  rw [support_avg μ (fun e => WeightedAbsoluteValues.exactHeight K (d e/d f.val)),scale_support] at hf
  exact ⟨f.val,f.property,hf⟩

end
end PlanarUnitDistances.LevelScale

namespace PlanarUnitDistances.NormalizedScale
open FiniteLaw FiniteStarCoupling WeightedAbsoluteValues
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma avg_congr_support {X : Type*} [Fintype X] (μ : Law X) {f g : X → ℝ}
    (h : ∀x,0<μ.val x → f x=g x) : avg μ f=avg μ g := by
  unfold avg
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0<μ.val x
  · rw [h x hx]
  · rw [le_antisymm (le_of_not_gt hx) (μ.nonneg x),zero_mul,zero_mul]

theorem coordinates (π : Law (P×Q)) (z w : P⊕Q → K) (E : P → Q → Prop)
    (hE : ∀p q,0<π.val (p,q) → E p q)
    (hu : ∀p q,E p q → (z (.inl p)-z (.inr q))*(w (.inl p)-w (.inr q))=1)
    (hzi : Function.Injective (z ∘ Sum.inl)) (hzq : Function.Injective (z ∘ Sum.inr))
    (S : Finset K) (hS : ∀p q,E p q → z (.inl p)-z (.inr q)∈S)
    {C R : ℝ} (hc : LocalHeightTransfer.LabelControl C (fun p q => π.val (p,q)))
    (hR : LevelScale.scale π S (fun pq => z (.inl pq.1)-z (.inr pq.2)) ≤ R) :
    ∃(Z W : P → K) (a b : Q → K),
      (∀p q,E p q → (Z p-a q)*(W p-b q)=1) ∧
      Function.Injective Z ∧ Function.Injective a ∧
      let A := 4*((C+1)*(Real.log 2+2))*(R+1)+4*R+2*Real.log 2
      avg (left π) (fun p => exactHeight K (Z p)) ≤ A ∧
      avg (left π) (fun p => exactHeight K (W p)) ≤ A ∧
      avg (right π) (fun q => exactHeight K (a q)) ≤ A ∧
      avg (right π) (fun q => exactHeight K (b q)) ≤ A ∧
      avg π (fun pq => exactHeight K (Z pq.1-a pq.2)) ≤ A := by
  let d : P×Q → K := fun pq => z (.inl pq.1)-z (.inr pq.2)
  have hn : ∀pq,0<π.val pq → d pq≠0 := by
    intro pq hp hz
    have hh := hu pq.1 pq.2 (hE pq.1 pq.2 hp)
    change d pq*(w (.inl pq.1)-w (.inr pq.2))=1 at hh
    rw [hz,zero_mul] at hh
    exact zero_ne_one hh
  obtain ⟨e,he,havg⟩ := LevelScale.exists_normalizing_edge_support π S d hn
    (fun pq hp => hS pq.1 pq.2 (hE pq.1 pq.2 hp))
  have hθ := hn e he
  let z₀ : P⊕Q → K := fun v => z v/d e
  let w₀ : P⊕Q → K := fun v => w v*d e
  have huz : ∀p q,E p q → (z₀ (.inl p)-z₀ (.inr q))*(w₀ (.inl p)-w₀ (.inr q))=1 := by
    intro p q hp
    dsimp only [z₀,w₀]
    rw [←sub_div,←sub_mul]
    field_simp
    exact hu p q hp
  have hZ : avg π (fun pq => exactHeight K (z₀ (.inl pq.1)-z₀ (.inr pq.2))) ≤ R := by
    simpa only [z₀,←sub_div,d] using havg.trans hR
  have hW : avg π (fun pq => exactHeight K (w₀ (.inl pq.1)-w₀ (.inr pq.2))) ≤ R := by
    have hh : avg π (fun pq => exactHeight K (w₀ (.inl pq.1)-w₀ (.inr pq.2)))=
        avg π (fun pq => exactHeight K (z₀ (.inl pq.1)-z₀ (.inr pq.2))) := by
      apply avg_congr_support
      intro pq hp
      have hh := huz pq.1 pq.2 (hE pq.1 pq.2 hp)
      have heq := eq_inv_of_mul_eq_one_left hh
      rw [heq,exactHeight_inv]
    rwa [hh]
  obtain ⟨p₀,hp₀⟩ := NormalizedCoordinates.translate K π hc z₀ w₀ hZ hW
  let Z : P → K := fun p => z₀ (.inl p)-z₀ (.inl p₀)
  let W : P → K := fun p => w₀ (.inl p)-w₀ (.inl p₀)
  let a : Q → K := fun q => z₀ (.inr q)-z₀ (.inl p₀)
  let b : Q → K := fun q => w₀ (.inr q)-w₀ (.inl p₀)
  have heq (p : P) (q : Q) : Z p-a q=z₀ (.inl p)-z₀ (.inr q) := by dsimp [Z,a]; ring
  have hfq (p : P) (q : Q) : W p-b q=w₀ (.inl p)-w₀ (.inr q) := by dsimp [W,b]; ring
  refine ⟨Z,W,a,b,fun p q hp => by rw [heq,hfq]; exact huz p q hp,?_,?_,?_⟩
  · intro p r hpr
    apply hzi
    have hh : z (.inl p)/d e=z (.inl r)/d e := sub_left_inj.mp hpr
    exact (div_left_inj' hθ).mp hh
  · intro p r hpr
    apply hzq
    have hh : z (.inr p)/d e=z (.inr r)/d e := sub_left_inj.mp hpr
    exact (div_left_inj' hθ).mp hh
  · simp only [avg_add] at hp₀
    change avg (left π) (fun p => exactHeight K (Z p))+avg (left π) (fun p => exactHeight K (W p))+
      (avg (right π) (fun q => exactHeight K (a q))+avg (right π) (fun q => exactHeight K (b q)))+
      (avg π (fun pq => exactHeight K (z₀ (.inl pq.1)-z₀ (.inr pq.2)))+
        avg π (fun pq => exactHeight K (w₀ (.inl pq.1)-w₀ (.inr pq.2)))) ≤ _ at hp₀
    have hz := avg_nonneg (left π) (fun p => exactHeight_nonneg K (Z p))
    have hw := avg_nonneg (left π) (fun p => exactHeight_nonneg K (W p))
    have ha := avg_nonneg (right π) (fun q => exactHeight_nonneg K (a q))
    have hb := avg_nonneg (right π) (fun q => exactHeight_nonneg K (b q))
    have hd := avg_nonneg π (fun pq => exactHeight_nonneg K (z₀ (.inl pq.1)-z₀ (.inr pq.2)))
    have he := avg_nonneg π (fun pq => exactHeight_nonneg K (w₀ (.inl pq.1)-w₀ (.inr pq.2)))
    dsimp only
    simp_rw [heq]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith
end
end PlanarUnitDistances.NormalizedScale

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

lemma integral_pmf [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Law X) (f : X → ℝ) :
    (∫ x,f x ∂μ.pmf.toMeasure) = avg μ f := by
  rw [PMF.integral_eq_sum]
  simp [avg,μ.nonneg]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

attribute [local instance] Classical.propDecidable

omit [IsGalois ℚ K] in
lemma arch_average_posLog_le (x : K) :
    (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) /
      (Module.finrank ℚ K : ℝ) ≤ exactHeight K x := by
  apply div_le_div_of_nonneg_right _ (finrank_pos K).le
  exact le_add_of_nonneg_right (finsum_nonneg fun _ => posLog_nonneg)

omit [IsGalois ℚ K] in
lemma large_embedding_tail (x : K) {B : ℝ} (hB : 1 < B) :
    (∑ σ : K →ₐ[ℚ] ℂ, if B < infiniteEntry K σ x then (1 : ℝ) else 0) /
      (Module.finrank ℚ K : ℝ) ≤ exactHeight K x / log B := by
  have hlog : 0 < log B := log_pos hB
  have hh : (∑ σ : K →ₐ[ℚ] ℂ, if B < infiniteEntry K σ x then (1 : ℝ) else 0) * log B ≤
      ∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x) := by
    rw [sum_mul]
    apply sum_le_sum
    intro σ _
    split_ifs with hs
    · rw [one_mul, posLog_eq_log (by rw [abs_of_nonneg ((infiniteEntry K σ).nonneg _)]; linarith)]
      exact log_le_log (by linarith) hs.le
    · simpa using (posLog_nonneg (x := infiniteEntry K σ x))
  rw [le_div_iff₀ hlog,div_mul_eq_mul_div]
  exact (div_le_div_of_nonneg_right hh (finrank_pos K).le).trans (arch_average_posLog_le K x)

omit [IsGalois ℚ K] in
lemma random_large_embedding_tail {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → K) {B : ℝ} (hB : 1 < B) :
    (∑ ω, p ω * ((∑ σ : K →ₐ[ℚ] ℂ,
      if B < infiniteEntry K σ (X ω) then (1 : ℝ) else 0) / (Module.finrank ℚ K : ℝ))) ≤
      (∑ ω, p ω * exactHeight K (X ω)) / log B := by
  rw [sum_div]
  exact sum_le_sum fun ω _ => by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
      (large_embedding_tail K (X ω) hB) (hp ω)

end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.EmbeddingTails
open Finset FiniteLaw WeightedAbsoluteValues Real
open scoped Classical
noncomputable section
variable {K Ω I : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype Ω] [Fintype I]

omit [Fintype I] in
lemma large (μ : Law Ω) (X : Ω → K) {B : ℝ} (hB : 1 < B) :
    event (pair μ (uniform (Embeddings K))) (fun a => B < ‖a.2 (X a.1)‖) ≤
      avg μ (fun x => exactHeight K (X x))/log B := by
  rw [event,pair_avg]
  simp_rw [uniform_avg]
  have hh := random_large_embedding_tail K μ.val μ.nonneg X hB
  simp only [infiniteEntry_apply] at hh
  convert hh using 1
  simp only [avg,Embeddings,infiniteEntry_count]
  apply sum_congr rfl
  intro x _
  congr 1
  congr 1

omit [Fintype I] in
lemma small (μ : Law Ω) (X : Ω → K) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    event (pair μ (uniform (Embeddings K))) (fun a => X a.1 ≠ 0 ∧ ‖a.2 (X a.1)‖ < r) ≤
      avg μ (fun x => exactHeight K (X x))/log (1/r) := by
  have he (a : Ω × Embeddings K) :
      (X a.1 ≠ 0 ∧ ‖a.2 (X a.1)‖ < r) ↔ 1/r < ‖a.2 ((X a.1)⁻¹)‖ := by
    by_cases hx : X a.1=0
    · simp [hx,hr.le]
    have hn : 0 < ‖a.2 (X a.1)‖ := norm_pos_iff.mpr ((map_ne_zero a.2).mpr hx)
    rw [map_inv₀,norm_inv,one_div,inv_lt_inv₀ hr hn]
    exact and_iff_right hx
  rw [event_congr _ he]
  simpa only [exactHeight_inv] using large μ (fun x => (X x)⁻¹) ((one_lt_div hr).mpr hr₁)

lemma large_family (μ : Law Ω) (X : I → Ω → K) {B : ℝ} (hB : 1 < B) :
    event (pair μ (uniform (Embeddings K))) (fun a => ∃i,B < ‖a.2 (X i a.1)‖) ≤
      avg μ (fun x => ∑i,exactHeight K (X i x))/log B := by
  calc
    _ ≤ ∑i,event (pair μ (uniform (Embeddings K))) (fun a => B < ‖a.2 (X i a.1)‖) := event_exists_le _ _
    _ ≤ ∑i,avg μ (fun x => exactHeight K (X i x))/log B := sum_le_sum (fun i _ => large μ (X i) hB)
    _ = _ := by rw [←sum_div,avg_sum]

lemma small_family (μ : Law Ω) (X : I → Ω → K) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    event (pair μ (uniform (Embeddings K))) (fun a => ∃i,X i a.1 ≠ 0 ∧ ‖a.2 (X i a.1)‖ < r) ≤
      avg μ (fun x => ∑i,exactHeight K (X i x))/log (1/r) := by
  calc
    _ ≤ ∑i,event (pair μ (uniform (Embeddings K))) (fun a => X i a.1 ≠ 0 ∧ ‖a.2 (X i a.1)‖ < r) := event_exists_le _ _
    _ ≤ ∑i,avg μ (fun x => exactHeight K (X i x))/log (1/r) := sum_le_sum (fun i _ => small μ (X i) hr hr₁)
    _ = _ := by rw [←sum_div,avg_sum]
end
end PlanarUnitDistances.EmbeddingTails

namespace PlanarUnitDistances.TemplateCollision
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

lemma collision_eq {X : Type*} [Fintype X] (μ : Law X) :
    event (pair μ μ) (fun xx => xx.1=xx.2)=∑x,μ.val x^2 := by
  simp [event,avg,pair,Fintype.sum_prod_type,pow_two]

end
end PlanarUnitDistances.TemplateCollision

namespace PlanarUnitDistances.PredictionCoupling
open Finset FiniteLaw FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P H A B : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]

lemma cond_diagonal (μ : Law P) (h : P → H) (j : H) {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀p,μ.val p ≤ d) :
    (push μ h).val j*event (pair (cond μ h j) (cond μ h j)) (fun pp => pp.1=pp.2) ≤ d := by
  rw [TemplateCollision.collision_eq,mul_sum]
  calc
    _ = ∑p,(if h p=j then μ.val p else 0)*(cond μ h j).val p := by
      apply sum_congr rfl
      intro p _
      rw [pow_two,←mul_assoc]
      exact congrArg (fun t => t*(cond μ h j).val p) (cond_weight μ h j p)
    _ ≤ ∑p,d*(cond μ h j).val p := by
      apply sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (by split_ifs; exact hm p; exact hd) ((cond μ h j).nonneg p)
    _ = d := by rw [←mul_sum,(cond μ h j).total,mul_one]

theorem diagonal (μ : Law P) (h : P → H) {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    event (coupling μ h) (fun pp => pp.1=pp.2) ≤ (Fintype.card H:ℝ)*d := by
  unfold event
  rw [coupling,mix_avg]
  calc
    _ ≤ ∑_j : H,d := sum_le_sum (fun j _ => cond_diagonal μ h j hd hm)
    _ = _ := by simp

end
end PlanarUnitDistances.PredictionCoupling

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

open MeasureTheory Real
lemma history_singleton (D : Type*) [MeasurableSpace D] [MeasurableSingletonClass D] (n : ℕ) :
    MeasurableSingletonClass (FiniteInformation.History D n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (MeasurableSingletonClass (FiniteInformation.History D n × D))

end
end PlanarUnitDistances.CrossPrediction

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]

lemma triple_coordinate (μ : Law X) (i : Fin 3) (f : X → ℝ) :
    avg (triple μ) (fun x => f (entry x i))=avg μ f := by
  fin_cases i <;> simp [entry,triple,pair_avg,avg_const]

lemma triple_pair (μ : Law X) (i j : Fin 3) (hij : i≠j) (f : X → X → ℝ) :
    avg (triple μ) (fun x => f (entry x i) (entry x j))=
      avg μ (fun x => avg μ (f x)) := by
  fin_cases i <;> fin_cases j <;> simp_all [entry,triple,pair_avg,avg_const]
  all_goals exact avg_comm μ μ _

lemma triple_collision (μ : Law X) (i j : Fin 3) (hij : i≠j) :
    event (triple μ) (fun x => entry x i=entry x j)=∑x,μ.val x^2 := by
  calc
    _ = avg μ (fun x => avg μ (fun y => if x=y then (1:ℝ) else 0)) :=
      triple_pair μ i j hij (fun x y => if x=y then (1:ℝ) else 0)
    _ = _ := by
      rw [←pair_avg μ μ (fun pp => if pp.1=pp.2 then (1:ℝ) else 0)]
      exact TemplateCollision.collision_eq μ

lemma collision_le_atom (μ : Law X) {d : ℝ} (hm : ∀x,μ.val x ≤ d) :
    (∑x,μ.val x^2) ≤ d := by
  calc
    _ ≤ ∑x,d*μ.val x := sum_le_sum (fun x _ => by
      rw [pow_two]; exact mul_le_mul_of_nonneg_right (hm x) (μ.nonneg x))
    _ = d := by rw [←mul_sum,μ.total,mul_one]
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Quantization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.TripleCoupling
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q H : Type*} [Fintype P] [Fintype Q] [Fintype H]

omit [Fintype H] in
lemma first (π : Law (P×Q)) (h : P → H) (f : P → ℝ) :
    avg (law π h) (fun a => f (point a))=avg (left π) f := by
  simp only [law,dependent_avg,point,avg_const]

lemma predicted_point (π : Law (P×Q)) (h : P → H) (f : P → ℝ) :
    avg (law π h) (fun a => f (prediction a))=avg (left π) f := by
  simp only [law,dependent_avg,prediction,pair_avg,avg_const]
  rw [←push_avg (left π) h (fun j => avg (cond (left π) h j) f)]
  exact cond_tower (left π) h f

omit [Fintype H] in
lemma edge (π : Law (P×Q)) (h : P → H) (i : Fin 3) (f : P → Q → ℝ) :
    avg (law π h) (fun a => f (point a) (neighbor a i))=avg π (fun pq => f pq.1 pq.2) := by
  simp only [law,dependent_avg,point,neighbor,pair_avg,triple_coordinate,avg_const]
  exact row_avg π f

omit [Fintype H] in
lemma center (π : Law (P×Q)) (h : P → H) (i : Fin 3) (f : Q → ℝ) :
    avg (law π h) (fun a => f (neighbor a i))=avg (right π) f := by
  simpa only [right,push_avg] using edge π h i (fun _ q => f q)

omit [Fintype H] in
lemma predicted_pair (π : Law (P×Q)) (h : P → H) (i : Fin 3) (f : P → Q → ℝ) :
    avg (law π h) (fun a => f (prediction a) (neighbor a i))=
      avg (right π) (fun q => avg (col π q) (fun p =>
        avg (cond (left π) h (h p)) (fun r => f r q))) := by
  simp only [law,dependent_avg,prediction,neighbor,pair_avg,triple_coordinate]
  simp_rw [avg_comm (cond (left π) h (h _)) (row π _)]
  rw [row_avg,col_avg]

lemma point_prediction (π : Law (P×Q)) (h : P → H) (f : P → P → ℝ) :
    avg (law π h) (fun a => f (point a) (prediction a))=
      avg (PredictionCoupling.coupling (left π) h) (fun pp => f pp.1 pp.2) := by
  simp only [law,dependent_avg,point,prediction,pair_avg,avg_const,
    PredictionCoupling.coupling,mix_avg]
  exact (cond_tower_dep (left π) h (fun j p => avg (cond (left π) h j) (f p))).symm

omit [Fintype H] in
lemma two_centers (π : Law (P×Q)) (h : P → H) (i j : Fin 3) (f : Q → Q → ℝ) :
    avg (law π h) (fun a => f (neighbor a i) (neighbor a j))=
      avg (left π) (fun p => avg (triple (row π p)) (fun x => f (entry x i) (entry x j))) := by
  simp only [law,dependent_avg,neighbor,pair_avg,avg_const]

lemma predicted_diagonal (π : Law (P×Q)) (h : P → H) {d : ℝ}
    (hd : 0 ≤ d) (hm : ∀p,(left π).val p ≤ d) :
    event (law π h) (fun a => point a=prediction a) ≤ (Fintype.card H:ℝ)*d := by
  change avg (law π h) (fun a => (fun p r => if p=r then (1:ℝ) else 0) (point a) (prediction a))≤_
  rw [point_prediction π h (fun p r => if p=r then (1:ℝ) else 0)]
  exact PredictionCoupling.diagonal (left π) h hd hm

omit [Fintype H] in
lemma center_diagonal (π : Law (P×Q)) (h : P → H) (i j : Fin 3) (hij : i≠j)
    {d : ℝ} (hm : ∀p q,(row π p).val q ≤ d) :
    event (law π h) (fun a => neighbor a i=neighbor a j) ≤ d := by
  change avg (law π h) (fun a => (fun q r => if q=r then (1:ℝ) else 0) (neighbor a i) (neighbor a j))≤_
  rw [two_centers π h i j (fun q r => if q=r then (1:ℝ) else 0)]
  change avg (left π) (fun p => event (triple (row π p))
    (fun x => entry x i=entry x j)) ≤ d
  simp_rw [triple_collision _ i j hij]
  exact avg_le_const _ (fun p => collision_le_atom (row π p) (hm p))
end
end PlanarUnitDistances.TripleCoupling

namespace PlanarUnitDistances.FiniteQuantization
open scoped Classical
noncomputable section

lemma bounded_cell {B τ x : ℝ} (hτ : 0 < τ) (hx : |x| ≤ B) :
    ⌊x/τ⌋ ∈ Finset.Icc (-(radius B τ : ℤ)) (radius B τ : ℤ) := by
  have hN : B/τ ≤ (radius B τ : ℝ) := Nat.le_ceil _
  have hu : x/τ ≤ (radius B τ : ℝ) :=
    (div_le_div_of_nonneg_right (le_trans (le_abs_self x) hx) hτ.le).trans hN
  have hl : -(radius B τ : ℝ) ≤ x/τ := by
    have hh : -B ≤ x := (abs_le.mp hx).1
    have hh' := div_le_div_of_nonneg_right hh hτ.le
    rw [neg_div] at hh'
    linarith
  apply Finset.mem_Icc.mpr
  constructor
  · apply Int.le_floor.mpr
    simpa only [Int.cast_neg,Int.cast_natCast] using hl
  · apply Int.floor_le_iff.mpr
    simp only [Int.cast_natCast]
    linarith

lemma axis_close {B τ x y : ℝ} (hτ : 0 < τ) (hx : |x| ≤ B)
    (he : axis B τ x=axis B τ y) : |y-x| < τ := by
  have hmem := bounded_cell hτ hx
  have hf : ⌊x/τ⌋=⌊y/τ⌋ := by
    unfold axis at he
    rw [dite_eq_left hmem] at he
    split_ifs at he with hy
    · exact congrArg Subtype.val (Option.some.inj he)
  have hx0 := Int.floor_le (x/τ)
  have hx1 := Int.lt_floor_add_one (x/τ)
  have hy0 := Int.floor_le (y/τ)
  have hy1 := Int.lt_floor_add_one (y/τ)
  rw [←hf] at hy0 hy1
  have h1 : (y-x)/τ < 1 := by rw [sub_div]; linarith
  have h2 : (x-y)/τ < 1 := by rw [sub_div]; linarith
  have h1' := (div_lt_iff₀ hτ).mp h1
  have h2' := (div_lt_iff₀ hτ).mp h2
  apply abs_lt.mpr
  constructor <;> linarith

lemma complex_close {B τ : ℝ} {z z' : ℂ} (hτ : 0 < τ) (hz : ‖z‖ ≤ B)
    (he : (axis B τ z.re,axis B τ z.im)=(axis B τ z'.re,axis B τ z'.im)) :
    ‖z'-z‖ ≤ Real.sqrt 2*τ := by
  have hr := (axis_close hτ ((Complex.abs_re_le_norm z).trans hz) (congrArg Prod.fst he)).le
  have hi := (axis_close hτ ((Complex.abs_im_le_norm z).trans hz) (congrArg Prod.snd he)).le
  have hr2 := mul_self_le_mul_self (abs_nonneg (z'.re-z.re)) hr
  have hi2 := mul_self_le_mul_self (abs_nonneg (z'.im-z.im)) hi
  simp only [←pow_two, sq_abs] at hr2 hi2
  have hn := Complex.sq_norm (z'-z)
  rw [Complex.normSq_apply] at hn
  simp only [Complex.sub_re,Complex.sub_im] at hn
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp : 0 ≤ Real.sqrt 2*τ := mul_nonneg (Real.sqrt_nonneg _) hτ.le
  nlinarith [norm_nonneg (z'-z)]

theorem same_code_close {B τ : ℝ} (hτ : 0 < τ) {Z W Z' W' : ℂ}
    (hZ : ‖Z‖ ≤ B) (hW : ‖W‖ ≤ B) (he : code B τ Z W=code B τ Z' W') :
    ‖Z'-Z‖ ≤ Real.sqrt 2*τ ∧ ‖W'-W‖ ≤ Real.sqrt 2*τ := by
  exact ⟨complex_close hτ hZ (congrArg Prod.fst he),
    complex_close hτ hW (congrArg Prod.snd he)⟩

end
end PlanarUnitDistances.FiniteQuantization

namespace PlanarUnitDistances.BoundedScaleGeometry

lemma inverse_difference_det {K : Type*} [Field K] (d₀ d₁ d₂ : K)
    (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    ((d₁⁻¹-d₀⁻¹)*(d₂-d₀)-(d₂⁻¹-d₀⁻¹)*(d₁-d₀))*d₀*d₁*d₂ =
      (d₀-d₁)*(d₀-d₂)*(d₁-d₂) := by
  field_simp
  ring

lemma cramer_identity {K : Type*} [Field K] (d₀ d₁ d₂ z w E₀ E₁ E₂ : K)
    (he₀ : z/d₀ + w*d₀ + z*w = E₀)
    (he₁ : z/d₁ + w*d₁ + z*w = E₁)
    (he₂ : z/d₂ + w*d₂ + z*w = E₂) :
    ((d₁⁻¹-d₀⁻¹)*(d₂-d₀)-(d₂⁻¹-d₀⁻¹)*(d₁-d₀))*z =
      (E₁-E₀)*(d₂-d₀)-(E₂-E₀)*(d₁-d₀) := by
  simp only [div_eq_mul_inv] at he₀ he₁ he₂
  linear_combination (d₂-d₀)*(he₁-he₀)-(d₁-d₀)*(he₂-he₀)

lemma quantized_edge_error (Z W Z' W' a b : ℂ) {B τ : ℝ}
    (_hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hZ : ‖Z‖ ≤ B) (hW : ‖W‖ ≤ B) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B)
    (hZ' : ‖Z'-Z‖ ≤ τ) (hW' : ‖W'-W‖ ≤ τ)
    (he : (Z'-a)*(W'-b) = 1) :
    ‖(Z-a)*(W-b)-1‖ ≤ 4*B*τ + τ^2 := by
  have hid : (Z-a)*(W-b)-1 =
      -(Z'-Z)*(W-b)-(W'-W)*(Z-a)-(Z'-Z)*(W'-W) := by
    linear_combination he
  rw [hid]
  calc
    _ ≤ ‖-(Z'-Z)*(W-b)-(W'-W)*(Z-a)‖+‖(Z'-Z)*(W'-W)‖ := norm_sub_le _ _
    _ ≤ ‖-(Z'-Z)*(W-b)‖+‖(W'-W)*(Z-a)‖+‖(Z'-Z)*(W'-W)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ τ*(B+B)+τ*(B+B)+τ*τ := by
      simp only [norm_mul, norm_neg]
      gcongr
      · exact (norm_sub_le _ _).trans (add_le_add hW hb)
      · exact (norm_sub_le _ _).trans (add_le_add hZ ha)
    _ = _ := by ring

lemma square_grid_edge_error (Z W Z' W' a b : ℂ) {B τ : ℝ}
    (hB : 2 ≤ B) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1)
    (hZ : ‖Z‖ ≤ B) (hW : ‖W‖ ≤ B) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B)
    (hZ' : ‖Z'-Z‖ ≤ Real.sqrt 2 * τ) (hW' : ‖W'-W‖ ≤ Real.sqrt 2 * τ)
    (he : (Z'-a)*(W'-b) = 1) :
    ‖(Z-a)*(W-b)-1‖ ≤ 8*B*τ := by
  have hs : Real.sqrt 2 ≤ (3:ℝ)/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]
  have hBn : 0 ≤ B := by linarith
  calc
    _ ≤ 4*B*(Real.sqrt 2*τ)+(Real.sqrt 2*τ)^2 :=
      quantized_edge_error Z W Z' W' a b hBn (by positivity) hZ hW ha hb hZ' hW' he
    _ = 4*B*(Real.sqrt 2*τ)+2*τ^2 := by
      rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    _ ≤ 6*B*τ+2*τ := by
      have h₁ := mul_le_mul_of_nonneg_right hs (show 0 ≤ 4*B*τ by positivity)
      have h₂ : τ^2 ≤ τ := by nlinarith
      nlinarith
    _ ≤ 8*B*τ := by nlinarith [mul_nonneg (show 0 ≤ B-1 by linarith) hτ]

theorem no_separated_approximate_point
    (d₀ d₁ d₂ z w E₀ E₁ E₂ : ℂ) {B r τ : ℝ}
    (hB : 0 < B) (hr : 0 < r) (hτ : 0 ≤ τ)
    (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (hd₀ : ‖d₀‖ ≤ B) (hd₁ : ‖d₁‖ ≤ B) (hd₂ : ‖d₂‖ ≤ B)
    (hs₀₁ : r ≤ ‖d₀-d₁‖) (hs₀₂ : r ≤ ‖d₀-d₂‖) (hs₁₂ : r ≤ ‖d₁-d₂‖)
    (hz : r ≤ ‖z‖)
    (hE₀ : ‖E₀‖ ≤ 8*B*τ) (hE₁ : ‖E₁‖ ≤ 8*B*τ) (hE₂ : ‖E₂‖ ≤ 8*B*τ)
    (he₀ : z/d₀ + w*d₀ + z*w = E₀)
    (he₁ : z/d₁ + w*d₁ + z*w = E₁)
    (he₂ : z/d₂ + w*d₂ + z*w = E₂)
    (hmesh : τ < r^4/(128*B^5)) : False := by
  let Δ := (d₁⁻¹-d₀⁻¹)*(d₂-d₀)-(d₂⁻¹-d₀⁻¹)*(d₁-d₀)
  have hdet : ‖Δ‖*B^3 ≥ r^3 := by
    have hh := congrArg norm (inverse_difference_det d₀ d₁ d₂ h₀ h₁ h₂)
    simp only [norm_mul] at hh
    calc
      r^3 = r*r*r := by ring
      _ ≤ ‖d₀-d₁‖*‖d₀-d₂‖*‖d₁-d₂‖ := by gcongr
      _ = ‖Δ‖*‖d₀‖*‖d₁‖*‖d₂‖ := hh.symm
      _ ≤ ‖Δ‖*B*B*B := by gcongr
      _ = ‖Δ‖*B^3 := by ring
  have hup : ‖Δ‖*‖z‖ ≤ 64*B^2*τ := by
    have hh := congrArg norm (cramer_identity d₀ d₁ d₂ z w E₀ E₁ E₂ he₀ he₁ he₂)
    rw [norm_mul] at hh
    change ‖Δ‖*‖z‖ = _ at hh
    rw [hh]
    calc
      _ ≤ ‖(E₁-E₀)*(d₂-d₀)‖+‖(E₂-E₀)*(d₁-d₀)‖ := norm_sub_le _ _
      _ = ‖E₁-E₀‖*‖d₂-d₀‖+‖E₂-E₀‖*‖d₁-d₀‖ := by simp only [norm_mul]
      _ ≤ (16*B*τ)*(2*B)+(16*B*τ)*(2*B) := by
        gcongr
        · exact (norm_sub_le _ _).trans (by linarith)
        · exact (norm_sub_le _ _).trans (by linarith)
        · exact (norm_sub_le _ _).trans (by linarith)
        · exact (norm_sub_le _ _).trans (by linarith)
      _ = _ := by ring
  have hfinal : r^4 ≤ 64*B^5*τ := by
    calc
      r^4 = r^3*r := by ring
      _ ≤ (‖Δ‖*B^3)*‖z‖ := mul_le_mul hdet hz hr.le (by positivity)
      _ = (‖Δ‖*‖z‖)*B^3 := by ring
      _ ≤ (64*B^2*τ)*B^3 := mul_le_mul_of_nonneg_right hup (by positivity)
      _ = _ := by ring
  have hm := (lt_div_iff₀ (show 0 < 128*B^5 by positivity)).mp hmesh
  nlinarith [pow_pos hr 4]
end PlanarUnitDistances.BoundedScaleGeometry

namespace PlanarUnitDistances.QuantizedContradiction
open FiniteQuantization BoundedScaleGeometry
open scoped Classical
noncomputable section

lemma difference_equation (Z W R S a b : ℂ) (he : (Z-a)*(W-b)=1) :
    (R-Z)/(Z-a)+(S-W)*(Z-a)+(R-Z)*(S-W)=(R-a)*(S-b)-1 := by
  have hi : (Z-a)⁻¹=W-b := inv_eq_of_mul_eq_one_right he
  rw [div_eq_mul_inv,hi]
  linear_combination -he

theorem impossible {P Q : Type*} (Z W : P → ℂ) (a b : Q → ℂ) (E : P → Q → Prop)
    (unit : ∀p q,E p q → (Z p-a q)*(W p-b q)=1)
    (p r : P) (q : Fin 3 → Q) {B τ δ : ℝ}
    (hB : 2 ≤ B) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hδ : 0 < δ)
    (hmesh : τ < δ^4/(128*B^5))
    (hp : ∀i,E p (q i))
    (hr : ∀i,∃s,E s (q i) ∧ code B τ (Z r) (W r)=code B τ (Z s) (W s))
    (hZ : ‖Z r‖ ≤ B) (hW : ‖W r‖ ≤ B)
    (ha : ∀i,‖a (q i)‖ ≤ B) (hb : ∀i,‖b (q i)‖ ≤ B)
    (hd : ∀i,‖Z p-a (q i)‖ ≤ B)
    (hsep : ∀i j : Fin 3,i<j → δ ≤ ‖(Z p-a (q i))-(Z p-a (q j))‖)
    (hpr : δ ≤ ‖Z r-Z p‖) : False := by
  let d : Fin 3 → ℂ := fun i => Z p-a (q i)
  let F : Fin 3 → ℂ := fun i => (Z r-a (q i))*(W r-b (q i))-1
  have hdn (i : Fin 3) : d i ≠ 0 := by
    have hh := unit p (q i) (hp i)
    intro hz
    change Z p-a (q i)=0 at hz
    rw [hz,zero_mul] at hh
    exact zero_ne_one hh
  have hF (i : Fin 3) : ‖F i‖ ≤ 8*B*τ := by
    obtain ⟨s,hs,hc⟩ := hr i
    obtain ⟨hcZ,hcW⟩ := same_code_close hτ hZ hW hc
    exact square_grid_edge_error (Z r) (W r) (Z s) (W s) (a (q i)) (b (q i))
      hB hτ.le hτ₁ hZ hW (ha i) (hb i) hcZ hcW (unit s (q i) hs)
  have he (i : Fin 3) : (Z r-Z p)/d i+(W r-W p)*d i+(Z r-Z p)*(W r-W p)=F i :=
    difference_equation (Z p) (W p) (Z r) (W r) (a (q i)) (b (q i)) (unit p (q i) (hp i))
  exact no_separated_approximate_point (d 0) (d 1) (d 2) (Z r-Z p) (W r-W p)
    (F 0) (F 1) (F 2) (by linarith) hδ hτ.le (hdn 0) (hdn 1) (hdn 2)
    (hd 0) (hd 1) (hd 2) (hsep 0 1 (by decide)) (hsep 0 2 (by decide))
    (hsep 1 2 (by decide)) hpr (hF 0) (hF 1) (hF 2) (he 0) (he 1) (he 2) hmesh
end
end PlanarUnitDistances.QuantizedContradiction

namespace PlanarUnitDistances.BoundedGeometricCover
open FiniteLaw FiniteStarCoupling TripleCoupling FiniteQuantization
open scoped Classical
noncomputable section
variable {P Q K : Type*} [Field K] [NumberField K]

theorem cover (Z W : P → K) (a b : Q → K) (E : P → Q → Prop)
    (hu : ∀p q,E p q → (Z p-a q)*(W p-b q)=1)
    (hZinj : Function.Injective Z) (hainj : Function.Injective a)
    {B τ δ : ℝ} (hB : 2 ≤ B) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hδ : 0 < δ)
    (hmesh : τ < δ^4/(128*B^5)) (x : Outcome P Q × (K →ₐ[ℚ] ℂ)) :
    ∃i,bad Z W a b E B τ δ i x := by
  by_contra hn
  have hh (i : Fin 6) : ¬bad Z W a b E B τ δ i x := fun hi => hn ⟨i,hi⟩
  have hb (i : BigIndex) : ‖x.2 (big Z W a b x.1 i)‖ ≤ B :=
    le_of_not_gt (fun hi => hh 0 ⟨i,hi⟩)
  have hs (i : SmallIndex) (hi : small Z a x.1 i ≠ 0) : δ ≤ ‖x.2 (small Z a x.1 i)‖ :=
    le_of_not_gt (fun hz => hh 1 ⟨i,hi,hz⟩)
  have hp : point x.1 ≠ prediction x.1 := hh 2
  have hq (i j : Fin 3) (hij : i < j) : neighbor x.1 i ≠ neighbor x.1 j :=
    fun he => hh 3 ⟨(i,j),hij,he⟩
  have he (i : Fin 3) : E (point x.1) (neighbor x.1 i) := by
    by_contra hi
    exact hh 4 ⟨i,hi⟩
  have ha (i : Fin 3) : accept Z W E B τ x.2 (prediction x.1) (neighbor x.1 i) := by
    by_contra hi
    exact hh 5 ⟨i,hi⟩
  have hsep (i j : Fin 3) (hij : i < j) :
      δ ≤ ‖(x.2 (Z (point x.1))-x.2 (a (neighbor x.1 i)))-
        (x.2 (Z (point x.1))-x.2 (a (neighbor x.1 j)))‖ := by
    have hi : small Z a x.1 (.inr (i,j)) ≠ 0 := by
      simp only [small,sub_ne_zero]
      intro h
      exact hq i j hij (hainj (sub_right_inj.mp h))
    simpa only [small,map_sub] using hs (.inr (i,j)) hi
  have hpr : δ ≤ ‖x.2 (Z (prediction x.1))-x.2 (Z (point x.1))‖ := by
    have hi : small Z a x.1 (.inl ()) ≠ 0 := by
      rw [small,sub_ne_zero]
      exact fun h => hp (hZinj h).symm
    simpa only [small,map_sub] using hs (.inl ()) hi
  exact QuantizedContradiction.impossible (fun p => x.2 (Z p)) (fun p => x.2 (W p))
    (fun q => x.2 (a q)) (fun q => x.2 (b q)) E
    (fun p q h => by simpa only [map_mul,map_sub,map_one] using congrArg x.2 (hu p q h))
    (point x.1) (prediction x.1) (neighbor x.1) hB hτ hτ₁ hδ hmesh he ha
    (hb (.inl false)) (hb (.inl true)) (fun i => hb (.inr (i,.inl false)))
    (fun i => hb (.inr (i,.inl true)))
    (fun i => by simpa only [big,map_sub] using hb (.inr (i,.inr ()))) hsep hpr
end
end PlanarUnitDistances.BoundedGeometricCover

namespace PlanarUnitDistances.BoundedProbabilities
open Finset FiniteLaw FiniteStarCoupling TripleCoupling BoundedGeometricCover
open WeightedAbsoluteValues EmbeddingTails
open scoped Classical
noncomputable section
variable {P Q H K : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Field K] [NumberField K] [IsGalois ℚ K]

omit [Fintype P] [Fintype Q] [Fintype H] in
lemma height_sub (x y : K) : exactHeight K (x-y) ≤ exactHeight K x+exactHeight K y+Real.log 2 := by
  have hh := exactHeight_add_le K x (-y)
  rw [←sub_eq_add_neg,exactHeight_neg] at hh
  linarith

omit [IsGalois ℚ K] in
lemma big_mean (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    {C : ℝ} (hZ : avg (left π) (fun p => exactHeight K (Z p)) ≤ C)
    (hW : avg (left π) (fun p => exactHeight K (W p)) ≤ C)
    (ha : avg (right π) (fun q => exactHeight K (a q)) ≤ C)
    (hb : avg (right π) (fun q => exactHeight K (b q)) ≤ C)
    (hD : avg π (fun pq => exactHeight K (Z pq.1-a pq.2)) ≤ C) (i : BigIndex) :
    avg (law π h) (fun x => exactHeight K (big Z W a b x i)) ≤ C := by
  rcases i with i | ⟨j,i⟩
  · cases i
    · exact (predicted_point π h (fun p => exactHeight K (Z p))).le.trans hZ
    · exact (predicted_point π h (fun p => exactHeight K (W p))).le.trans hW
  · rcases i with i | i
    · cases i
      · exact (center π h j (fun q => exactHeight K (a q))).le.trans ha
      · exact (center π h j (fun q => exactHeight K (b q))).le.trans hb
    · cases i
      exact (edge π h j (fun p q => exactHeight K (Z p-a q))).le.trans hD

lemma small_mean (π : Law (P×Q)) (h : P → H) (Z : P → K) (a : Q → K)
    {C : ℝ} (hZ : avg (left π) (fun p => exactHeight K (Z p)) ≤ C)
    (ha : avg (right π) (fun q => exactHeight K (a q)) ≤ C) (i : SmallIndex) :
    avg (law π h) (fun x => exactHeight K (BoundedGeometricCover.small Z a x i)) ≤ 2*C+Real.log 2 := by
  rcases i with i | ⟨i,j⟩
  · cases i
    have hh:=avg_mono (law π h) (fun x => height_sub (Z (prediction x)) (Z (point x)))
    simp only [avg_add,avg_const] at hh
    rw [predicted_point π h (fun p => exactHeight K (Z p)),
      first π h (fun p => exactHeight K (Z p))] at hh
    exact hh.trans (by linarith)
  · have hs (x : Outcome P Q) : BoundedGeometricCover.small Z a x (.inr (i,j))=a (neighbor x j)-a (neighbor x i) := by
      simp only [BoundedGeometricCover.small]; ring
    have hh:=avg_mono (law π h) (fun x => height_sub (a (neighbor x j)) (a (neighbor x i)))
    simp only [avg_add,avg_const] at hh
    rw [center π h j (fun q => exactHeight K (a q)),center π h i (fun q => exactHeight K (a q))] at hh
    simp_rw [hs]
    exact hh.trans (by linarith)

omit [Fintype H] in
lemma large_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    {C B τ δ : ℝ} (hB : 1 < B) (E : P → Q → Prop)
    (hmean : ∀i,avg (law π h) (fun x => exactHeight K (big Z W a b x i)) ≤ C) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 0) ≤ 11*C/Real.log B := by
  have hh := large_family (law π h) (fun i x => big Z W a b x i) hB
  refine hh.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos hB).le)
  rw [avg_sum]
  calc
    _ ≤ ∑ _ : BigIndex,C := sum_le_sum (fun i _ => hmean i)
    _ = 11*C := by norm_num [BigIndex]

omit [Fintype H] in
lemma small_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    {C B τ δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) (E : P → Q → Prop)
    (hmean : ∀i,avg (law π h) (fun x => exactHeight K (BoundedGeometricCover.small Z a x i)) ≤ C) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 1) ≤ 10*C/Real.log (1/δ) := by
  have hh := small_family (law π h) (fun i x => small Z a x i) hδ hδ₁
  refine hh.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos ((one_lt_div hδ).mpr hδ₁)).le)
  rw [avg_sum]
  calc
    _ ≤ ∑ _ : SmallIndex,C := sum_le_sum (fun i _ => hmean i)
    _ = 10*C := by norm_num [SmallIndex]

lemma point_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (B τ δ : ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀p,(left π).val p ≤ d) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 2) ≤ (Fintype.card H:ℝ)*d := by
  have he : event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 2)=
      event (law π h) (fun x => point x=prediction x) := by
    unfold event
    rw [pair_avg]
    apply avg_congr
    intro x
    by_cases hx : point x=prediction x <;>
      simp only [BoundedGeometricCover.bad,hx,ite_true,ite_false,avg_const]
  rw [he]
  exact predicted_diagonal π h hd hm

omit [Fintype H] in
lemma centers_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (B τ δ : ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀p q,(row π p).val q ≤ d) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 3) ≤ 9*d := by
  have he : event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 3)=
      event (law π h) (fun x => ∃ij : Fin 3×Fin 3,ij.1 < ij.2 ∧ neighbor x ij.1=neighbor x ij.2) := by
    unfold event
    rw [pair_avg]
    apply avg_congr
    intro x
    by_cases hx : ∃ij : Fin 3×Fin 3,ij.1 < ij.2 ∧ neighbor x ij.1=neighbor x ij.2 <;>
      simp only [BoundedGeometricCover.bad,hx,ite_true,ite_false,avg_const]
  rw [he]
  refine (event_exists_le (law π h) _).trans ?_
  calc
    _ ≤ ∑ _ : Fin 3 × Fin 3,d := by
      apply sum_le_sum
      intro ij _
      by_cases hij : ij.1 < ij.2
      · refine (event_mono _ (fun _ hx => hx.2)).trans (center_diagonal π h ij.1 ij.2 (ne_of_lt hij) hm)
      · simpa only [hij,false_and,event_false] using hd
    _ = 9*d := by norm_num

omit [Fintype H] in
lemma nonedge_zero (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (hE : ∀p q,0 < π.val (p,q) → E p q) (B τ δ : ℝ) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 4) ≤ 0 := by
  have he : event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 4)=
      event (law π h) (fun x => ∃i,¬E (point x) (neighbor x i)) := by
    unfold event
    rw [pair_avg]
    apply avg_congr
    intro x
    by_cases hx : ∃i,¬E (point x) (neighbor x i) <;>
      simp only [BoundedGeometricCover.bad,hx,ite_true,ite_false,avg_const]
  rw [he]
  refine (event_exists_le (law π h) _).trans ?_
  apply sum_nonpos
  intro i _
  have hi : event (law π h) (fun x => ¬E (point x) (neighbor x i))=
      event π (fun pq => ¬E pq.1 pq.2) := by
    simpa only [avg_ite] using edge π h i (fun p q => if ¬E p q then (1:ℝ) else 0)
  rw [hi]
  unfold event avg
  apply sum_nonpos
  intro pq _
  by_cases hpos : 0 < π.val pq
  · simp [hE pq.1 pq.2 hpos]
  · have hz := le_antisymm (le_of_not_gt hpos) (π.nonneg pq)
    simp [hz]

omit [Fintype H] in
lemma mixture_col (π : Law (P×Q)) : mixture (right π) (col π)=left π := by
  apply law_ext
  intro p
  simp only [mixture,avg,col_weight,FiniteStarCoupling.left_val]

omit [Fintype H] in
lemma failure_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (B τ δ : ℝ) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 5) ≤ 3*failure π h Z W E B τ := by
  refine (event_exists_le _ _).trans ?_
  have he (i : Fin 3) : event (pair (law π h) (uniform (Embeddings K)))
      (fun x => ¬accept Z W E B τ x.2 (prediction x.1) (neighbor x.1 i)) = failure π h Z W E B τ := by
    rw [event,pair_avg,avg_comm]
    unfold failure
    apply avg_congr
    intro σ
    calc
      _ = event (law π h) (fun x => ¬accept Z W E B τ σ (prediction x) (neighbor x i)) := by
        unfold event
        apply avg_congr
        intro x
        split_ifs <;> simp_all only [not_true_eq_false,not_false_eq_true]
      _ = _ := by
        simpa only [avg_ite] using predicted_pair π h i (fun r q => if ¬accept Z W E B τ σ r q then (1:ℝ) else 0)
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,le_refl]
end
end PlanarUnitDistances.BoundedProbabilities

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

namespace PlanarUnitDistances.FiniteAcceptance
open Finset FiniteLaw CrossPrediction Real MeasureTheory
open scoped Classical
noncomputable section
variable {P Q H C T : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype C] [Fintype T] [DecidableEq H]

omit [Fintype P] [Fintype Q] [Fintype H] [Fintype T] [DecidableEq H] in
lemma feature_inner (c : C) (A : C → Prop) :
    inner ℝ (feature c) (test A)=(if A c then 1 else 0) := by
  rw [PiLp.inner_apply]
  simp [feature,test,RCLike.inner_apply]

omit [Fintype P] [Fintype Q] [Fintype H] [Fintype T] [DecidableEq H] in
lemma norm_feature (c : C) : ‖feature c‖ ≤ 1 := by
  have hh : inner ℝ (feature c) (feature c)=1 := by
    rw [PiLp.inner_apply]
    simp [feature]
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (feature c)]

omit [Fintype P] [Fintype Q] [Fintype H] [Fintype T] [DecidableEq H] in
lemma norm_test (A : C → Prop) : ‖test A‖ ≤ sqrt (Fintype.card C) := by
  have hh : inner ℝ (test A) (test A) ≤ (Fintype.card C:ℝ) := by
    rw [PiLp.inner_apply]
    calc
      _ ≤ ∑ _ : C,(1:ℝ) := by
        apply sum_le_sum
        intro c _
        simp only [test,WithLp.ofLp_toLp,RCLike.inner_apply,conj_trivial]
        split_ifs <;> norm_num
      _ = _ := by simp
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [sqrt_nonneg (Fintype.card C:ℝ),sq_sqrt (Nat.cast_nonneg (Fintype.card C))]

omit [Fintype T] in
lemma discrepancy_eq (κ : Law Q) (w : Q → Law P) (h : P → H)
    (hμ : ∀p,0 < (mixture κ w).val p) (c : P → C) (A : Q → C → Prop) :
    FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) h c feature (fun q => test (A q))=
      |actual κ w c A-predicted κ w h c A| := by
  have hm : FiniteInformation.marginal κ.val (fun q => (w q).val)=(mixture κ w).val := rfl
  unfold FiniteInformation.testDiscrepancy
  rw [hm]
  simp_rw [FiniteInformation.mean_posterior,posterior_cond _ _ _ (hμ _),sum_inner,
    real_inner_smul_left,inner_sub_left,sum_inner,real_inner_smul_left,feature_inner]
  simp only [actual,predicted,event,avg]
  congr 1
  simp only [mul_sub,sum_sub_distrib]

omit [Fintype H] [Fintype T] [Fintype C] [DecidableEq H] in
lemma actual_one (κ : Law Q) (w : Q → Law P) (c : P → C) (A : Q → C → Prop)
    (hpass : ∀q p,0 < κ.val q*(w q).val p → A q (c p)) : actual κ w c A=1 := by
  have he : actual κ w c A=avg κ (fun _ => (1:ℝ)) := by
    unfold actual event avg
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro q _
    conv_rhs => rw [←(w q).total, mul_sum]
    apply sum_congr rfl
    intro p _
    by_cases hz : κ.val q*(w q).val p=0
    · rw [←mul_assoc,hz,zero_mul]
    · have hp := lt_of_le_of_ne (mul_nonneg (κ.nonneg q) ((w q).nonneg p)) (Ne.symm hz)
      rw [ite_eq_left (hpass q p hp),mul_one]
  rw [he,avg_const]

omit [Fintype H] [DecidableEq H] in

theorem exists_history [Nonempty C] (κ : Law Q) (w : Q → Law P)
    (hμ : ∀p,0 < (mixture κ w).val p) (σ : Law T)
    (c : T → P → C) (A : T → Q → C → Prop)
    (hpass : ∀t q p,0 < κ.val q*(w q).val p → A t q (c t p))
    (K : ℕ) (hK : 0 < K) :
    ∃n<K,∃h : P → FiniteInformation.History C n,
      (univ.image h).card ≤ (Fintype.card C)^(K-1) ∧
      avg σ (fun t => 1-predicted κ w h (c t) (A t)) ≤
        4*sqrt (Fintype.card C)*(FiniteInformation.KL
          (FiniteInformation.wedge κ.val (fun q => (w q).val))
          (fun pp : P×P => (mixture κ w).val pp.1*(mixture κ w).val pp.2)/(K:ℝ))^(1/4:ℝ) := by
  let : MeasurableSpace C := ⊤
  let : MeasurableSpace T := ⊤
  have hδ : ∀n,Measurable (fun z : (P → FiniteInformation.History C n)×T =>
      FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) z.1
        (c z.2) feature (fun q => test (A z.2 q))) := by
    intro n
    let := history_singleton C n
    exact measurable_of_finite _
  obtain ⟨n,hn,h,hcard,hb⟩ := FiniteInformation.exists_prediction_history
    (ν := σ.pmf.toMeasure) κ.val (fun q => (w q).val) κ.nonneg (fun q => (w q).nonneg)
    κ.total (fun q => (w q).total) c (fun _ => feature) (fun t q => test (A t q))
    (fun _ => measurable_of_finite _) hδ (by norm_num : (0:ℝ) ≤ 1)
    (sqrt_nonneg (Fintype.card C)) (fun _ => norm_feature) (fun t q => norm_test (A t q)) K hK
  refine ⟨n,hn,h,hcard,?_⟩
  rw [integral_pmf] at hb
  simp only [discrepancy_eq κ w h hμ,actual_one κ w _ _ (hpass _),mul_one] at hb
  exact (avg_mono σ (fun t => le_abs_self (1-predicted κ w h (c t) (A t)))).trans hb
end
end PlanarUnitDistances.FiniteAcceptance

namespace PlanarUnitDistances.BoundedScaleFinite
open Finset FiniteLaw FiniteStarCoupling TripleCoupling BoundedGeometricCover
open WeightedAbsoluteValues BoundedProbabilities FiniteQuantization EmbeddingTails
open scoped Classical
noncomputable section
variable {P Q H K : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Field K] [NumberField K] [IsGalois ℚ K]

theorem obstruction (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (hE : ∀p q,0<π.val (p,q) → E p q)
    (hu : ∀p q,E p q → (Z p-a q)*(W p-b q)=1)
    (hZinj : Function.Injective Z) (hainj : Function.Injective a)
    {C B τ δ d m : ℝ} (hB : 2 ≤ B) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (hmesh : τ < δ^4/(128*B^5))
    (hZ : avg (left π) (fun p => exactHeight K (Z p)) ≤ C)
    (hW : avg (left π) (fun p => exactHeight K (W p)) ≤ C)
    (ha : avg (right π) (fun q => exactHeight K (a q)) ≤ C)
    (hb : avg (right π) (fun q => exactHeight K (b q)) ≤ C)
    (hD : avg π (fun pq => exactHeight K (Z pq.1-a pq.2)) ≤ C)
    (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hp : ∀p,(left π).val p ≤ d) (hq : ∀p q,(row π p).val q ≤ m) :
    1 ≤ 11*C/Real.log B+10*(2*C+Real.log 2)/Real.log (1/δ)+
      (Fintype.card H:ℝ)*d+9*m+3*BoundedProbabilities.failure π h Z W E B τ := by
  let μ := pair (law π h) (uniform (Embeddings K))
  have hall : event μ (fun x => ∃i,bad Z W a b E B τ δ i x)=1 := by
    calc
      _ = event μ (fun _ => True) := event_congr μ (fun x => iff_true_intro
        (cover Z W a b E hu hZinj hainj hB hτ hτ₁ hδ hmesh x))
      _ = 1 := event_true μ
  have hh := event_exists_le μ (bad Z W a b E B τ δ)
  rw [hall] at hh
  have h0 := large_bound π h Z W a b (τ := τ) (δ := δ) (show 1<B by linarith) E (big_mean π h Z W a b hZ hW ha hb hD)
  have h1 := small_bound π h Z W a b (B := B) (τ := τ) hδ hδ₁ E (small_mean π h Z a hZ ha)
  have h2 := point_bound π h Z W a b E B τ δ hd hp
  have h3 := centers_bound π h Z W a b E B τ δ hm hq
  have h4 := nonedge_zero π h Z W a b E hE B τ δ
  have h5 := failure_bound π h Z W a b E B τ δ
  norm_num [Fin.sum_univ_succ,Fin.succ] at hh
  change 1 ≤
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 0) +
    (event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 1) +
    (event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 2) +
    (event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 3) +
    (event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 4) +
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 5))))) at hh
  linarith

omit [Fintype H] in
theorem exists_small_failure (π : Law (P×Q)) (Z W : P → K) (E : P → Q → Prop)
    (hE : ∀p q,0<π.val (p,q) → E p q) (hμ : ∀p,0<(left π).val p)
    (B τ : ℝ) (k : ℕ) (hk : 0<k) :
    ∃n<k,∃h : P → FiniteInformation.History (Alphabet B τ) n,
      BoundedProbabilities.failure π h Z W E B τ ≤
        4*Real.sqrt (Fintype.card (Alphabet B τ))*
          (information π/(k:ℝ))^(1/4:ℝ) := by
  let c : Embeddings K → P → Alphabet B τ := fun σ p => code B τ (σ (Z p)) (σ (W p))
  let A : Embeddings K → Q → Alphabet B τ → Prop := fun σ q v => ∃s,E s q ∧ v=c σ s
  have hm : ∀p,0<(mixture (right π) (col π)).val p := by rwa [mixture_col]
  have hp : ∀σ q p,0<(right π).val q*(col π q).val p → A σ q (c σ p) := by
    intro σ q p hi
    rw [col_weight] at hi
    exact ⟨p,hE p q hi,rfl⟩
  obtain ⟨n,hn,h,_,hb⟩ := FiniteAcceptance.exists_history (right π) (col π) hm
    (uniform (Embeddings K)) c A hp k hk
  refine ⟨n,hn,h,?_⟩
  have hf : BoundedProbabilities.failure π h Z W E B τ =
      avg (uniform (Embeddings K)) (fun σ => 1-FiniteAcceptance.predicted (right π) (col π) h (c σ) (A σ)) := by
    unfold BoundedProbabilities.failure FiniteAcceptance.predicted
    rw [mixture_col]
    apply avg_congr
    intro σ
    simp only [event_compl,avg_sub,avg_const]
    rfl
  rw [hf]
  simpa only [mixture_col,information] using hb
end
end PlanarUnitDistances.BoundedScaleFinite

namespace PlanarUnitDistances.BoundedConstants
noncomputable section

theorem exists_cutoffs (C : ℝ) (hC : 0 ≤ C) :
    ∃B τ δ : ℝ,2 ≤ B ∧ 0 < τ ∧ τ ≤ 1 ∧ 0 < δ ∧ δ < 1 ∧
      τ < δ^4/(128*B^5) ∧
      11*C/Real.log B+10*(2*C+Real.log 2)/Real.log (1/δ) ≤ 1/4 := by
  let X := 1000*(C+1)
  let Y := 1000*(2*C+Real.log 2+1)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  let B := Real.exp X
  let δ := Real.exp (-Y)
  have hB : 2 ≤ B := by
    have he := Real.add_one_le_exp X
    dsimp [B,X] at *
    linarith
  have hδ : 0 < δ := Real.exp_pos _
  have hδ₁ : δ < 1 := by exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hY)
  have hm : 0 < δ^4/(128*B^5) := div_pos (pow_pos hδ _) (mul_pos (by norm_num) (pow_pos (by linarith) _))
  let τ := min (1/2:ℝ) (δ^4/(128*B^5)/2)
  refine ⟨B,τ,δ,hB,lt_min (by norm_num) (half_pos hm),?_,hδ,hδ₁,?_,?_⟩
  · exact (min_le_left _ _).trans (by norm_num)
  · exact (min_le_right _ _).trans_lt (half_lt_self hm)
  · have hLB : Real.log B=X := Real.log_exp _
    have hLD : Real.log (1/δ)=Y := by simp [δ,Real.log_inv]
    rw [hLB,hLD]
    have hx : 11*C/X ≤ 11/1000 := by
      apply (div_le_iff₀ hX).mpr
      dsimp [X]
      nlinarith
    have hy : 10*(2*C+Real.log 2)/Y ≤ 10/1000 := by
      apply (div_le_iff₀ hY).mpr
      dsimp [Y]
      nlinarith
    linarith
end
end PlanarUnitDistances.BoundedConstants

namespace PlanarUnitDistances.BoundedScaleUniform
open FiniteLaw FiniteStarCoupling WeightedAbsoluteValues FiniteQuantization
open scoped Classical
noncomputable section

theorem obstruction (C : ℝ) (hC : 0 ≤ C) :
    ∃M : ℕ,0<M ∧ ∀(P Q K : Type) [Fintype P] [Fintype Q]
      [Field K] [NumberField K] [IsGalois ℚ K],
    ∀(π : Law (P×Q)) (Z W : P → K) (a b : Q → K) (E : P → Q → Prop),
    (∀p q,0<π.val (p,q) → E p q) →
    (∀p q,E p q → (Z p-a q)*(W p-b q)=1) →
    Function.Injective Z → Function.Injective a →
    (∀p,0<(left π).val p) →
    avg (left π) (fun p => exactHeight K (Z p)) ≤ C →
    avg (left π) (fun p => exactHeight K (W p)) ≤ C →
    avg (right π) (fun q => exactHeight K (a q)) ≤ C →
    avg (right π) (fun q => exactHeight K (b q)) ≤ C →
    avg π (fun pq => exactHeight K (Z pq.1-a pq.2)) ≤ C →
    ∀d m : ℝ,0 ≤ d → 0 ≤ m →
    (∀p,(left π).val p ≤ d) → (∀p q,(row π p).val q ≤ m) →
    ∀k : ℕ,0<k →
      3/4 ≤ (M:ℝ)^k*d+9*m+12*Real.sqrt M*(BoundedScaleFinite.information π/(k:ℝ))^(1/4:ℝ) := by
  obtain ⟨B,τ,δ,hB,hτ,hτ₁,hδ,hδ₁,hmesh,htail⟩ := BoundedConstants.exists_cutoffs C hC
  let M := Fintype.card (Alphabet B τ)
  have hM : 0<M := Fintype.card_pos
  refine ⟨M,hM,?_⟩
  intro P Q K _ _ _ _ _ π Z W a b E hE hu hZi hai hμ hZ hW ha hb hD d m hd hm hp hq k hk
  obtain ⟨n,hn,h,hfail⟩ := BoundedScaleFinite.exists_small_failure π Z W E hE hμ B τ k hk
  have hh := BoundedScaleFinite.obstruction π h Z W a b E hE hu hZi hai hB hτ hτ₁ hδ hδ₁ hmesh
    hZ hW ha hb hD hd hm hp hq
  have hc : (Fintype.card (FiniteInformation.History (Alphabet B τ) n):ℝ) ≤ (M:ℝ)^k := by
    rw [FiniteInformation.history_card]
    norm_cast
    exact Nat.pow_le_pow_right hM (Nat.le_of_lt hn)
  have hcd := mul_le_mul_of_nonneg_right hc hd
  change BoundedProbabilities.failure π h Z W E B τ ≤
    4*Real.sqrt M*(BoundedScaleFinite.information π/(k:ℝ))^(1/4:ℝ) at hfail
  linarith
end
end PlanarUnitDistances.BoundedScaleUniform

namespace PlanarUnitDistances.LogHistory
open Filter
noncomputable section

lemma length_pos (M : ℕ) (t : ℝ) : 0<length M t := Nat.succ_pos _

lemma bounds {M : ℕ} (hM : 0<M) {t : ℝ} (ht : 1<t) :
    Real.log t/(4*(Real.log M+1)) ≤ (length M t:ℝ) ∧
      (length M t:ℝ) ≤ Real.log t/(4*(Real.log M+1))+1 ∧
      (M:ℝ)^(length M t) ≤ M*t^(1/4:ℝ) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hp : (0:ℝ)<M := by exact_mod_cast hM
  have hl : 0 ≤ Real.log M := Real.log_nonneg hm
  have ha : 0<4*(Real.log M+1) := by positivity
  have ht0 : 0<t := by linarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht.le
  have hf := Nat.floor_le (div_nonneg hlt ha.le)
  have hg := Nat.lt_floor_add_one (Real.log t/(4*(Real.log M+1)))
  have hk : (length M t:ℝ) ≤ Real.log t/(4*(Real.log M+1))+1 := by
    simp only [length,Nat.cast_add,Nat.cast_one]
    linarith
  refine ⟨by simpa only [length,Nat.cast_add,Nat.cast_one] using hg.le,hk,?_⟩
  have hcoef : Real.log M/(4*(Real.log M+1)) ≤ 1/4 := by
    apply (div_le_iff₀ ha).mpr
    linarith
  have he : (length M t:ℝ)*Real.log M ≤ Real.log M+(1/4:ℝ)*Real.log t := by
    have hh := mul_le_mul_of_nonneg_right hk hl
    have hj := mul_le_mul_of_nonneg_right hcoef hlt
    nlinarith [show Real.log t/(4*(Real.log M+1))*Real.log M=
      (Real.log M/(4*(Real.log M+1)))*Real.log t by ring]
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_nat_mul,Real.exp_log hp,Real.exp_add,Real.exp_log hp] at hh
  simpa only [Real.rpow_def_of_pos ht0,mul_comm (Real.log t) (1/4:ℝ)] using hh

lemma ratio_limit {M : ℕ} (hM : 0<M) (t D : ℕ → ℝ)
    (ht : Tendsto t atTop atTop)
    (hD0 : ∀ᶠn in atTop,0 ≤ D n)
    (hD : Tendsto (fun n => D n/Real.log (t n)) atTop (nhds 0)) :
    Tendsto (fun n => D n/(length M (t n):ℝ)) atTop (nhds 0) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hl : 0 ≤ Real.log M := Real.log_nonneg hm
  have ha : 0<4*(Real.log M+1) := by positivity
  have hupper : Tendsto (fun n => (4*(Real.log M+1))*(D n/Real.log (t n))) atTop (nhds 0) := by
    simpa only [mul_zero] using hD.const_mul (4*(Real.log M+1))
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hD0] with n hn
    exact div_nonneg hn (Nat.cast_nonneg _)
  · filter_upwards [hD0,ht.eventually_gt_atTop 1] with n hdn htn
    have hb := (bounds hM htn).1
    have hk : (0:ℝ)<length M (t n) := by exact_mod_cast length_pos M (t n)
    have hlt : 0<Real.log (t n) := Real.log_pos htn
    have hh : Real.log (t n) ≤ (length M (t n):ℝ)*(4*(Real.log M+1)) := (div_le_iff₀ ha).mp hb
    apply (div_le_iff₀ hk).mpr
    have he : (4*(Real.log M+1))*(D n/Real.log (t n))*(length M (t n):ℝ)=
        D n*((length M (t n):ℝ)*(4*(Real.log M+1)))/Real.log (t n) := by ring
    rw [he]
    apply (le_div_iff₀ hlt).mpr
    exact mul_le_mul_of_nonneg_left hh hdn

lemma density_limit {M : ℕ} (hM : 0<M) (t d : ℕ → ℝ)
    (ht : Tendsto t atTop atTop) (hd0 : ∀ᶠn in atTop,0 ≤ d n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ)) :
    Tendsto (fun n => (M:ℝ)^(length M (t n))*d n) atTop (nhds 0) := by
  have hv : Tendsto (fun n => (M:ℝ)*t n^(-1/4:ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_apply,neg_div] using ((_root_.tendsto_rpow_neg_atTop (y := (1/4:ℝ)) (by norm_num)).comp ht).const_mul (M:ℝ)
  apply squeeze_zero' _ _ hv
  · filter_upwards [hd0] with n hn
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg M) _) hn
  · filter_upwards [hd,ht.eventually_gt_atTop 1] with n hdn htn
    have hb := (bounds hM htn).2.2
    calc
      _ ≤ (M:ℝ)^(length M (t n))*t n^(-1/2:ℝ) :=
        mul_le_mul_of_nonneg_left hdn (pow_nonneg (Nat.cast_nonneg M) _)
      _ ≤ ((M:ℝ)*t n^(1/4:ℝ))*t n^(-1/2:ℝ) :=
        mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [mul_assoc,←Real.rpow_add (by linarith : 0<t n)]; norm_num
end
end PlanarUnitDistances.LogHistory

namespace PlanarUnitDistances.BoundedScaleExclusion
open FiniteLaw FiniteStarCoupling WeightedAbsoluteValues Filter
open scoped Classical
noncomputable section

lemma information_nonneg {P Q : Type} [Fintype P] [Fintype Q] (π : Law (P×Q)) :
    0 ≤ BoundedScaleFinite.information π := by
  have h := FiniteInformation.KL_nonneg _ _
    (FiniteInformation.wedge_nonneg _ _ (right π).nonneg (fun q => (col π q).nonneg))
    (fun pr : P×P => mul_nonneg ((mixture (right π) (col π)).nonneg pr.1)
      ((mixture (right π) (col π)).nonneg pr.2))
    (FiniteInformation.wedge_sum _ _ (right π).total (fun q => (col π q).total))
    (show ∑pr : P×P,(mixture (right π) (col π)).val pr.1*(mixture (right π) (col π)).val pr.2=1 by
      rw [Fintype.sum_prod_type,←Finset.sum_mul_sum,(mixture (right π) (col π)).total,one_mul])
    (FiniteInformation.wedge_ac _ _ (right π).nonneg (fun q => (col π q).nonneg))
  simpa only [BoundedProbabilities.mixture_col,BoundedScaleFinite.information] using h

theorem no_sequence {P Q K : ℕ → Type} [∀n,Fintype (P n)] [∀n,Fintype (Q n)]
    [∀n,Field (K n)] [∀n,NumberField (K n)] [∀n,IsGalois ℚ (K n)]
    (π : ∀n,Law (P n×Q n)) (Z W : ∀n,P n → K n) (a b : ∀n,Q n → K n)
    (E : ∀n,P n → Q n → Prop)
    (hE : ∀n p q,0<(π n).val (p,q) → E n p q)
    (hu : ∀n p q,E n p q → (Z n p-a n q)*(W n p-b n q)=1)
    (hZi : ∀n,Function.Injective (Z n)) (hai : ∀n,Function.Injective (a n))
    (hμ : ∀n p,0<(left (π n)).val p)
    {C : ℝ} (hC : 0 ≤ C)
    (hZ : ∀n,avg (left (π n)) (fun p => exactHeight (K n) (Z n p)) ≤ C)
    (hW : ∀n,avg (left (π n)) (fun p => exactHeight (K n) (W n p)) ≤ C)
    (ha : ∀n,avg (right (π n)) (fun q => exactHeight (K n) (a n q)) ≤ C)
    (hb : ∀n,avg (right (π n)) (fun q => exactHeight (K n) (b n q)) ≤ C)
    (hΔ : ∀n,avg (π n) (fun pq => exactHeight (K n) (Z n pq.1-a n pq.2)) ≤ C)
    (t d m : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hd0 : ∀n,0 ≤ d n) (hm0 : ∀n,0 ≤ m n)
    (hp : ∀n p,(left (π n)).val p ≤ d n)
    (hq : ∀n p q,(row (π n) p).val q ≤ m n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ))
    (hm : Tendsto m atTop (nhds 0))
    (hinfo : Tendsto (fun n => BoundedScaleFinite.information (π n)/Real.log (t n)) atTop (nhds 0)) :
    False := by
  obtain ⟨M,hM,hfinite⟩ := BoundedScaleUniform.obstruction C hC
  let k : ℕ → ℕ := fun n => LogHistory.length M (t n)
  have hfirst : Tendsto (fun n => (M:ℝ)^(k n)*d n) atTop (nhds 0) :=
    LogHistory.density_limit hM t d ht (Eventually.of_forall hd0) hd
  have hratio : Tendsto (fun n => BoundedScaleFinite.information (π n)/(k n:ℝ)) atTop (nhds 0) :=
    LogHistory.ratio_limit hM t _ ht (Eventually.of_forall (fun n => information_nonneg (π n))) hinfo
  have hlast : Tendsto (fun n => 12*Real.sqrt M*(BoundedScaleFinite.information (π n)/(k n:ℝ))^(1/4:ℝ))
      atTop (nhds 0) := by
    simpa only [mul_zero] using (hratio.rpow_const_nhds_zero (by norm_num : (0:ℝ)<1/4)).const_mul (12*Real.sqrt M)
  have hsum : Tendsto (fun n => (M:ℝ)^(k n)*d n+9*m n+
      12*Real.sqrt M*(BoundedScaleFinite.information (π n)/(k n:ℝ))^(1/4:ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero] using (hfirst.add (hm.const_mul 9)).add hlast
  have hbound : ∀n,3/4 ≤ (M:ℝ)^(k n)*d n+9*m n+
      12*Real.sqrt M*(BoundedScaleFinite.information (π n)/(k n:ℝ))^(1/4:ℝ) := by
    intro n
    exact hfinite (P n) (Q n) (K n) (π n) (Z n) (W n) (a n) (b n) (E n)
      (hE n) (hu n) (hZi n) (hai n) (hμ n) (hZ n) (hW n) (ha n) (hb n) (hΔ n)
      (d n) (m n) (hd0 n) (hm0 n) (hp n) (hq n) (k n) (LogHistory.length_pos M (t n))
  have hh : (3/4:ℝ) ≤ 0 := ge_of_tendsto hsum (Eventually.of_forall hbound)
  norm_num at hh
end
end PlanarUnitDistances.BoundedScaleExclusion

namespace PlanarUnitDistances.ScaleDivergence
open FiniteLaw FiniteStarCoupling WeightedAbsoluteValues Filter
open scoped Classical
noncomputable section

theorem not_bounded {P Q K : ℕ → Type} [∀n,Fintype (P n)] [∀n,Fintype (Q n)]
    [∀n,Field (K n)] [∀n,NumberField (K n)] [∀n,IsGalois ℚ (K n)]
    (π : ∀n,Law (P n×Q n)) (z w : ∀n,P n⊕Q n → K n)
    (E : ∀n,P n → Q n → Prop)
    (hE : ∀n p q,0<(π n).val (p,q) → E n p q)
    (hu : ∀n p q,E n p q → (z n (.inl p)-z n (.inr q))*(w n (.inl p)-w n (.inr q))=1)
    (hzi : ∀n,Function.Injective (z n ∘ Sum.inl))
    (hzq : ∀n,Function.Injective (z n ∘ Sum.inr))
    (hμ : ∀n p,0<(left (π n)).val p)
    (S : ∀n,Finset (K n))
    (hS : ∀n p q,E n p q → z n (.inl p)-z n (.inr q)∈S n)
    {C R : ℝ} (hc : ∀n,LocalHeightTransfer.LabelControl C (fun p q => (π n).val (p,q)))
    (hR : ∀n,LevelScale.scale (π n) (S n) (fun pq => z n (.inl pq.1)-z n (.inr pq.2)) ≤ R)
    (t d m : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hd0 : ∀n,0 ≤ d n) (hm0 : ∀n,0 ≤ m n)
    (hp : ∀n p,(left (π n)).val p ≤ d n)
    (hq : ∀n p q,(row (π n) p).val q ≤ m n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ))
    (hm : Tendsto m atTop (nhds 0))
    (hinfo : Tendsto (fun n => BoundedScaleFinite.information (π n)/Real.log (t n)) atTop (nhds 0)) :
    False := by
  have hn (n : ℕ) := NormalizedScale.coordinates (K n) (π n) (z n) (w n) (E n)
    (hE n) (hu n) (hzi n) (hzq n) (S n) (hS n) (hc n) (hR n)
  choose Z W a b hu' hZi hai hb using hn
  let A := 4*((C+1)*(Real.log 2+2))*(R+1)+4*R+2*Real.log 2
  exact BoundedScaleExclusion.no_sequence π Z W a b E hE hu' hZi hai hμ
    (C := max A 0) (le_max_right _ _)
    (fun n => (hb n).1.trans (le_max_left _ _))
    (fun n => (hb n).2.1.trans (le_max_left _ _))
    (fun n => (hb n).2.2.1.trans (le_max_left _ _))
    (fun n => (hb n).2.2.2.1.trans (le_max_left _ _))
    (fun n => (hb n).2.2.2.2.trans (le_max_left _ _))
    t d m ht hd0 hm0 hp hq hd hm hinfo

theorem tends_to_infinity {P Q K : ℕ → Type} [∀n,Fintype (P n)] [∀n,Fintype (Q n)]
    [∀n,Field (K n)] [∀n,NumberField (K n)] [∀n,IsGalois ℚ (K n)]
    (π : ∀n,Law (P n×Q n)) (z w : ∀n,P n⊕Q n → K n)
    (E : ∀n,P n → Q n → Prop)
    (hE : ∀n p q,0<(π n).val (p,q) → E n p q)
    (hu : ∀n p q,E n p q → (z n (.inl p)-z n (.inr q))*(w n (.inl p)-w n (.inr q))=1)
    (hzi : ∀n,Function.Injective (z n ∘ Sum.inl))
    (hzq : ∀n,Function.Injective (z n ∘ Sum.inr))
    (hμ : ∀n p,0<(left (π n)).val p)
    (S : ∀n,Finset (K n))
    (hS : ∀n p q,E n p q → z n (.inl p)-z n (.inr q)∈S n)
    {C : ℝ} (hc : ∀n,LocalHeightTransfer.LabelControl C (fun p q => (π n).val (p,q)))
    (t d m : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hd0 : ∀n,0 ≤ d n) (hm0 : ∀n,0 ≤ m n)
    (hp : ∀n p,(left (π n)).val p ≤ d n)
    (hq : ∀n p q,(row (π n) p).val q ≤ m n)
    (hd : ∀ᶠn in atTop,d n ≤ t n^(-1/2:ℝ))
    (hm : Tendsto m atTop (nhds 0))
    (hinfo : Tendsto (fun n => BoundedScaleFinite.information (π n)/Real.log (t n)) atTop (nhds 0)) :
    Tendsto (fun n => LevelScale.scale (π n) (S n) (fun pq => z n (.inl pq.1)-z n (.inr pq.2)))
      atTop atTop := by
  apply tendsto_atTop.2
  intro R
  by_contra h
  have hh : ∀N : ℕ,∃n,N ≤ n ∧
      LevelScale.scale (π n) (S n) (fun pq => z n (.inl pq.1)-z n (.inr pq.2)) < R := by
    simpa only [eventually_atTop,not_exists,not_forall,not_le,exists_prop] using h
  choose f hf hR using hh
  have hft : Tendsto f atTop atTop := tendsto_atTop_mono hf tendsto_id
  exact not_bounded (fun n => π (f n)) (fun n => z (f n)) (fun n => w (f n))
    (fun n => E (f n)) (fun n => hE (f n)) (fun n => hu (f n))
    (fun n => hzi (f n)) (fun n => hzq (f n)) (fun n => hμ (f n))
    (fun n => S (f n)) (fun n => hS (f n)) (fun n => hc (f n)) (fun n => (hR n).le)
    (t ∘ f) (d ∘ f) (m ∘ f) (ht.comp hft) (fun n => hd0 (f n)) (fun n => hm0 (f n))
    (fun n => hp (f n)) (fun n => hq (f n)) (hft.eventually hd) (hm.comp hft) (hinfo.comp hft)
end
end PlanarUnitDistances.ScaleDivergence

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
lemma point_bound (n : ℕ) (p : s.P n) : (left (graph s n)).val p≤ s.t n^(-1/2:ℝ) := by
  rw [graph,GeometricLaw.left_eq]
  exact (s.good n).atomUpper p p.property
lemma row_bound (n : ℕ) (p : s.P n) (q : s.Q n) :
    (row (graph s n) p).val q≤1/(s.t n^(1/2:ℝ)) := by
  have hp := (s.good n).point_degree_pos p
  have he := (s.good n).positive
  have hb := (le_div_iff₀ he).mp ((s.good n).atomP p p.property)
  have hd : s.t n^(1/2:ℝ)≤CircleIncidence.degree (s.Q n) p :=
    (s.good n).degreeP.trans (by simpa only [div_mul_eq_mul_div] using hb)
  exact (GeometricLaw.row_le _ _ he p q hp).trans
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith [s.large n,Nat.cast_nonneg (α:=ℝ) n]) _) hd)
lemma information_eq (n : ℕ) : BoundedScaleFinite.information (graph s n)=
    IncidenceSequence.information (s.P n) (s.Q n) := by
  unfold BoundedScaleFinite.information IncidenceSequence.information
  rw [graph,GeometricLaw.wedge_eq _ _ _ ((s.good n).center_degree_pos)]
  simp only [GeometricLaw.graph,UniformGraphLaw.left_eq]
lemma label_control : ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
    LocalHeightTransfer.LabelControl C (fun p q => (graph s n).val (p,q)) := by
  obtain ⟨ξ₀,C,hξ,hC,hc⟩ := GlobalLabelControl.constants (by norm_num : (0:ℝ)<27/50)
    (by norm_num : (0:ℝ)<1/25)
  refine ⟨C,hC,?_⟩
  filter_upwards [s.error_limit.eventually_le_const hξ] with n hn
  apply hc (s.P n) (s.Q n) (graph s n)
    (GeometricLaw.counting (s.P n) (GeometricLaw.card_pos _ _ (s.good n).positive).1)
    (GeometricLaw.counting (s.Q n) (GeometricLaw.card_pos _ _ (s.good n).positive).2)
  · intro p
    rw [graph,GeometricLaw.left_eq]
    simpa only [GeometricLaw.counting,mul_one_div] using (s.good n).atomP p p.property
  · intro q
    rw [graph,GeometricLaw.right_eq]
    simpa only [GeometricLaw.counting,mul_one_div] using (s.good n).atomQ q q.property
  · exact (s.good n).error_nonneg
  · exact hn
  · exact GeometricLaw.expansion _ _ (s.good n).positive (s.good n).expansion

theorem scale_limit_oai : Tendsto (scale s) atTop atTop := by
  obtain ⟨C,_,hc⟩ := label_control s
  obtain ⟨N,hN⟩ := eventually_atTop.mp hc
  have hf : Tendsto (fun n : ℕ => n+N) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n N) tendsto_id
  have ht := s.tendsto.comp hf
  have hm : Tendsto (fun n => 1/(s.t (n+N)^(1/2:ℝ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp ht)
  have hh := ScaleDivergence.tends_to_infinity
    (fun n => graph s (n+N)) (fun n => (model s (n+N)).z) (fun n => (model s (n+N)).w)
    (fun n => GeometricLaw.E (s.P (n+N)) (s.Q (n+N)))
    (fun n => support s (n+N)) (fun n => (model s (n+N)).unit_identity)
    (fun n => (model s (n+N)).point_injective) (fun n => (model s (n+N)).center_injective)
    (fun n => positive s (n+N))
    (fun n => (model s (n+N)).support) (fun n p q _ => (model s (n+N)).sub_mem (.inl p) (.inr q))
    (fun n => hN (n+N) (Nat.le_add_left N n))
    (fun n => s.t (n+N)) (fun n => s.t (n+N)^(-1/2:ℝ))
    (fun n => 1/(s.t (n+N)^(1/2:ℝ))) ht
    (fun n => Real.rpow_nonneg (by linarith [s.large (n+N),Nat.cast_nonneg (α:=ℝ) (n+N)]) _)
    (fun n => div_nonneg zero_le_one (Real.rpow_nonneg (by linarith [s.large (n+N),Nat.cast_nonneg (α:=ℝ) (n+N)]) _)) (fun n => point_bound s (n+N)) (fun n => row_bound s (n+N))
    (Eventually.of_forall (fun _ => le_rfl)) hm
    (by
      simp only [information_eq]
      exact s.information_limit.comp hf)
  exact (tendsto_add_atTop_iff_nat N).mp hh
end
end PlanarUnitDistances.IncidenceScale

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.IncidenceScale.scale_limit_oai := @OAI.PlanarUnitDistances.IncidenceScale.scale_limit_oai
