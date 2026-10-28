-- Prove2me | solution 1 for OAI.SmoothObstruction.WordHierarchy.no_switching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:21:26.862081+00:00
-- url     : https://prove2.me/submissions/37492dd7-4b05-44fc-a28d-772c08322333

import Mathlib
import Definitions.Def_OAIQ5T3000

section
-- module Solutions.OAIQ5_T3.Compat
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_FiniteEntropy
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction

namespace FiniteEntropy

variable {α β γ : Type*}

/-- The pointwise log-sum bound, including the zero convention. -/
lemma negMulLog_le_cross {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ -p * Real.log q + q - p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · subst p
    simp only [Real.negMulLog_zero, neg_zero, zero_mul, zero_add, sub_zero]
    exact hq.le
  · have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h hp.le
    simp only [mul_sub, mul_one, mul_div_cancel₀ _ hp.ne'] at h'
    simp only [Real.negMulLog_def]
    nlinarith

/-- Entropy of a nonnegative vector of total mass `θ` on a finite set. -/
lemma sum_negMulLog_le_mass (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤
      Real.negMulLog (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * Real.log s.card := by
  classical
  let θ := ∑ i ∈ s, p i
  have hθ : 0 ≤ θ := sum_nonneg hp
  by_cases hzero : θ = 0
  · have hz (i : α) (hi : i ∈ s) : p i = 0 :=
      (sum_eq_zero_iff_of_nonneg hp).mp hzero i hi
    simp [show ∑ i ∈ s, p i = 0 from hzero, sum_congr rfl (fun i hi => congrArg Real.negMulLog (hz i hi))]
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hs : s.Nonempty := by
      by_contra h
      have hempty := not_nonempty_iff_eq_empty.mp h
      simp [θ, hempty] at hzero
    have hc : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
    have hq : 0 < θ / s.card := div_pos hθpos hc
    calc
      _ ≤ ∑ i ∈ s, (-p i * Real.log (θ / s.card) + θ / s.card - p i) :=
        sum_le_sum (fun i hi => negMulLog_le_cross (hp i hi) hq)
      _ = -θ * Real.log (θ / s.card) := by
        simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
        rw [← sum_mul, sum_neg_distrib]
        change -θ * Real.log (θ / s.card) + s.card * (θ / s.card) - θ = _
        rw [mul_div_cancel₀ _ hc.ne']
        ring
      _ = _ := by
        rw [Real.log_div hθpos.ne' hc.ne']
        simp only [Real.negMulLog_def]
        change -θ * (Real.log θ - Real.log s.card) = -θ * Real.log θ + θ * Real.log s.card
        ring

lemma entropy_nonneg [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) : 0 ≤ natEntropy p := by
  apply sum_nonneg
  intro a _
  apply Real.negMulLog_nonneg (hp a)
  calc
    p a ≤ ∑ a, p a := single_le_sum (fun a _ => hp a) (mem_univ a)
    _ = 1 := hpsum

lemma entropy_le_log_card [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) : natEntropy p ≤ Real.log (Fintype.card α) := by
  simpa [natEntropy, hpsum] using sum_negMulLog_le_mass univ p (fun a _ => hp a)

/-- Concavity of finite entropy, without any independence assumptions. -/
lemma entropy_mixture [Fintype α] [Fintype β] (w : α → ℝ) (p : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) (hp : ∀ a b, 0 ≤ p a b) :
    ∑ a, w a * natEntropy (p a) ≤ natEntropy (fun b => ∑ a, w a * p a b) := by
  simp only [natEntropy, mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
    (t := univ) (w := w) (p := fun a => p a b) (fun a _ => hw a) hsum
    (fun a _ => hp a b)

/-- Exact entropy chain rule for a finite mixture with the component label retained. -/
lemma entropy_joint [Fintype α] [Fintype β] (w : α → ℝ) (p : α → β → ℝ)
    (hsum : ∀ a, ∑ b, p a b = 1) :
    natEntropy (fun ab : α × β => w ab.1 * p ab.1 ab.2) =
      natEntropy w + ∑ a, w a * natEntropy (p a) := by
  simp only [natEntropy, Fintype.sum_prod_type, Real.negMulLog_mul, sum_add_distrib]
  simp_rw [← sum_mul, hsum, one_mul, ← mul_sum]

lemma negMulLog_le_log_two {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    Real.negMulLog x ≤ Real.log 2 := by
  have h := entropy_le_log_card (p := fun b : Bool => if b then x else 1 - x)
    (by intro b; cases b <;> simp <;> linarith) (by simp)
  simp only [natEntropy, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    Fintype.card_bool, Nat.cast_ofNat] at h
  have hn := Real.negMulLog_nonneg (sub_nonneg.mpr hx') (by linarith : 1 - x ≤ 1)
  linarith

lemma heavyMass_nonneg [Fintype α] (a : ℝ) {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) :
    0 ≤ heavyMass a p := by
  apply sum_nonneg
  intro i _
  split_ifs
  · exact hp i
  · exact le_rfl

lemma heavyMass_le_one [Fintype α] (a : ℝ) {p : α → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : heavyMass a p ≤ 1 := by
  calc
    _ ≤ ∑ i, p i := sum_le_sum (by intro i _; split_ifs <;> simp_all)
    _ = 1 := hsum

/-- The source heavy--light entropy estimate, with its literal one-bit cost. -/
theorem entropy_le_heavy [Fintype α] [Nonempty α] {p : α → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (a : ℝ) :
    natEntropy p ≤ Real.log 2 +
      (1 - (1 - a) * heavyMass a p) * Real.log (Fintype.card α) := by
  classical
  let H : Finset α := univ.filter (fun i => Real.exp (-a * Real.log (Fintype.card α)) < p i)
  let L : Finset α := univ \ H
  let θ := heavyMass a p
  have hθ : θ = ∑ i ∈ H, p i := by simp [θ, heavyMass, H, sum_filter]
  have hθ₀ : 0 ≤ θ := heavyMass_nonneg a hp
  have hθ₁ : θ ≤ 1 := heavyMass_le_one a hp hsum
  have hLH : Disjoint L H := sdiff_disjoint
  have hLU : L ∪ H = univ := sdiff_union_of_subset (subset_univ H)
  have hsumL : ∑ i ∈ L, p i = 1 - θ := by
    have h := sum_union hLH (f := p)
    rw [hLU, hsum, ← hθ] at h
    linarith
  have hheavy : ∑ i ∈ H, Real.negMulLog (p i) ≤
      a * θ * Real.log (Fintype.card α) := by
    calc
      _ ≤ ∑ i ∈ H, a * p i * Real.log (Fintype.card α) := by
        apply sum_le_sum
        intro i hi
        have hi' := (mem_filter.mp hi).2
        have hip : 0 < p i := (Real.exp_pos _).trans hi'
        have hlog : -a * Real.log (Fintype.card α) ≤ Real.log (p i) := by
          rw [← Real.log_exp (-a * Real.log (Fintype.card α))]
          exact Real.log_le_log (Real.exp_pos _) hi'.le
        have hh := mul_le_mul_of_nonneg_left hlog (hp i)
        rw [Real.negMulLog_def]
        nlinarith
      _ = _ := by rw [← sum_mul, ← mul_sum, ← hθ]
  have hlight : ∑ i ∈ L, Real.negMulLog (p i) ≤
      Real.log 2 + (1 - θ) * Real.log (Fintype.card α) := by
    have hbase := sum_negMulLog_le_mass L p (fun i _ => hp i)
    rw [hsumL] at hbase
    have hc : Real.log L.card ≤ Real.log (Fintype.card α) := by
      by_cases he : L = ∅
      · simp only [he, card_empty, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›)
      · apply Real.log_le_log (Nat.cast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr he)))
        exact_mod_cast card_le_card (subset_univ L)
    calc
      _ ≤ _ := hbase
      _ ≤ _ := add_le_add (negMulLog_le_log_two (by linarith) (by linarith))
        (mul_le_mul_of_nonneg_left hc (by linarith))
  have hsplit := sum_union hLH (f := fun i => Real.negMulLog (p i))
  rw [hLU] at hsplit
  have hfinal := add_le_add hlight hheavy
  rw [← hsplit] at hfinal
  dsimp [natEntropy]
  dsimp [θ] at hfinal
  nlinarith

end FiniteEntropy
end SmoothObstruction

namespace SmoothObstruction.FiniteEntropy

open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

omit [Fintype α] in
lemma leftMass_nonneg {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) :
    0 ≤ leftMass p a := sum_nonneg (fun _ _ => hp _)
omit [Fintype β] in
lemma rightMass_nonneg {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (b : β) :
    0 ≤ rightMass p b := sum_nonneg (fun _ _ => hp _)
omit [Fintype α] in
lemma le_leftMass {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) (b : β) :
    p (a,b) ≤ leftMass p a := single_le_sum (fun _ _ => hp _) (mem_univ b)
omit [Fintype β] in
lemma le_rightMass {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) (b : β) :
    p (a,b) ≤ rightMass p b := single_le_sum (fun a _ => hp (a,b)) (mem_univ a)
lemma sum_leftMass (p : α × β → ℝ) : ∑ a, leftMass p a = ∑ x, p x := by
  simp only [leftMass, Fintype.sum_prod_type]
lemma sum_rightMass (p : α × β → ℝ) : ∑ b, rightMass p b = ∑ x, p x := by
  simp only [rightMass, Fintype.sum_prod_type]
  exact sum_comm

/-- Finite joint entropy subadditivity, including zero marginal masses.
This is the unconditional entropy input for block-rate existence. -/
theorem entropy_subadd {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    natEntropy p ≤ natEntropy (leftMass p) + natEntropy (rightMass p) := by
  have hpoint (a : α) (b : β) : Real.negMulLog (p (a,b)) ≤
      -p (a,b) * Real.log (leftMass p a) - p (a,b) * Real.log (rightMass p b) +
        leftMass p a * rightMass p b - p (a,b) := by
    rcases eq_or_lt_of_le (hp (a,b)) with he | he
    · rw [← he]
      simp only [Real.negMulLog_zero, neg_zero, zero_mul, sub_zero, zero_add]
      exact mul_nonneg (leftMass_nonneg hp a) (rightMass_nonneg hp b)
    · have ha := he.trans_le (le_leftMass hp a b)
      have hb := he.trans_le (le_rightMass hp a b)
      have h := negMulLog_le_cross (hp (a,b)) (mul_pos ha hb)
      rw [Real.log_mul ha.ne' hb.ne'] at h
      nlinarith
  have hA : (∑ a, ∑ b, -p (a,b) * Real.log (leftMass p a)) = natEntropy (leftMass p) := by
    simp only [← sum_mul, sum_neg_distrib, leftMass, natEntropy, Real.negMulLog_def]
  have hB : (∑ a, ∑ b, -p (a,b) * Real.log (rightMass p b)) = natEntropy (rightMass p) := by
    rw [sum_comm]
    simp only [← sum_mul, sum_neg_distrib, rightMass, natEntropy, Real.negMulLog_def]
  have hAB : (∑ a, ∑ b, leftMass p a * rightMass p b) = 1 := by
    simp only [← mul_sum, sum_rightMass, sum_leftMass, hs, mul_one]
  calc
    _ ≤ ∑ a, ∑ b, (-p (a,b) * Real.log (leftMass p a) -
        p (a,b) * Real.log (rightMass p b) + leftMass p a * rightMass p b - p (a,b)) := by
      simp only [natEntropy, Fintype.sum_prod_type]
      exact sum_le_sum (fun a _ => sum_le_sum (fun b _ => hpoint a b))
    _ = _ := by
      simp only [sub_eq_add_neg, neg_mul, sum_add_distrib, sum_neg_distrib] at hA hB ⊢
      have hpSum : (∑ a, ∑ b, p (a,b)) = 1 := by simpa only [Fintype.sum_prod_type] using hs
      rw [hA, hB, hAB, hpSum]
      ring

lemma entropy_push_le {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (f : α → β) :
    natEntropy (pushMass p f) ≤ natEntropy p := by
  classical
  have hupper (a : α) : p a ≤ pushMass p f (f a) := by
    have h := single_le_sum (s := univ) (a := a)
      (f := fun x => if f x = f a then p x else 0)
      (by intro x _; split_ifs; exact hp x; exact le_rfl) (mem_univ a)
    simpa [pushMass] using h
  have hpoint (a : α) : -p a * Real.log (pushMass p f (f a)) ≤ Real.negMulLog (p a) := by
    rcases eq_or_lt_of_le (hp a) with ha | ha
    · rw [← ha]; simp
    · have hm := Real.log_le_log ha (hupper a)
      simpa only [Real.negMulLog_def] using mul_le_mul_of_nonpos_left hm (by linarith : -p a ≤ 0)
  have heq : natEntropy (pushMass p f) = ∑ a, -p a * Real.log (pushMass p f (f a)) := by
    unfold natEntropy
    simp only [Real.negMulLog_def]
    calc
      _ = ∑ b, ∑ a, -(if f a = b then p a else 0) * Real.log (pushMass p f b) := by
        apply sum_congr rfl
        intro b _
        rw [← sum_mul, sum_neg_distrib]
        rfl
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        simp [ite_mul]
  rw [heq]
  exact sum_le_sum (fun a _ => hpoint a)

end SmoothObstruction.FiniteEntropy

end

section

namespace SmoothObstruction.FiniteEntropy
open Finset
variable {α : Type*} [Fintype α]

lemma entropy_lower_mass {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) :
    Real.negMulLog (∑ a, p a) ≤ natEntropy p := by
  have hh := entropy_push_le hp (fun _ : α => ())
  simpa [natEntropy,pushMass] using hh

lemma entropy_add_le {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) :
    natEntropy (fun a => p a+q a) ≤ natEntropy p+natEntropy q := by
  let joint : Bool × α → ℝ := fun ba => if ba.1 then q ba.2 else p ba.2
  have h := entropy_push_le (p:=joint) (by intro ba; dsimp [joint]; split <;> [exact hq _; exact hp _]) Prod.snd
  have hpush : pushMass joint Prod.snd = fun a => p a+q a := by
    classical
    funext a
    simp [pushMass,joint,Fintype.sum_prod_type,add_comm]
  rw [hpush] at h
  simpa [joint,natEntropy,Fintype.sum_prod_type,Fintype.sum_bool,add_comm] using h

/-- Removing part of a probability law can increase unnormalized entropy
only by the entropy term of the retained mass. -/
lemma entropy_common_le {p m : α → ℝ} (_hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a=1)
    (hm : ∀ a, 0 ≤ m a) (hmle : ∀ a, m a ≤ p a) :
    natEntropy m ≤ natEntropy p + Real.negMulLog (∑ a,m a) := by
  let r := fun a => p a-m a
  have hr : ∀ a, 0 ≤ r a := fun a => sub_nonneg.mpr (hmle a)
  let joint : Bool × α → ℝ := fun ba => if ba.1 then r ba.2 else m ba.2
  have hj : ∀ ba, 0≤joint ba := by intro ba; dsimp [joint]; split <;> [exact hr _; exact hm _]
  have hjs : ∑ ba, joint ba=1 := by
    simp only [joint,Fintype.sum_prod_type,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
    simp only [r,sum_sub_distrib,hs]
    ring
  have hh := entropy_subadd hj hjs
  have hrm : rightMass joint = p := by
    funext a
    simp [rightMass,joint,r]
  have hleft : natEntropy (leftMass joint) =
      Real.negMulLog (∑ a,m a)+Real.negMulLog (∑ a,r a) := by
    simp [natEntropy,leftMass,joint,add_comm]
  have hjh : natEntropy joint=natEntropy m+natEntropy r := by
    simp [natEntropy,joint,Fintype.sum_prod_type,add_comm]
  rw [hrm,hleft,hjh] at hh
  have hlo := entropy_lower_mass hr
  linarith

/-- Shannon's continuity estimate from a literal total-variation distance.
No coupling or chain-rule inequality is assumed. Natural logs here; division
by log 2 gives precisely the manuscript's one-bit cost. -/
theorem entropy_tv {p q : α → ℝ} (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hps : ∑ a,p a=1) (hqs : ∑ a,q a=1) :
    natEntropy q ≤ natEntropy p+Real.log 2+
      ((1/2:ℝ)*∑ a,|p a-q a|)*Real.log (Fintype.card α) := by
  let m := fun a => min (p a) (q a)
  let r := fun a => q a-m a
  have hm : ∀ a,0 ≤ m a := fun a => le_min (hp a) (hq a)
  have hr : ∀ a,0 ≤ r a := fun a => sub_nonneg.mpr (min_le_right _ _)
  have hc := entropy_common_le hp hps hm (fun a => min_le_left _ _)
  have ha := entropy_add_le hm hr
  have hmr : (fun a => m a+r a)=q := by funext a; dsimp [r]; ring
  rw [hmr] at ha
  have hb := sum_negMulLog_le_mass univ r (fun a _ => hr a)
  simp only [card_univ] at hb
  change natEntropy r ≤ Real.negMulLog (∑ a,r a)+(∑ a,r a)*Real.log (Fintype.card α) at hb
  have ht : (∑ a,m a)+(∑ a,r a)=1 := by
    rw [←sum_add_distrib]
    simpa only [hmr] using hqs
  have hbin := entropy_le_log_card (p:=fun b : Bool => if b then ∑ a,m a else ∑ a,r a)
    (by intro b; cases b; exact sum_nonneg (fun a _=>hr a); exact sum_nonneg (fun a _=>hm a))
    (by simpa only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte] using ht)
  simp only [natEntropy,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,Fintype.card_bool,Nat.cast_ofNat] at hbin
  have hδ : (∑ a,r a)=((1/2:ℝ)*∑ a,|p a-q a|) := by
    have hpoint (a : α) : |p a-q a| = p a+q a-2*m a := by
      dsimp [m]
      rcases le_total (p a) (q a) with h|h
      · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    simp_rw [hpoint]
    simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,hps,hqs]
    simp only [r,sum_sub_distrib,hqs]
    ring
  rw [hδ] at hb
  rw [hδ] at hbin
  linarith
end SmoothObstruction.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Models
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped ENNReal Topology Manifold ContDiff

namespace SmoothObstruction.ConullTransport
open MeasureTheory Set
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma invariant_iterates (T : X → X) (A : Set X) (hA : T ⁻¹' A=A) :
    ∀ n, ∀ x∈A,(T^[n]) x∈A := by
  intro n x hx
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact show (T^[n]) x∈T ⁻¹' A from by rw [hA]; exact ih

end SmoothObstruction.ConullTransport

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PairLaw
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Classical
open Finset

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset
open scoped ENNReal
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

lemma second_marginal (μ : Measure X) [IsFiniteMeasure μ] (P : X → α) (hP : Measurable P) :
    (law μ P).map Prod.snd=μ := by
  rw [law,←Measure.mapₗ_apply_of_measurable measurable_snd,map_sum]
  simp only [Measure.mapₗ_apply_of_measurable measurable_snd,
    Measure.map_smul,
    Measure.map_snd_prod,smul_smul,normalized_cell]
  exact sum_cells μ P hP

end SmoothObstruction.PairLaw

end

section

namespace SmoothObstruction
open MeasureTheory Filter Topology Set
open scoped ENNReal
attribute [instance] SwitchData.fin SwitchData.meas SwitchData.singletons
end SmoothObstruction

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PhaseDynamics
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter Topology

namespace SmoothObstruction.PhaseDynamics

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
lemma iterate_phase {m : ℕ} (T : X → X) (a : X → ZMod m)
    (ha : ∀ x, a (T x) = a x + 1) (x : X) (n : ℕ) :
    a ((T^[n]) x) = a x + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ha, ih, Nat.cast_add, Nat.cast_one, add_assoc]

end SmoothObstruction.PhaseDynamics

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordParameters
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty _root_.OAI.SmoothObstruction.WordHierarchy.lengthNeZero _root_.OAI.SmoothObstruction.WordHierarchy.recognitionLengthNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology

namespace SmoothObstruction.WordParameters

lemma length_eq_pow (s₀ i : ℕ) :
    length s₀ i = 2 ^ (∑ j ∈ Finset.range i, K (sequence s₀ j)) := by
  induction i with
  | zero => simp [length]
  | succ i ih => rw [length, ih, Finset.sum_range_succ, pow_add]

lemma rate_pos {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) : 0 < rate s₀ i := by
  have hk := (sequence_growth h₀ i).1
  have hkr : (256 : ℝ) ≤ K (sequence s₀ i) := by exact_mod_cast hk
  apply div_pos _ (by exact_mod_cast length_pos s₀ i)
  have hb := (K_bounds (sequence s₀ i)).1
  nlinarith

lemma rate_step {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    epsilon i / 200 * rate s₀ i ≤ rate s₀ (i + 1) := by
  obtain ⟨hk, he⟩ := step_conditions h₀ i
  have hx := (one_step_growth hk he).1
  have hr := (rounding hx).2.2
  unfold rate
  rw [sequence, length, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  apply (le_div_iff₀ (mul_pos (by exact_mod_cast length_pos s₀ i) (by positivity))).mpr
  have hm : (length s₀ i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast length_pos s₀ i)
  calc
    _ = X i (sequence s₀ i) / 2 := by unfold X; field_simp; ring
    _ ≤ _ := hr

lemma rate_step_dyadic {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    rate s₀ i / (2 : ℝ) ^ (i + 11) ≤ rate s₀ (i + 1) := by
  have hp : 0 < rate s₀ i := rate_pos h₀ i
  calc
    _ ≤ epsilon i / 200 * rate s₀ i := by
      unfold epsilon
      rw [show i + 11 = (i + 3) + 8 by omega, pow_add]
      norm_num
      field_simp
      nlinarith
    _ ≤ _ := rate_step h₀ i

/-- The exact dyadic rate lower bound, with the finite arithmetic sum left
unrounded (its value is i(i+21)/2). Level zero is source level one. -/
theorem rate_lower {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    rate s₀ 0 / (2 : ℝ) ^ (∑ j ∈ Finset.range i, (j + 11)) ≤ rate s₀ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, pow_add, ← div_div]
    exact (div_le_div_of_nonneg_right ih (by positivity)).trans (rate_step_dyadic h₀ i)

lemma exponent_sum (i : ℕ) :
    (2 : ℕ) * (∑ j ∈ Finset.range i, (j + 11)) = i * (i + 21) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Finset.sum_range_succ]; nlinarith

lemma K_double_exponential {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    2 ^ (8 * 2 ^ i) ≤ K (sequence s₀ i) := by
  induction i with
  | zero => simpa [sequence] using h₀
  | succ i ih =>
    obtain ⟨hk, he⟩ := step_conditions h₀ i
    have hs := (one_step_growth hk he).2.2.2.1
    change _ ≤ K (nextS i (sequence s₀ i))
    calc
      _ = (2 ^ (8 * 2 ^ i)) ^ 2 := by rw [← pow_mul, pow_succ]; congr 1; omega
      _ ≤ K (sequence s₀ i) ^ 2 := Nat.pow_le_pow_left ih 2
      _ ≤ _ := hs

lemma double_exp_budget (i : ℕ) (hi : 16 ≤ i) :
    16 * (∑ j ∈ Finset.range i, (j + 11)) ≤ 8 * 2 ^ i := by
  have hpoly : i * (i + 21) ≤ 2 ^ i := by
    induction i, hi using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ]
      have hmul : (n + 1) * (n + 1 + 21) ≤ 2 * (n * (n + 21)) := by nlinarith
      nlinarith
  have hs := exponent_sum i
  nlinarith

/-- Source divergence: the available-scale information cannot be summable.
The proof gives an explicit positive lower bound after level16, not merely
an informal comparison of logarithmic growth rates. -/
theorem rates_not_summable {s₀ : ℕ} (h₀ : 256 ≤ K s₀) :
    ¬ Summable (fun i => (K (sequence s₀ i) : ℝ) * rate s₀ i ^ 16) := by
  have hlower (i : ℕ) (hi : 16 ≤ i) : rate s₀ 0 ^ 16 ≤
      (K (sequence s₀ i) : ℝ) * rate s₀ i ^ 16 := by
    let t := ∑ j ∈ Finset.range i, (j + 11)
    have hg : (2 : ℝ) ^ (16 * t) ≤ K (sequence s₀ i) := by
      have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) (double_exp_budget i hi)
      exact_mod_cast h1.trans (K_double_exponential h₀ i)
    have hr := pow_le_pow_left₀ (div_nonneg (rate_pos h₀ 0).le (by positivity) :
        0 ≤ rate s₀ 0 / (2 : ℝ) ^ t)
      (rate_lower h₀ i) 16
    have hp : 0 < (2 : ℝ) ^ t := by positivity
    have heq : rate s₀ 0 ^ 16 = (2 : ℝ) ^ (16 * t) *
        (rate s₀ 0 / (2 : ℝ) ^ t) ^ 16 := by
      rw [div_pow, ← pow_mul]
      rw [Nat.mul_comm t 16]
      field_simp
    rw [heq]
    exact mul_le_mul hg hr (by positivity) (by positivity)
  intro hs
  have hlim := hs.tendsto_atTop_zero
  have hle : rate s₀ 0 ^ 16 ≤ 0 := ge_of_tendsto hlim (eventually_atTop.2 ⟨16, hlower⟩)
  exact (not_le_of_gt (pow_pos (rate_pos h₀ 0) 16)) hle

end SmoothObstruction.WordParameters

end

section

open Filter Topology

namespace SmoothObstruction.CheapScales
open Filter Finset

/-- A summable nonnegative expense cannot dominate a nonsummable information
budget on pairwise disjoint finite test sets. -/
theorem arbitrarily_late_cheap {J : ℕ → Finset ℕ}
    (hJ : ∀ i i', i ≠ i' → Disjoint (J i) (J i'))
    {B R : ℕ → ℝ} (hR : ∀ i,0≤R i)
    (hBs : Summable (fun j => (B j)^16))
    (hRs : ¬Summable (fun i => (J i).card*(R i)^16))
    {ε : ℝ} (hε : 0<ε) (N : ℕ) :
    ∃ i≥N, ∃ j∈J i,B j<ε*R i := by
  classical
  let idx : (Σ i,{j // j∈J i}) → ℕ := fun p => p.2.val
  have hinj : Function.Injective idx := by
    intro ⟨i,j,hj⟩ ⟨i',j',hj'⟩ h
    change j=j' at h
    subst j'
    have hi : i=i' := by
      by_contra hn
      exact (Finset.disjoint_left.mp (hJ i i' hn) hj hj')
    subst i'
    rfl
  have hsum := (hBs.comp_injective hinj).sigma
  have hsum' : Summable (fun i => ∑ j∈J i,(B j)^16) := by
    apply hsum.congr
    intro i
    change (∑' j : {j // j∈J i}, (B j.val)^16)=_
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun j => (B j)^16) (J i)
  by_contra hc
  push Not at hc
  have hbound (i : ℕ) : (ε^16)*((J (i+N)).card*(R (i+N))^16) ≤
      ∑ j∈J (i+N),(B j)^16 := by
    calc
      _ = ∑ j∈J (i+N),(ε*R (i+N))^16 := by simp [mul_pow]; ring
      _ ≤ _ := Finset.sum_le_sum (fun j hj =>
        pow_le_pow_left₀ (mul_nonneg hε.le (hR _)) (hc (i+N) (by omega) j hj) 16)
  have hs := ((summable_nat_add_iff N).mpr hsum').of_nonneg_of_le
    (fun i => mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (by positivity))) hbound
  have ht := hs.mul_left (ε^16)⁻¹
  have ht' : Summable (fun i => (J (i+N)).card*(R (i+N))^16) := by
    simpa only [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hε.ne'),one_mul] using ht
  exact hRs ((summable_nat_add_iff N).mp ht')

/-- Successively late tests with ratios tending to zero; positivity is retained
for the source information rate, so the ratio is not a totalized-division trick. -/
theorem cheap_sequence {J : ℕ → Finset ℕ}
    (hJ : ∀ i i', i ≠ i' → Disjoint (J i) (J i'))
    {B R : ℕ → ℝ} (hB : ∀ j,0≤B j) (hR : ∀ i,0<R i)
    (hBs : Summable (fun j => (B j)^16))
    (hRs : ¬Summable (fun i => (J i).card*(R i)^16)) :
    ∃ (i j : ℕ → ℕ), (∀ a : ℕ, a ≤ i a) ∧ (∀ a : ℕ, j a ∈ J (i a)) ∧
      Tendsto i atTop atTop ∧ Tendsto (fun a => B (j a)/R (i a)) atTop (nhds 0) := by
  have hex (a : ℕ) := arbitrarily_late_cheap hJ (fun i => (hR i).le) hBs hRs
    (show 0<(1:ℝ)/(a+1) by positivity) a
  choose i hi j hj hcheap using hex
  refine ⟨i,j,hi,hj,tendsto_atTop_mono hi tendsto_id,?_⟩
  apply squeeze_zero (fun a => div_nonneg (hB _) (hR _).le)
      (fun a => (div_le_iff₀ (hR _)).mpr (hcheap a).le)
  simpa only [Nat.cast_add,Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun a : ℕ => (1:ℝ)/(a+1)) atTop (nhds 0))

end SmoothObstruction.CheapScales

namespace SmoothObstruction.WordParameters
open Filter Finset

lemma logLevel_succ (s₀ i : ℕ) :
    logLevel s₀ (i+1)=logLevel s₀ i+K (sequence s₀ i) := by
  simp only [logLevel,Finset.sum_range_succ]

lemma logLevel_strictMono {s₀ : ℕ} (h₀ : 256≤K s₀) : StrictMono (logLevel s₀) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [logLevel_succ]
  have := (step_conditions h₀ i).1
  omega

lemma testScales_disjoint {s₀ : ℕ} (h₀ : 256≤K s₀) :
    ∀ i i', i≠i' → Disjoint (testScales s₀ i) (testScales s₀ i') := by
  have hd (i i' : ℕ) (hi : i< i') : Disjoint (testScales s₀ i) (testScales s₀ i') := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [testScales,Finset.mem_Icc] at hj hj'
    have hm := (logLevel_strictMono h₀).monotone (show i+1≤ i' by omega)
    rw [logLevel_succ] at hm
    have hk := (step_conditions h₀ i).1
    omega
  intro i i' hi
  rcases lt_or_gt_of_ne hi with h|h
  · exact hd i i' h
  · exact (hd i' i h).symm

lemma testScales_card {s₀ : ℕ} (h₀ : 256≤K s₀) (i : ℕ) :
    K (sequence s₀ i) ≤ 32*(testScales s₀ i).card := by
  rw [testScales,Nat.card_Icc]
  have hk := (step_conditions h₀ i).1
  omega

lemma testScales_not_summable {s₀ : ℕ} (h₀ : 256≤K s₀) :
    ¬ Summable (fun i => (testScales s₀ i).card*(rate s₀ i)^16) := by
  intro hs
  apply rates_not_summable h₀
  apply (hs.mul_left 32).of_nonneg_of_le
  · intro i; positivity
  · intro i
    have hh : (K (sequence s₀ i) : ℝ)≤32*(testScales s₀ i).card := by
      exact_mod_cast testScales_card h₀ i
    nlinarith [mul_le_mul_of_nonneg_right hh (show 0≤(rate s₀ i)^16 by positivity)]

/-- The source's actual disjoint tests, with their full stated range and
no enlargement or alteration of the word recursion. -/
theorem actual_cheap_scales {s₀ : ℕ} (h₀ : 256≤K s₀)
    {B : ℕ → ℝ} (hB : ∀ j,0<B j) (hBs : Summable (fun j => (B j)^16)) :
    ∃ (i j : ℕ → ℕ), (∀ a : ℕ,a≤ i a) ∧ (∀ a,j a∈testScales s₀ (i a)) ∧
      Tendsto i atTop atTop ∧
      Tendsto (fun a => B (j a)/rate s₀ (i a)) atTop (nhds 0) ∧
      ∀ a, ∃ t : ℕ, (K (sequence s₀ (i a))+15)/16≤t ∧
        t≤K (sequence s₀ (i a))/8 ∧
        length s₀ (i a)*2^t=2^(j a) ∧ 2≤2^t := by
  obtain ⟨i,j,hi,hj,hit,hcheap⟩ := CheapScales.cheap_sequence (testScales_disjoint h₀)
    (fun j => (hB j).le) (rate_pos h₀) hBs (testScales_not_summable h₀)
  refine ⟨i,j,hi,hj,hit,hcheap,fun a => ?_⟩
  have hh := hj a
  simp only [testScales,Finset.mem_Icc] at hh
  let t := j a-logLevel s₀ (i a)
  have ht : j a=logLevel s₀ (i a)+t := by omega
  have htrange : (K (sequence s₀ (i a))+15)/16≤t ∧ t≤K (sequence s₀ (i a))/8 := by omega
  refine ⟨t,htrange.1,htrange.2,?_,?_⟩
  · rw [length_eq_pow,←pow_add,ht]
    rfl
  · have hk := (step_conditions h₀ (i a)).1
    have hp : 1≤t := by omega
    exact (by decide : 2≤2^1).trans (Nat.pow_le_pow_right (by decide) hp)

end SmoothObstruction.WordParameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordStep
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty _root_.OAI.SmoothObstruction.WordHierarchy.recognitionNNeZero _root_.OAI.SmoothObstruction.WordHierarchy.stageLengthNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A B : Type*} [Fintype A] [Fintype B]

lemma expect_transport (e : A ≃ B) (P : Law A) (f : B → ℝ) :
    expect (transport e P) f = expect P (f ∘ e) := by
  unfold expect transport
  exact Fintype.sum_equiv e.symm _ _ (fun b => by simp)
end SmoothObstruction.FiniteLaw

end

section

namespace SmoothObstruction.WordStep
open WordParameters WordAlphabet FiniteLaw WordLaw
open scoped BigOperators

lemma D_le_N (s : ℕ) : D s ≤ N s :=
  Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
end SmoothObstruction.WordStep

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordHierarchy
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty _root_.OAI.SmoothObstruction.WordHierarchy.levelNonempty _root_.OAI.SmoothObstruction.WordHierarchy.recognitionLengthNeZero _root_.OAI.SmoothObstruction.WordHierarchy.recognitionNNeZero _root_.OAI.SmoothObstruction.WordHierarchy.stageLengthNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.WordHierarchy
open WordParameters WordAlphabet WordStep FiniteLaw WordLaw
open scoped BigOperators

/-- Every stored successor word actually obeys the W4 event for every
nonwrapping lower-window offset. -/
lemma stage_approximates (i : ℕ) (a : A (i+2)) (t : Offsets (S i)) :
    tvFromUniformObservable (fun b => window (S i) t ((stage i).word b))
      (WordFlatten.flattenEquiv.symm ((stage (i+1)).word a)) ≤ 1/10000 := by
  classical
  have h := (stage (i+1)).supported ((Fintype.equivFin (A (i+2))) a)
  change _ ∈ Finset.univ.filter _ at h
  exact (Finset.mem_filter.mp h).2 t

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordConcatenation
variable {A B : Type*} {m N : ℕ}

lemma pack_val (b : Fin N) (r : Fin m) : (pack (b,r)).val = b.val*m+r.val := by
  change r.val + m*b.val = b.val*m+r.val
  ac_rfl

end SmoothObstruction.WordConcatenation

namespace SmoothObstruction.PhaseDynamics
open MeasureTheory Set Finset
section Window
variable {A : Type*} [TopologicalSpace A] 
  [MeasurableSpace A] [MeasurableSingletonClass A] (m : ℕ → ℕ)
  [∀ i, NeZero (m i)]

omit [MeasurableSpace A] [MeasurableSingletonClass A]  in
omit [∀ i, NeZero (m i)] in
lemma iterate_symbol (x : Space A m) (j : ℕ) (t : ℤ) :
    ((shift A m)^[j] x).1 t = x.1 (t+j) := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',shift_symbol,ih]
    apply congrArg x.1
    push_cast
    omega

omit [MeasurableSpace A] [MeasurableSingletonClass A]  in
omit [∀ i, NeZero (m i)] in
lemma shift_iterate_phase (x : Space A m) (i j : ℕ) :
    ((shift A m)^[j] x).2 i=x.2 i+j :=
  iterate_phase (shift A m) (fun x => x.2 i) (fun _ => rfl) x j

omit [MeasurableSpace A] [MeasurableSingletonClass A]  in
omit [∀ i, NeZero (m i)] in
lemma containingWord_tower (x : Space A m) (i : ℕ) (hc : x.2 i=0)
    (j : ℕ) (hj : j < m i) :
    containingWord m ((shift A m)^[j] x) i=containingWord m x i := by
  have hp : (((shift A m)^[j] x).2 i).val=j := by
    rw [shift_iterate_phase,hc,zero_add,ZMod.val_natCast,Nat.mod_eq_of_lt hj]
  funext r
  simp only [containingWord,wordAt,hp,hc,ZMod.val_zero,Nat.cast_zero,neg_zero,zero_add,iterate_symbol]
  apply congrArg x.1
  omega

/-- Every parent-word event has exactly the same unnormalized mass at each
phase. This is the invariance argument in source (parent-slot-law), before
normalizing either restriction. No uniform-parent assumption occurs. -/
theorem parent_phase_mass (μ : Measure (Space A m))
    (hT : MeasurePreserving (shift A m) μ μ) (i : ℕ) (v : Fin (m i) → A)
    (j : ℕ) (hj : j < m i) :
    μ {x | x.2 i=(j : ZMod (m i)) ∧ containingWord m x i=v} =
      μ {x | x.2 i=0 ∧ containingWord m x i=v} := by
  let E : Set (Space A m) := {x | x.2 i=(j : ZMod (m i)) ∧ containingWord m x i=v}
  have hc : Measurable (fun x : Space A m => x.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hE : MeasurableSet E := (hc (measurableSet_singleton _)).inter
    (measurable_containingWord m i (measurableSet_singleton v))
  have hpre : ((shift A m)^[j]) ⁻¹' E = {x | x.2 i=0 ∧ containingWord m x i=v} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,E,shift_iterate_phase]
    constructor
    · rintro ⟨hp,hv⟩
      have hz : x.2 i=0 := by
        apply add_right_cancel (b := (j : ZMod (m i)))
        simpa only [zero_add] using hp
      exact ⟨hz,(containingWord_tower m x i hz j hj) ▸ hv⟩
    · rintro ⟨hz,hv⟩
      exact ⟨by rw [hz,zero_add],by rwa [containingWord_tower m x i hz j hj]⟩
  rw [←(hT.iterate j).measure_preimage hE.nullMeasurableSet,hpre]

lemma parent_phase_mass_zmod (μ : Measure (Space A m))
    (hT : MeasurePreserving (shift A m) μ μ) (i : ℕ) (v : Fin (m i) → A)
    (j : ZMod (m i)) :
    μ {x | x.2 i=j ∧ containingWord m x i=v} =
      μ {x | x.2 i=0 ∧ containingWord m x i=v} := by
  simpa only [ZMod.natCast_zmod_val] using parent_phase_mass m μ hT i v j.val (ZMod.val_lt j)

omit [TopologicalSpace A] [MeasurableSingletonClass A] in
lemma sum_phase_parent (μ : Measure (Space A m)) [IsFiniteMeasure μ]
    (i : ℕ) (v : Fin (m i) → A) :
    (∑ j : ZMod (m i), μ.real {x | x.2 i=j ∧ containingWord m x i=v}) =
      μ.real {x | containingWord m x i=v} := by
  let E : Set (Space A m) := {x | containingWord m x i=v}
  have hc : Measurable (fun x : Space A m => x.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hs := sum_measureReal_preimage_singleton (μ:=μ.restrict E) univ
    (fun j _ => (measurableSet_singleton j).preimage hc)
  have hterm (j : ZMod (m i)) : (μ.restrict E).real ((fun x : Space A m => x.2 i) ⁻¹' {j}) =
      μ.real {x | x.2 i=j ∧ containingWord m x i=v} := by
    rw [measureReal_restrict_apply (hc (measurableSet_singleton j))]
    rfl
  change (∑ j, (μ.restrict E).real ((fun x : Space A m => x.2 i) ⁻¹' {j})) =
    (μ.restrict E).real ((fun x : Space A m => x.2 i) ⁻¹' (↑(univ : Finset (ZMod (m i))))) at hs
  simp only [hterm,coe_univ,Set.preimage_univ,measureReal_restrict_apply_univ] at hs
  exact hs

/-- Parent and containing slot are independent under the full stationary
law, although the parent distribution can be wholly nonuniform. -/
theorem parent_slot_independent (μ : Measure (Space A m)) [IsFiniteMeasure μ]
    (hT : MeasurePreserving (shift A m) μ μ) (i : ℕ) (v : Fin (m i) → A)
    (j : ZMod (m i)) :
    (m i : ℝ)*μ.real {x | x.2 i=j ∧ containingWord m x i=v} =
      μ.real {x | containingWord m x i=v} := by
  have hs := sum_phase_parent m μ i v
  have ht (u : ZMod (m i)) : μ.real {x | x.2 i=u ∧ containingWord m x i=v} =
      μ.real {x | x.2 i=j ∧ containingWord m x i=v} := by
    simp only [Measure.real,parent_phase_mass_zmod m μ hT i v]
  simp_rw [ht] at hs
  simpa only [sum_const,card_univ,ZMod.card,nsmul_eq_mul] using hs
end Window
end SmoothObstruction.PhaseDynamics

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set

lemma label_eq_iff (i : ℕ) (x : Extension) (a : A i) :
    label i x=a ↔ PhaseDynamics.containingWord (length 40000) x.val i=word i a := by
  rw [←word_label, (word_injective i).eq_iff]

lemma stationary_ambient (μ : Measure Extension) (hT : MeasurePreserving T μ μ) :
    MeasurePreserving (PhaseDynamics.shift (A 0) (length 40000))
      (μ.map Subtype.val) (μ.map Subtype.val) := by
  have hm : Measurable (PhaseDynamics.shift (A 0) (length 40000)) := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr (fun t => (measurable_pi_apply (t+1)).comp measurable_fst)
    · exact measurable_pi_iff.mpr (fun i => (measurable_of_countable (fun a : ZMod (length 40000 i) => a+1)).comp
        ((measurable_pi_apply i).comp measurable_snd))
  refine ⟨hm,?_⟩
  rw [Measure.map_map hm measurable_subtype_coe]
  have he : (PhaseDynamics.shift (A 0) (length 40000)) ∘ (Subtype.val : Extension → _) =
      (Subtype.val : Extension → _) ∘ T := rfl
  rw [he,←Measure.map_map measurable_subtype_coe hT.measurable,hT.map_eq]

/-- Actual selected parent labels are independent of the fine phase under
EVERY invariant finite measure on the extension. The parent law is arbitrary. -/
theorem label_phase_independent (μ : Measure Extension) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (a : A i) (j : ZMod (length 40000 i)) :
    (length 40000 i : ℝ)*μ.real {x | x.val.2 i=j ∧ label i x=a} =
      μ.real {x | label i x=a} := by
  have hh := PhaseDynamics.parent_slot_independent (length 40000) (μ.map Subtype.val)
    (stationary_ambient μ hT) i (word i a) j
  have hp : Measurable (fun x : PhaseDynamics.Space (A 0) (length 40000) => x.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hw := PhaseDynamics.measurable_containingWord (A := A 0) (length 40000) i
  have hE : MeasurableSet {x : PhaseDynamics.Space (A 0) (length 40000) |
      x.2 i=j ∧ PhaseDynamics.containingWord (length 40000) x i=word i a} := by
    exact (measurableSet_eq_fun hp measurable_const).inter (measurableSet_eq_fun hw measurable_const)
  have hF : MeasurableSet {x : PhaseDynamics.Space (A 0) (length 40000) |
      PhaseDynamics.containingWord (length 40000) x i=word i a} := by
    exact measurableSet_eq_fun hw measurable_const
  simp only [Measure.real] at hh ⊢
  rw [Measure.map_apply (μ := μ) measurable_subtype_coe hE,
    Measure.map_apply (μ := μ) measurable_subtype_coe hF] at hh
  simpa only [Set.preimage_ofPred_eq,←label_eq_iff] using hh

/-- Compatibility determines the child offset by the parent residue. -/
lemma phase_mod (i : ℕ) (x : Extension) :
    (x.val.2 (i+1)).val % length 40000 i=(x.val.2 i).val := by
  have hc := (x.property i).1
  change ZMod.castHom (length_dvd 40000 i) (ZMod (length 40000 i)) (x.val.2 (i+1))=x.val.2 i at hc
  have hh := congrArg (fun a : ZMod (length 40000 i) => a.val) hc
  rw [←ZMod.natCast_zmod_val (x.val.2 (i+1)),map_natCast,ZMod.val_natCast] at hh
  exact hh


lemma phase_decompose (i : ℕ) (x : Extension) :
    (x.val.2 (i+1)).val=(slot i x).val*length 40000 i+(x.val.2 i).val := by
  rw [←phase_mod i x]
  exact (Nat.div_add_mod' _ _).symm

/-- The observed child label is exactly the selected concatenation entry
indexed by the actual parent phase, with no exceptional configurations. -/
theorem label_child (i : ℕ) (x : Extension) :
    label i x=children i (label (i+1) x) (slot i x) := by
  apply word_injective i
  funext j
  have hh := congrFun (word_label (i+1) x) (pack (slot i x,j))
  change concat (word i) (children i (label (i+1) x)) (pack (slot i x,j)) = _ at hh
  rw [concat_pack] at hh
  rw [hh,congrFun (word_label i x) j]
  simp only [PhaseDynamics.containingWord,PhaseDynamics.wordAt]
  apply congrArg x.val.1
  change -((x.val.2 i).val : ℤ)+(j.val:ℤ) =
    -((x.val.2 (i+1)).val : ℤ)+((j.val+length 40000 i*(slot i x).val : ℕ):ℤ)
  have hp : ((x.val.2 (i+1)).val : ℤ)=(slot i x).val*(length 40000 i : ℤ)+(x.val.2 i).val := by
    exact_mod_cast phase_decompose i x
  push_cast
  rw [hp]
  ring

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.Alignment
open MeasureTheory Set Finset
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype Y] [MeasurableSingletonClass Y]

section Cyclic
variable {m : ℕ} [NeZero m]
variable (T : X → X) (a : X → ZMod m)

omit [MeasurableSpace X] in
lemma align_phase (ha : ∀ x,a (T x)=a x+1) (x : X) : a (align T a x)=0 := by
  rw [align,iterate_phase T a ha,ZMod.natCast_zmod_val,add_neg_cancel]

end Cyclic
end SmoothObstruction.Alignment

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep MeasureTheory Set
open scoped ENNReal

lemma iterate_coe (j : ℕ) (x : Extension) :
    ((T^[j]) x).val=(PhaseDynamics.shift (A 0) (length 40000))^[j] x.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    change PhaseDynamics.shift (A 0) (length 40000) (((T^[j]) x).val) = _
    exact congrArg (PhaseDynamics.shift (A 0) (length 40000)) ih

lemma phase_iterate (i j : ℕ) (x : Extension) : phase i ((T^[j]) x)=phase i x+j := by
  change (((T^[j]) x).val).2 i = _
  rw [iterate_coe,PhaseDynamics.shift_iterate_phase]

/-- Literal forward-to-first-boundary law; µ_i is the source's factor-m_i
normalized restriction, not a newly chosen distribution. -/
theorem advance_map (μ : Measure Extension) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) : μ.map (advance i)=boundary μ i :=
  Alignment.align_map T (phase i) μ hT (measurable_phase i) (fun _ => rfl)

lemma phase_mod_two (i : ℕ) (x : Extension) :
    (phase (i+2) x).val % length 40000 i=(phase i x).val := by
  rw [←phase_mod i x,←phase_mod (i+1) x,Nat.mod_mod_of_dvd _ (length_dvd 40000 i)]

lemma measurable_parentSlot (i : ℕ) : Measurable (parentSlot i) := by
  have hh : parentSlot i = (fun a : ZMod (length 40000 (i+2)) =>
      (⟨a.val / length 40000 i,by
        apply (Nat.div_lt_iff_lt_mul (length_pos 40000 i)).mpr
        simpa only [length_two,Nat.mul_comm] using ZMod.val_lt a⟩ : Fin (N (S i)*N (S (i+1))))) ∘ phase (i+2) := rfl
  rw [hh]
  exact (measurable_of_countable _).comp (measurable_phase (i+2))

lemma parentSlot_decompose (i : ℕ) (x : Extension) :
    (phase (i+2) x).val=(parentSlot i x).val*length 40000 i+(phase i x).val := by
  rw [←phase_mod_two i x]
  exact (Nat.div_add_mod' _ _).symm

lemma parentSlot_site_lt (i : ℕ) (j : Fin (N (S i)*N (S (i+1)))) :
    j.val*length 40000 i < length 40000 (i+2) := by
  rw [length_two,Nat.mul_comm (length 40000 i)]
  exact Nat.mul_lt_mul_of_pos_right j.isLt (length_pos 40000 i)

lemma parentSlot_site (i : ℕ) (x : Extension) (j : Fin (N (S i)*N (S (i+1)))) :
    parentSlot i x=j ∧ phase i x=0 ↔
      phase (i+2) x=(j.val*length 40000 i : ℕ) := by
  constructor
  · rintro ⟨hj,hp⟩
    apply ZMod.val_injective
    rw [parentSlot_decompose,hj,hp,ZMod.val_zero,Nat.add_zero,ZMod.val_natCast,
      Nat.mod_eq_of_lt (parentSlot_site_lt i j)]
  · intro hp
    have hv : (phase (i+2) x).val=j.val*length 40000 i := by
      rw [hp,ZMod.val_natCast,Nat.mod_eq_of_lt (parentSlot_site_lt i j)]
    refine ⟨?_,?_⟩
    · apply Fin.ext
      change (phase (i+2) x).val / length 40000 i=j.val
      rw [hv,Nat.mul_div_left _ (length_pos 40000 i)]
    · apply ZMod.val_injective
      rw [ZMod.val_zero,←phase_mod_two i x,hv,Nat.mul_mod_left]

/-- Every genuine parent slot has the same mass with a fixed parent label.
The right-hand side is the arbitrary stationary parent law, not uniform. -/
theorem boundary_parentSlot_mass (μ : Measure Extension) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (v : A (i+2))
    (j : Fin (N (S i)*N (S (i+1)))) :
    (N (S i)*N (S (i+1)) : ℕ)*(boundary μ i).real {x | parentSlot i x=j ∧ label (i+2) x=v} =
      μ.real {x | label (i+2) x=v} := by
  have hE : MeasurableSet {x | parentSlot i x=j ∧ label (i+2) x=v} :=
    (measurableSet_eq_fun (measurable_parentSlot i) measurable_const).inter
      (measurableSet_eq_fun (measurable_label (i+2)) measurable_const)
  change (N (S i)*N (S (i+1)) : ℕ)*
    (Alignment.boundaryMeasure (phase i) μ).real _ = _
  rw [Alignment.boundary_real (phase i) μ _ hE]
  have he : {x | parentSlot i x=j ∧ label (i+2) x=v} ∩ {x | phase i x=0} =
      {x | phase (i+2) x=(j.val*length 40000 i : ℕ) ∧ label (i+2) x=v} := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq]
    simpa only [and_assoc,and_left_comm,and_comm] using
      and_congr_left (fun _ : label (i+2) x=v => parentSlot_site i x j)
  rw [he]
  have hh := label_phase_independent μ hT (i+2) v (j.val*length 40000 i : ℕ)
  rw [show (length 40000 (i+2):ℝ)=(length 40000 i:ℝ)*(N (S i)*N (S (i+1)):ℕ) by
    exact_mod_cast length_two i] at hh
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set

lemma phase_val_nonwrap (i j : ℕ) (x : Extension)
    (hj : (phase i x).val+j < length 40000 i) :
    (phase i ((T^[j]) x)).val=(phase i x).val+j := by
  rw [phase_iterate,←ZMod.natCast_zmod_val (phase i x),←Nat.cast_add,
    ZMod.val_natCast,Nat.mod_eq_of_lt hj,ZMod.natCast_zmod_val]

lemma label_nonwrap (i j : ℕ) (x : Extension)
    (hj : (phase i x).val+j < length 40000 i) :
    label i ((T^[j]) x)=label i x := by
  apply word_injective i
  rw [word_label,word_label]
  funext r
  change (((T^[j]) x).val).1 (-(phase i ((T^[j]) x)).val+(r.val:ℤ)) =
    x.val.1 (-(phase i x).val+(r.val:ℤ))
  rw [phase_val_nonwrap i j x hj,iterate_coe,PhaseDynamics.iterate_symbol]
  apply congrArg x.val.1
  push_cast
  ring

lemma slot_pair (i : ℕ) (x : Extension) :
    (parentSlot i x).val=(slot (i+1) x).val*N (S i)+(slot i x).val := by
  have h := parentSlot_decompose i x
  rw [phase_decompose (i+1) x,phase_decompose i x,length_step i] at h
  have he : ((parentSlot i x).val)*length 40000 i =
      ((slot (i+1) x).val*N (S i)+(slot i x).val)*length 40000 i := by
    nlinarith
  exact Nat.eq_of_mul_eq_mul_right (length_pos 40000 i) he

/-- Inside a parent, advancement by a child-word length advances its actual
slot by one. Alignment is the genuine phase-zero event. -/
lemma label_advance_child (i r : ℕ) (x : Extension) (hx : phase i x=0)
    (hr : (slot i x).val+r < N (S i)) :
    label i ((T^[r*length 40000 i]) x) =
      children i (label (i+1) x) ⟨(slot i x).val+r,hr⟩ := by
  have hp : (phase (i+1) x).val=(slot i x).val*length 40000 i := by
    change x.val.2 i=0 at hx
    rw [phase_decompose i x,hx,ZMod.val_zero,Nat.add_zero]
  have hj : (phase (i+1) x).val+r*length 40000 i < length 40000 (i+1) := by
    rw [hp,←Nat.add_mul,length_step,Nat.mul_comm (length 40000 i)]
    exact Nat.mul_lt_mul_of_pos_right hr (length_pos 40000 i)
  rw [label_child,label_nonwrap (i+1) _ x hj]
  apply congrArg (children i (label (i+1) x))
  apply Fin.ext
  change (phase (i+1) ((T^[r*length 40000 i]) x)).val / length 40000 i = _
  rw [phase_val_nonwrap (i+1) _ x hj,hp,←Nat.add_mul,
    Nat.mul_div_left _ (length_pos 40000 i)]

/-- Uniform finite-window sampling is an exact identification of the actual
symbolic orbit, not a replacement process. No wrap occurs at admissible slots. -/
theorem labelList_inside (i r : ℕ) (x : Extension) (hx : phase i x=0)
    (hr : (slot i x).val+r ≤ N (S i)) :
    labelList i r x = fun j : Fin r =>
      children i (children (i+1) (label (i+2) x) (slot (i+1) x))
        ⟨(slot i x).val+j.val,by have := j.isLt; omega⟩ := by
  funext j
  rw [labelList,label_advance_child i j.val x hx (by have := j.isLt; omega),
    label_child (i+1) x]
end SmoothObstruction.WordHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordEntropy
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty _root_.OAI.SmoothObstruction.WordHierarchy.recognitionLengthNeZero _root_.OAI.SmoothObstruction.WordHierarchy.recognitionNNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.WordFlatten
open Finset FiniteLaw WordLaw SequentialLaw
variable {A : Type*} [Fintype A] [DecidableEq A] {q H : ℕ}

omit [Fintype A] in
lemma test_flatten (m : Fin (q*H) → Option A) (w : Fin q → Fin H → A) :
    test m (flattenEquiv w) = ∏ b, test (fun r => m (finProdFinEquiv (b,r))) (w b) := by
  unfold test
  calc
    _ = ∏ br : Fin q × Fin H, mark (m (finProdFinEquiv br)) (w br.1 br.2) := by
      simpa only [flattenEquiv, Equiv.coe_fn_mk,Equiv.symm_apply_apply] using
        (finProdFinEquiv.prod_comp (fun j => mark (m j) (flattenEquiv w j))).symm
    _ = _ := Fintype.prod_prod_type _

omit [Fintype A] [DecidableEq A] in
lemma count_grouped (m : Fin (q*H) → Option A) :
    (∑ b : Fin q, (univ.filter (fun r : Fin H => (m (finProdFinEquiv (b,r))).isSome)).card) =
      (univ.filter (fun r => (m r).isSome)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  calc
    _ = ∑ br : Fin q × Fin H, if (m (finProdFinEquiv br)).isSome then 1 else 0 :=
      (Fintype.sum_prod_type (fun br : Fin q × Fin H =>
        if (m (finProdFinEquiv br)).isSome then (1:ℕ) else 0)).symm
    _ = _ := finProdFinEquiv.sum_comp (fun r => if (m r).isSome then 1 else 0)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Fintype V] [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) {K : ℕ}

omit [FiniteDimensional (ZMod 2) V] in
/-- W3 itself: the actual single conditioned law controls every arbitrary
partial list, with a single factor two, including lists crossing groups. -/
theorem flat_sublist (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E)
    (m : Fin (q*H) → Option {v : V // v ≠ 0}) :
    expect (flatLaw B hd E hE) (test m) ≤
      2 * ((2 : ℝ)^(2*K) / Fintype.card {v : V // v ≠ 0}) ^
        (univ.filter (fun r => (m r).isSome)).card := by
  unfold flatLaw
  rw [expect_transport]
  have ht : ((test m) ∘ flattenEquiv) =
      (fun w => ∏ b, test (fun r => m (finProdFinEquiv (b,r))) (w b)) := by
    funext w
    exact test_flatten m w
  rw [ht]
  have hh := conditioned_sublist B hd hK E hE (fun b r => m (finProdFinEquiv (b,r)))
  simpa only [count_grouped] using hh
end SmoothObstruction.WordFlatten

namespace SmoothObstruction.FiniteLaw
open Finset FiniteEntropy
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma TV_symm (P Q : Law α) : TV P Q=TV Q P := by simp only [TV,abs_sub_comm]
lemma TV_triangle (P Q R : Law α) : TV P R ≤ TV P Q+TV Q R := by
  unfold TV
  rw [←mul_add,←sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (sum_le_sum (fun a _ => abs_sub_le (P.mass a) (Q.mass a) (R.mass a))) (by norm_num)

lemma push_sub [DecidableEq β] (P Q : Law α) (f : α → β) (b : β) :
    (push P f).mass b-(push Q f).mass b = ∑ a,if f a=b then P.mass a-Q.mass a else 0 := by
  classical
  simp only [push,←sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  split_ifs <;> ring

lemma TV_push [DecidableEq β] (P Q : Law α) (f : α → β) : TV (push P f) (push Q f) ≤ TV P Q := by
  classical
  unfold TV
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simp_rw [push_sub]
  calc
    _ ≤ ∑ b,∑ a,|if f a=b then P.mass a-Q.mass a else 0| := sum_le_sum (fun b _ => abs_sum_le_sum_abs _ _)
    _ = ∑ a,|P.mass a-Q.mass a| := by
      rw [sum_comm]
      simp only [apply_ite abs,abs_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma entropy_nonneg (P : Law α) : 0 ≤ entropy P := FiniteEntropy.entropy_nonneg P.nonneg P.total
lemma entropy_mixture (P : Law α) (Q : α → Law β) :
    ∑ a,P.mass a*entropy (Q a) ≤ entropy (mixture P Q) :=
  FiniteEntropy.entropy_mixture P.mass (fun a => (Q a).mass) P.nonneg P.total (fun a => (Q a).nonneg)

lemma entropy_atom_lower (P : Law α) {M : ℝ} (_hM : 0 < M) (h : ∀ a,P.mass a ≤ M) :
    -Real.log M ≤ entropy P := by
  have hb (a : α) : P.mass a*(-Real.log M) ≤ Real.negMulLog (P.mass a) := by
    rcases (P.nonneg a).eq_or_lt with hz|hp
    · rw [←hz,zero_mul,Real.negMulLog_zero]
    · have hh := Real.log_le_log hp (h a)
      rw [Real.negMulLog_def]
      nlinarith [mul_le_mul_of_nonneg_left hh hp.le]
  have hs := sum_le_sum (fun a (_ha : a ∈ (univ : Finset α)) => hb a)
  simpa only [←sum_mul,P.total,one_mul,entropy,natEntropy] using hs

/-- Exactly the one-bit TV cost used in source equation (tv-entropy),
expressed first in natural units. -/
lemma entropy_tv_lower (P Q : Law α) {s : ℝ} (hs : TV P Q ≤ s) :
    entropy P-Real.log 2-s*Real.log (Fintype.card α) ≤ entropy Q := by
  have hcard : 1 ≤ Fintype.card α := by
    by_contra h
    have he : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    have hh := P.total
    simp only [univ_eq_empty,sum_empty] at hh
    norm_num at hh
  have hc : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg (by exact_mod_cast hcard)
  have hh := FiniteEntropy.entropy_tv Q.nonneg P.nonneg Q.total P.total
  rw [←TV,TV_symm] at hh
  change entropy P ≤ entropy Q+Real.log 2+TV P Q*Real.log (Fintype.card α) at hh
  nlinarith [mul_le_mul_of_nonneg_right hs hc]

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.SequentialLaw
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A] {q N : ℕ}

omit [Fintype A] [DecidableEq A] in
lemma embeddedMarks_at (e : Fin q ↪ Fin N) (v : Fin q → A) (j : Fin q) :
    embeddedMarks e v (e j)=some (v j) := by
  classical
  have h : ∃ k, e k=e j := ⟨j,rfl⟩
  have hc := e.injective h.choose_spec
  simp only [embeddedMarks,dite_eq_left h,hc]

omit [Fintype A] [DecidableEq A] in
lemma embeddedMarks_some (e : Fin q ↪ Fin N) (v : Fin q → A) (i : Fin N) (a : A) :
    embeddedMarks e v i=some a ↔ ∃ j,e j=i ∧ v j=a := by
  classical
  constructor
  · intro h
    unfold embeddedMarks at h
    split_ifs at h with hi
    · exact ⟨hi.choose,hi.choose_spec,Option.some.inj h⟩
  · rintro ⟨j,rfl,rfl⟩
    exact embeddedMarks_at e v j

omit [Fintype A] [DecidableEq A] in
lemma embeddedMarks_count (e : Fin q ↪ Fin N) (v : Fin q → A) :
    (univ.filter (fun i => (embeddedMarks e v i).isSome)).card=q := by
  classical
  have he : univ.filter (fun i => (embeddedMarks e v i).isSome)=univ.map e := by
    ext i
    simp only [mem_filter,mem_univ,true_and,mem_map]
    constructor
    · intro hi
      cases hm : embeddedMarks e v i with
      | none => simp [hm] at hi
      | some a =>
        obtain ⟨j,hj,_⟩ := (embeddedMarks_some e v i a).mp hm
        exact ⟨j,hj⟩
    · rintro ⟨j,rfl⟩
      simp only [embeddedMarks_at,Option.isSome_some]
  rw [he,card_map,card_univ,Fintype.card_fin]

lemma embeddedMarks_test (e : Fin q ↪ Fin N) (v : Fin q → A) (w : Fin N → A) :
    test (embeddedMarks e v) w=if w ∘ e=v then 1 else 0 := by
  classical
  rw [test_eq_indicator]
  congr 1
  apply propext
  constructor
  · intro h
    funext j
    exact h (e j) (v j) (embeddedMarks_at e v j)
  · intro h i a hm
    obtain ⟨j,rfl,hj⟩ := (embeddedMarks_some e v i a).mp hm
    exact (congrFun h j).trans hj
end SmoothObstruction.SequentialLaw

namespace SmoothObstruction.WordFlatten
open Finset FiniteLaw WordLaw SequentialLaw
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Fintype V] [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) {K b H q : ℕ}

omit [FiniteDimensional (ZMod 2) V] in
/-- The pushed law of any distinct coordinate list has the exact W3 atom
bound; the law is the recursively used single conditioned sampler. -/
theorem flat_window_atom (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin b → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H b) E)
    (e : Fin q ↪ Fin (b*H)) (v : Fin q → {v : V // v ≠ 0}) :
    (push (flatLaw B hd E hE) (fun w => w ∘ e)).mass v ≤
      2*((2:ℝ)^(2*K)/Fintype.card {v : V // v ≠ 0})^q := by
  have hh := flat_sublist B hd hK E hE (embeddedMarks e v)
  rw [embeddedMarks_count] at hh
  simp only [FiniteLaw.expect,embeddedMarks_test] at hh
  simpa only [push,FiniteLaw.expect,mul_ite,mul_one,mul_zero] using hh
end SmoothObstruction.WordFlatten

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

lemma mass_ext (P Q : Law A) (h : P.mass=Q.mass) : P=Q := by
  cases P; cases Q; cases h; rfl

lemma push_comp [DecidableEq B] [DecidableEq C] (P : Law A) (f : A → B) (g : B → C) :
    push (push P f) g=push P (g ∘ f) := by
  apply mass_ext
  funext c
  simp only [push]
  calc
    _ = ∑ b,∑ a,if g b=c then (if f a=b then P.mass a else 0) else 0 := by
      apply sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      have he (b : B) : (if g b=c then (if f a=b then P.mass a else 0) else 0) =
          if f a=b then (if g b=c then P.mass a else 0) else 0 := by split_ifs <;> rfl
      simp only [he,Finset.sum_ite_eq,mem_univ,ite_true,Function.comp_apply]

lemma push_uniform_mass [Nonempty A] [DecidableEq B] (f : A → B) (b : B) :
    (push uniform f).mass b=(∑ a,if f a=b then (1:ℝ) else 0)/Fintype.card A := by
  simp only [push,uniform,div_eq_mul_inv,sum_mul,ite_mul,one_mul,zero_mul]

lemma uniform_reindex [Nonempty A] [Nonempty B] [DecidableEq C] (e : A ≃ B) (f : B → C) :
    push (uniform (α:=A)) (f ∘ e)=push (uniform (α:=B)) f := by
  apply mass_ext
  funext c
  rw [push_uniform_mass,push_uniform_mass,Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun b => if f b=c then (1:ℝ) else 0)

lemma push_observable {N : ℕ} [DecidableEq C] (P : Law (Fin N → A))
    (f : (Fin N → A) → C) (c : C) :
    (push P f).mass c=WordFamily.observableLaw P f c := by
  simp only [push,WordFamily.observableLaw,expect,mul_ite,mul_one,mul_zero]

lemma TV_empirical {M N : ℕ} [NeZero M] [DecidableEq C]
    (P : Law (Fin N → A)) (f : (Fin N → A) → C) (w : Fin M → Fin N → A) :
    TV (push uniform (f ∘ w)) (push P f)=WordFamily.empiricalTV P f w := by
  simp only [TV,push_uniform_mass,Fintype.card_fin,push_observable,
    WordFamily.empiricalTV,Function.comp_apply]

lemma TV_grouped {q H : ℕ} [NeZero q] [NeZero H] [Nonempty A] [DecidableEq C]
    (f : A → C) (w : Fin q → Fin H → A) :
    TV (push uniform (f ∘ WordFlatten.flattenEquiv w)) (push uniform f) =
      (1/2:ℝ)*∑ c, |(∑ b,(∑ r,if f (w b r)=c then (1:ℝ) else 0)/(H:ℝ))/(q:ℝ)-
        (∑ a,if f a=c then (1:ℝ) else 0)/Fintype.card A| := by
  unfold TV
  congr 1
  apply sum_congr rfl
  intro c _
  rw [push_uniform_mass,push_uniform_mass,Fintype.card_fin]
  congr 2
  have he : (∑ j : Fin (q*H),if (f ∘ WordFlatten.flattenEquiv w) j=c then (1:ℝ) else 0) =
      ∑ b,∑ r,if f (w b r)=c then (1:ℝ) else 0 := by
    rw [← finProdFinEquiv.sum_comp]
    simpa only [Function.comp_apply,WordFlatten.flattenEquiv,Equiv.coe_fn_mk,
      Equiv.symm_apply_apply] using Fintype.sum_prod_type (fun br : Fin q × Fin H =>
      if f (w br.1 br.2)=c then (1:ℝ) else 0)
  rw [he,←sum_div,Nat.cast_mul]
  simp only [div_div]
  rw [mul_comm]

lemma atom_entropy_formula {q K : ℕ} [Nonempty A] (P : Law (Fin q → A))
    (hP : ∀ v,P.mass v ≤ 2*((2:ℝ)^(2*K)/Fintype.card A)^q) :
    (q:ℝ)*(Real.log (Fintype.card A)-(2*K:ℕ)*Real.log 2)-Real.log 2 ≤ entropy P := by
  have hc : (0:ℝ)<Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hM : 0<2*((2:ℝ)^(2*K)/Fintype.card A)^q := by positivity
  have hh := entropy_atom_lower P hM hP
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,
    Real.log_div (by positivity) hc.ne',Real.log_pow] at hh
  convert hh using 1 <;> first | rfl | ring

lemma window_entropy_close {q K : ℕ} [Nonempty A] (P Q : Law (Fin q → A))
    (hP : ∀ v,P.mass v ≤ 2*((2:ℝ)^(2*K)/Fintype.card A)^q)
    {s : ℝ} (hPQ : TV P Q ≤ s) :
    (q:ℝ)*((1-s)*Real.log (Fintype.card A)-(2*K:ℕ)*Real.log 2)-2*Real.log 2 ≤ entropy Q := by
  have ha := atom_entropy_formula P hP
  have ht := entropy_tv_lower P Q hPQ
  rw [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow] at ht
  nlinarith
end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordHierarchy
open Finset WordParameters WordStep WordAlphabet FiniteLaw

/-- W3 for the actual uniform selected family, in the finite-law API. -/
lemma uniformWindow_close (i : ℕ) (t : Offsets (S i)) :
    TV (uniformWindow i t) (conditionedWindow i t) ≤ 1/10000 := by
  have h := (stage i).windowTV t
  rw [←TV_empirical] at h
  change TV (push uniform ((window (S i) t) ∘ (stage i).w)) (conditionedWindow i t) ≤ _ at h
  have he : uniformWindow i t=push uniform ((window (S i) t) ∘ (stage i).w) := by
    exact uniform_reindex (Fintype.equivFin (A (i+1))) ((window (S i) t) ∘ (stage i).w)
  rwa [he]

/-- W4 for each actual parent: uniformity is only over its slots, never
an assumption on the parent-word distribution. -/
lemma parentWindow_close (i : ℕ) (a : A (i+2)) (t : Offsets (S i)) :
    TV (parentWindow i a t) (uniformWindow i t) ≤ 1/10000 := by
  let : NeZero (q (S (i+1))) := ⟨(q_pos _).ne'⟩
  let : NeZero (H (S (i+1))) := ⟨(H_pos _).ne'⟩
  have hh := TV_grouped (fun b => window (S i) t ((stage i).word b))
    (WordFlatten.flattenEquiv.symm ((stage (i+1)).word a))
  simp only [Equiv.apply_symm_apply] at hh
  change TV (parentWindow i a t) (uniformWindow i t)=
    WordLaw.tvFromUniformObservable (fun b => window (S i) t ((stage i).word b))
      (WordFlatten.flattenEquiv.symm ((stage (i+1)).word a)) at hh
  rw [hh]
  exact stage_approximates i a t

/-- The two and only two approximation costs used in the manuscript. -/
lemma parent_conditioned_close (i : ℕ) (a : A (i+2)) (t : Offsets (S i)) :
    TV (conditionedWindow i t) (parentWindow i a t) ≤ 2/10000 := by
  rw [TV_symm]
  have ht := TV_triangle (parentWindow i a t) (uniformWindow i t) (conditionedWindow i t)
  have h1 := parentWindow_close i a t
  have h2 := uniformWindow_close i t
  linarith

lemma conditioned_prefix_atom (i : ℕ) (t : Offsets (S i)) {r : ℕ} (hr : r ≤ D (S i))
    (v : Fin r → A i) :
    (push (conditionedWindow i t) (takePrefix hr)).mass v ≤
      2*((2:ℝ)^(2*K (S i))/Fintype.card (A i))^r := by
  rw [conditionedWindow,push_comp]
  exact WordFlatten.flat_window_atom (form (S i)) (goodDim i)
    (by change 1 ≤ K (sequence 40000 i); have := (step_conditions initial_threshold i).1; omega)
    (stage i).E (stage i).massE (windowEmbedding i t hr) v

/-- A real entropy lower bound for EVERY selected parent and admissible
internal offset, with fully constructed comparison law and all atom bounds. -/
theorem parent_prefix_entropy (i : ℕ) (a : A (i+2)) (t : Offsets (S i))
    {r : ℕ} (hr : r ≤ D (S i)) :
    (r:ℝ)*((1-2/10000)*Real.log (Fintype.card (A i))-(2*K (S i):ℕ)*Real.log 2)-2*Real.log 2 ≤
      entropy (push (parentWindow i a t) (takePrefix hr)) := by
  exact window_entropy_close (push (conditionedWindow i t) (takePrefix hr)) _
    (conditioned_prefix_atom i t hr)
    ((TV_push _ _ (takePrefix hr)).trans (parent_conditioned_close i a t))
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.FiniteLaw
open MeasureTheory Set Finset
variable {X α β : Type*} [MeasurableSpace X] [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma observed_ext {P Q : Law α} (h : P.mass=Q.mass) : P=Q := by
  cases P; cases Q; cases h; rfl

lemma conditionalObserved_mass (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) (k : X → β) (hk : Measurable k)
    [Nonempty α] (b : β) (a : α) :
    (observed μ k hk).mass b*(conditionalObserved μ f hf k hk b).mass a =
      μ.real {x | k x=b ∧ f x=a} := by
  change μ.real {x | k x=b}*_= _
  unfold conditionalObserved
  dsimp only
  split_ifs with hp
  · rw [hp,zero_mul]
    apply (le_antisymm ?_ measureReal_nonneg).symm
    calc
      _ ≤ μ.real {x | k x=b} := measureReal_mono (by intro x hx; exact hx.1)
      _ = 0 := hp
  · exact mul_div_cancel₀ _ hp

/-- Disintegration over a finite actual observation. Zero conditional masses
are represented by a harmless uniform law and contribute exactly zero. -/
theorem observed_mixture (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) (k : X → β) (hk : Measurable k)
    [Nonempty α] :
    observed μ f hf=mixture (observed μ k hk) (conditionalObserved μ f hf k hk) := by
  apply observed_ext
  funext a
  change μ.real {x | f x=a}=∑ b,_
  simp only [conditionalObserved_mass]
  have h := Alignment.sum_fibers μ {x | f x=a} hk
  simpa only [Set.mem_ofPred_eq,and_comm] using h.symm
end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw
open scoped ENNReal

lemma pack_slots (i : ℕ) (x : Extension) :
    pack (slot (i+1) x,slot i x)=parentSlot i x := by
  apply Fin.ext
  rw [pack_val,slot_pair]

lemma slots_iff (i : ℕ) (x : Extension) (u : Fin (N (S i))) (h : Fin (N (S (i+1)))) :
    slot i x=u ∧ slot (i+1) x=h ↔ parentSlot i x=pack (h,u) := by
  rw [←pack_slots,(Equiv.injective pack).eq_iff,Prod.mk.injEq,and_comm]

lemma boundary_phase_zero (μ : Measure Extension) (i : ℕ) :
    ∀ᵐ x ∂boundary μ i,phase i x=0 := by
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_eq_fun (measurable_phase i) measurable_const)) _

lemma boundary_slots_mass (μ : Measure Extension) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (v : A (i+2))
    (u : Fin (N (S i))) (h : Fin (N (S (i+1)))) :
    (boundary μ i).real {x | label (i+2) x=v ∧ slot i x=u ∧ slot (i+1) x=h} =
      μ.real {x | label (i+2) x=v}/((N (S i):ℝ)*N (S (i+1))) := by
  have he : {x | label (i+2) x=v ∧ slot i x=u ∧ slot (i+1) x=h} =
      {x | parentSlot i x=pack (h,u) ∧ label (i+2) x=v} := by
    ext x
    simp only [Set.mem_ofPred_eq,←slots_iff,and_comm]
  rw [he]
  apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (N_pos _).ne') (Nat.cast_ne_zero.mpr (N_pos _).ne') : (N (S i):ℝ)*N (S (i+1))≠0)).mpr
  have hh := boundary_parentSlot_mass μ hT i v (pack (h,u))
  simpa only [Nat.cast_mul,mul_comm] using hh

lemma boundary_key_mass (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (v : A (i+2)) (u : Fin (N (S i))) :
    (boundary μ i).real {x | windowKey i x=(v,u)} =
      μ.real {x | label (i+2) x=v}/N (S i) := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  rw [←Alignment.sum_fibers (boundary μ i) {x | windowKey i x=(v,u)} (measurable_slot (i+1))]
  have hs (h : Fin (N (S (i+1)))) :
      (boundary μ i).real {x | x∈{x | windowKey i x=(v,u)} ∧ slot (i+1) x=h} =
        μ.real {x | label (i+2) x=v}/((N (S i):ℝ)*N (S (i+1))) := by
    convert boundary_slots_mass μ hT i v u h using 2
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Set.mem_ofPred_eq,windowKey,Prod.mk.injEq,and_assoc]
  simp only [hs,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr (N_pos (S (i+1))).ne']

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw

lemma labelList_key (i r : ℕ) (u : Fin (N (S i))) (hr : u.val+r ≤ N (S i))
    (v : A (i+2)) (h : Fin (N (S (i+1)))) (x : Extension) (hx : phase i x=0)
    (hk : windowKey i x=(v,u)) (hh : slot (i+1) x=h) :
    labelList i r x=sampledWindow i r u hr v h := by
  have hv : label (i+2) x=v := congrArg Prod.fst hk
  have hu : slot i x=u := congrArg Prod.snd hk
  rw [labelList_inside i r x hx (by simpa only [hu] using hr)]
  simp only [hv,hu,hh]
  rfl

/-- Exact disintegration at an admissible offset. Stationarity gives slot
uniformity even when the parent marginal has zero or varying masses. -/
theorem boundary_window_joint (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i r : ℕ) (u : Fin (N (S i)))
    (hr : u.val+r ≤ N (S i)) (v : A (i+2)) (w : Fin r → A i) :
    (boundary μ i).real {x | windowKey i x=(v,u) ∧ labelList i r x=w} =
      (boundary μ i).real {x | windowKey i x=(v,u)}*(sampledLaw i r u hr v).mass w := by
  classical
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  rw [←Alignment.sum_fibers (boundary μ i)
    {x | windowKey i x=(v,u) ∧ labelList i r x=w} (measurable_slot (i+1))]
  have hs (h : Fin (N (S (i+1)))) :
      (boundary μ i).real {x | x∈{x | windowKey i x=(v,u) ∧ labelList i r x=w} ∧ slot (i+1) x=h} =
        if sampledWindow i r u hr v h=w then μ.real {x | label (i+2) x=v}/((N (S i):ℝ)*N (S (i+1))) else 0 := by
    by_cases hw : sampledWindow i r u hr v h=w
    · rw [ite_eq_left hw]
      apply (measureReal_congr ?_).trans (boundary_slots_mass μ hT i v u h)
      filter_upwards [boundary_phase_zero μ i] with x hx
      apply propext
      constructor
      · rintro ⟨⟨hk,_⟩,hh⟩
        exact ⟨congrArg Prod.fst hk,congrArg Prod.snd hk,hh⟩
      · rintro ⟨hv,hu,hh⟩
        have hk : windowKey i x=(v,u) := Prod.ext hv hu
        exact ⟨⟨hk,(labelList_key i r u hr v h x hx hk hh).trans hw⟩,hh⟩
    · rw [ite_eq_right hw]
      apply (measureReal_congr (t := (∅ : Set Extension)) ?_).trans measureReal_empty
      filter_upwards [boundary_phase_zero μ i] with x hx
      apply propext
      change ((windowKey i x=(v,u) ∧ labelList i r x=w) ∧ slot (i+1) x=h) ↔ False
      constructor
      · rintro ⟨⟨hk,hlist⟩,hh⟩
        exact hw ((labelList_key i r u hr v h x hx hk hh).symm.trans hlist)
      · exact False.elim
  simp only [hs,boundary_key_mass μ hT i v u]
  simp only [sampledLaw,push,uniform,Fintype.card_fin]
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  split_ifs <;> simp [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]

/-- The conditional law is the actual finite-parent sampled window law on
all positive-probability fibres. No hypothesis about parent frequencies. -/
lemma conditional_window_eq (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i r : ℕ) (u : Fin (N (S i)))
    (hr : u.val+r ≤ N (S i)) (v : A (i+2))
    (hp : (boundary μ i).real {x | windowKey i x=(v,u)}≠0) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    conditionalObserved (boundary μ i) (labelList i r) (measurable_labelList i r)
      (windowKey i) (measurable_windowKey i) (v,u)=sampledLaw i r u hr v := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  apply mass_ext
  funext w
  have hh := conditionalObserved_mass (boundary μ i) (labelList i r)
    (measurable_labelList i r) (windowKey i) (measurable_windowKey i) (v,u) w
  rw [boundary_window_joint μ hT i r u hr v w] at hh
  exact (mul_left_cancel₀ hp) hh

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordStep FiniteLaw

lemma sampledLaw_prefix (i : ℕ) (a : A (i+2)) (t : Offsets (S i))
    {r : ℕ} (hr : r ≤ D (S i)) :
    sampledLaw i r ((finCongr (q_mul_H (S i))) t.val)
      (by have _ht := t.property; change t.val.val+r ≤ N (S i); rw [←q_mul_H]; omega) a =
      push (parentWindow i a t) (takePrefix hr) := by
  classical
  rw [parentWindow,push_comp]
  have he : (fun j : Fin (groupLength (i+1)) =>
      takePrefix hr (window (S i) t ((stage i).word ((stage (i+1)).word a j)))) =
      sampledWindow i r ((finCongr (q_mul_H (S i))) t.val)
      (by have _ht := t.property; change t.val.val+r ≤ N (S i); rw [←q_mul_H]; omega) a ∘
        (finCongr (q_mul_H (S (i+1)))) := by
    funext j k
    simp only [Function.comp_apply,sampledWindow,children,Equiv.symm_apply_apply,takePrefix,window]
    congr 2
  change push uniform _ = push uniform _
  dsimp only [Function.comp_def]
  rw [he]
  exact (uniform_reindex (finCongr (q_mul_H (S (i+1)))) _).symm

lemma sampled_entropy (i : ℕ) (a : A (i+2)) (u : Fin (N (S i)))
    (hu : u.val+D (S i) ≤ N (S i)) {r : ℕ} (hr : r ≤ D (S i)) :
    windowLower i r ≤ entropy (sampledLaw i r u (by omega) a) := by
  let t : Offsets (S i) := ⟨(finCongr (q_mul_H (S i))).symm u,by
    change u.val+D (S i) ≤ q (S i)*H (S i)
    rwa [q_mul_H]⟩
  have hh := parent_prefix_entropy i a t hr
  rw [←sampledLaw_prefix] at hh
  simpa only [t,windowLower,Equiv.apply_symm_apply] using hh

/-- The entropy of the genuine stationary aligned orbit window is bounded
using the exactly uniform internal-slot law, not a selected parent law. -/
theorem boundary_window_entropy (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i r : ℕ) (hr : r ≤ D (S i)) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    (∑ b : A (i+2) × Fin (N (S i)),
      if b.2.val+D (S i) ≤ N (S i) then
        (observed (boundary μ i) (windowKey i) (measurable_windowKey i)).mass b else 0)*windowLower i r ≤
      entropy (observed (boundary μ i) (labelList i r) (measurable_labelList i r)) := by
  classical
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  dsimp only
  rw [observed_mixture (boundary μ i) (labelList i r) (measurable_labelList i r)
    (windowKey i) (measurable_windowKey i)]
  apply le_trans _ (entropy_mixture _ _)
  rw [sum_mul]
  apply sum_le_sum
  rintro ⟨v,u⟩ _
  by_cases hu : u.val+D (S i) ≤ N (S i)
  · rw [ite_eq_left hu]
    by_cases hp : (boundary μ i).real {x | windowKey i x=(v,u)}=0
    · change (boundary μ i).real {x | windowKey i x=(v,u)}*_ ≤ _
      simp only [hp,zero_mul,observed,le_refl]
    · rw [conditional_window_eq μ hT i r u (by omega) v hp]
      exact mul_le_mul_of_nonneg_left (sampled_entropy i v u hu hr) measureReal_nonneg
  · rw [ite_eq_right hu,zero_mul]
    exact mul_nonneg measureReal_nonneg (entropy_nonneg _)

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordStep FiniteLaw

lemma D_pos (s : ℕ) : 0<D s := by unfold D; positivity

lemma good_offset_count (s : ℕ) :
    #{u : Fin (N s) | u.val+D s ≤ N s}=N s-D s+1 := by
  have hD := D_le_N s
  have hp := D_pos s
  have he : (univ.filter (fun u : Fin (N s) => u.val+D s ≤ N s))=
      (univ.filter (fun u : Fin (N s) => u.val < N s-D s+1)) := by
    apply Finset.filter_congr
    intro u hu
    omega
  rw [he,Fin.card_filter_val_lt,min_eq_right (by omega)]

lemma good_key_mass (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    (∑ b : A (i+2) × Fin (N (S i)),
      if b.2.val+D (S i) ≤ N (S i) then
        (observed (boundary μ i) (windowKey i) (measurable_windowKey i)).mass b else 0)=
      (N (S i)-D (S i)+1:ℕ)/(N (S i):ℝ) := by
  classical
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  dsimp only
  rw [Fintype.sum_prod_type]
  simp only [observed,boundary_key_mass μ hT]
  have hs (v : A (i+2)) :
      (∑ u : Fin (N (S i)),if u.val+D (S i) ≤ N (S i) then
        μ.real {x | label (i+2) x=v}/N (S i) else 0)=
      (N (S i)-D (S i)+1:ℕ)*(μ.real {x | label (i+2) x=v}/N (S i)) := by
    rw [←sum_filter]
    simp only [sum_const,nsmul_eq_mul,good_offset_count]
  simp only [hs]
  rw [←mul_sum,←sum_div]
  have hm := (observed μ (label (i+2)) (measurable_label (i+2))).total
  change (∑ v,μ.real {x | label (i+2) x=v})=1 at hm
  rw [hm,mul_one_div]

/-- The manuscript's explicit stationary entropy lower bound, with the
exact loss from inadmissible offsets and an arbitrary invariant probability. -/
theorem stationary_window_entropy (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i r : ℕ) (hr : r ≤ D (S i)) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    ((N (S i)-D (S i)+1:ℕ)/(N (S i):ℝ))*windowLower i r ≤
      entropy (observed (boundary μ i) (labelList i r) (measurable_labelList i r)) := by
  have hh := boundary_window_entropy μ hT i r hr
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  dsimp only at hh ⊢
  rw [good_key_mass μ hT i] at hh
  exact hh

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordAlphabet WordStep FiniteLaw

lemma log_card (i : ℕ) : Real.log (Fintype.card (A i))=ell (S i)*Real.log 2 := by
  change Real.log (Fintype.card (Alphabet (S i)))=_
  rw [cardAlphabetReal]
  dsimp only [ell,alphabetSize,Real.logb]
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))]

lemma K_large {i : ℕ} (hi : 1 ≤ i) : 4000 ≤ K (S i) := by
  have h := K_double_exponential initial_threshold i
  have hpow : 2 ≤ (2:ℕ)^i := by
    calc
      _ = (2:ℕ)^1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hi
  have hh : (2:ℕ)^16 ≤ 2^(8*2^i) := Nat.pow_le_pow_right (by decide) (by omega)
  exact (by norm_num : 4000 ≤ (2:ℕ)^16).trans (hh.trans h)

lemma bad_offset_small (i : ℕ) : (D (S i):ℝ)/(N (S i):ℝ) ≤ 1/2000 := by
  have hk := (step_conditions initial_threshold i).1
  change 256 ≤ K (S i) at hk
  have he : K (S i)/8+11 ≤ K (S i) := by omega
  have hp : 2048*D (S i) ≤ N (S i) := by
    calc
      _ = 2^(K (S i)/8+11) := by rw [pow_add]; norm_num [D]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) he
  have hr : (2000:ℝ)*(D (S i):ℝ) ≤ N (S i) := by
    exact_mod_cast (show 2000*D (S i) ≤ N (S i) by omega)
  have hN : (0:ℝ)<N (S i) := by exact_mod_cast N_pos (S i)
  apply (div_le_iff₀ hN).mpr
  linarith

lemma good_offset_large (i : ℕ) : (1999/2000:ℝ) ≤
    (N (S i)-D (S i)+1:ℕ)/(N (S i):ℝ) := by
  have hD := D_le_N (S i)
  have hN : (0:ℝ)<N (S i) := by exact_mod_cast N_pos (S i)
  have hb := bad_offset_small i
  rw [Nat.cast_add,Nat.cast_sub hD,Nat.cast_one]
  apply (le_div_iff₀ hN).mpr
  have hb' := (div_le_iff₀ hN).mp hb
  nlinarith

lemma windowLower_large {i r : ℕ} (hi : 1 ≤ i) (hr : 1 ≤ r) :
    (2497/2500:ℝ)*r*Real.log (Fintype.card (A i)) ≤ windowLower i r := by
  have hk : (4000:ℝ)≤K (S i) := by exact_mod_cast K_large hi
  have he := (K_bounds (S i)).1
  have hK : 2*(K (S i):ℝ) ≤ ell (S i)/2000 := by nlinarith
  have h1 : (2:ℝ) ≤ ell (S i)/2000 := by nlinarith
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hepos : 0 ≤ ell (S i) := ell_nonneg _
  have hklog := mul_le_mul_of_nonneg_right hK hlog.le
  have h1log := mul_le_mul_of_nonneg_right h1 hlog.le
  have hklogr := mul_le_mul_of_nonneg_left hklog (show (0:ℝ) ≤ r by positivity)
  have hcost : 2*Real.log 2 ≤ (r:ℝ)*(ell (S i)/2000*Real.log 2) := by
    exact h1log.trans (le_mul_of_one_le_left (by positivity) hr')
  rw [windowLower,log_card]
  push_cast
  nlinarith

/-- Uniform stationary window entropy, with the manuscript's decimal constant.
It is valid already at level one beyond the fixed initial level, independently
of the stationary probability and independently of the window length. Entropy
here uses natural logarithms, so both sides have the same conversion factor. -/
theorem stationary_window_entropy_996 (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {i r : ℕ} (hi : 1 ≤ i)
    (hr : 1 ≤ r) (hrD : r ≤ D (S i)) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    (996/1000:ℝ)*r*Real.log (Fintype.card (A i)) ≤
      entropy (observed (boundary μ i) (labelList i r) (measurable_labelList i r)) := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  dsimp only
  have hh := stationary_window_entropy μ hT i r hrD
  dsimp only at hh
  have hl := windowLower_large hi hr
  have hg := good_offset_large i
  have hlog : 0 ≤ Real.log (Fintype.card (A i)) := by
    rw [log_card]
    exact mul_nonneg (ell_nonneg _) (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hpos : 0 ≤ (2497/2500:ℝ)*r*Real.log (Fintype.card (A i)) := by positivity
  calc
    _ ≤ (1999/2000:ℝ)*((2497/2500:ℝ)*r*Real.log (Fintype.card (A i))) := by nlinarith
    _ ≤ ((N (S i)-D (S i)+1:ℕ)/(N (S i):ℝ))*windowLower i r :=
      mul_le_mul hg hl hpos (by positivity)
    _ ≤ _ := hh

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordAlphabet WordStep WordConcatenation MeasureTheory Set Finset

lemma graph_block_room (i k : ℕ) (hk : k ≤ K (S i)/8) : 2*2^k ≤ H (S i) := by
  have hK := (step_conditions initial_threshold i).1
  change 256 ≤ K (S i) at hK
  have he : k+1 ≤ K (S i)/2 := by omega
  calc
    _ = 2^(k+1) := by rw [pow_succ]; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

lemma children_graph (i k : ℕ) (hk : k ≤ K (S i)/8)
    (a : A (i+1)) (u : Fin (N (S i))) (j : ℕ)
    (hr : u.val%H (S i)+j+2^k < H (S i)) :
    let h₁ : u.val+j < N (S i) := by
      have hh := group_site_lt i u (show u.val%H (S i)+j<H (S i) from lt_of_le_of_lt (Nat.le_add_right _ _) hr)
      have he := Nat.div_add_mod u.val (H (S i))
      omega
    let h₂ : u.val+j+2^k < N (S i) := by
      have hh := group_site_lt i u hr
      have he := Nat.div_add_mod u.val (H (S i))
      omega
    form (S i) (children i a ⟨u.val+j,h₁⟩).val
      (children i a ⟨u.val+j+2^k,h₂⟩).val=0 := by
  dsimp only
  have hK := (step_conditions initial_threshold i).1
  change 256 ≤ K (S i) at hK
  have hkk : k<K (S i) := by omega
  let b : Fin (q (S i)) := ⟨u.val/H (S i),by
    apply (Nat.div_lt_iff_lt_mul (H_pos (S i))).mpr
    rw [q_mul_H]
    exact u.isLt⟩
  have hh := (stage i).relations ((Fintype.equivFin (A (i+1))) a) b
    (u.val%H (S i)+j) k hkk hk hr
  have he₁ : (finCongr (q_mul_H (S i))).symm
      (⟨u.val+j,by
        have hh := group_site_lt i u (show u.val%H (S i)+j<H (S i) from lt_of_le_of_lt (Nat.le_add_right _ _) hr)
        have he := Nat.div_add_mod u.val (H (S i)); omega⟩ : Fin (N (S i))) =
      finProdFinEquiv (b,⟨u.val%H (S i)+j,lt_of_le_of_lt (Nat.le_add_right _ _) hr⟩) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    change u.val+j = u.val%H (S i)+j+H (S i)*(u.val/H (S i))
    have he := Nat.mod_add_div u.val (H (S i))
    omega
  have he₂ : (finCongr (q_mul_H (S i))).symm
      (⟨u.val+j+2^k,by
        have hh := group_site_lt i u hr
        have he := Nat.div_add_mod u.val (H (S i)); omega⟩ : Fin (N (S i))) =
      finProdFinEquiv (b,⟨u.val%H (S i)+j+2^k,hr⟩) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    change u.val+j+2^k = u.val%H (S i)+j+2^k+H (S i)*(u.val/H (S i))
    have he := Nat.mod_add_div u.val (H (S i))
    omega
  simpa only [children,Family.word,he₁,he₂] using hh

lemma graphWindows_of_good (i k : ℕ) (hk : k ≤ K (S i)/8) (x : Extension)
    (hx : phase i x=0)
    (hgood : (slot i x).val%H (S i)+(2*2^k-1) ≤ H (S i)) :
    graphWindows i k x := by
  intro j
  have hD : 0<(2:ℕ)^k := by positivity
  have hj := j.isLt
  have hr : (slot i x).val%H (S i)+j.val+2^k < H (S i) := by omega
  have hh := children_graph i k hk (label (i+1) x) (slot i x) j.val hr
  dsimp only at hh
  have he := Nat.div_add_mod (slot i x).val (H (S i))
  have h₁ : (slot i x).val+j.val<N (S i) := by
    have hh := group_site_lt i (slot i x) (show (slot i x).val%H (S i)+j.val<H (S i) by omega)
    omega
  have h₂ : (slot i x).val+(j.val+2^k)<N (S i) := by
    have hh := group_site_lt i (slot i x) hr
    omega
  rw [label_advance_child i j.val x hx h₁,label_advance_child i (j.val+2^k) x hx h₂]
  simpa only [Nat.add_assoc] using hh

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordAlphabet WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw

lemma boundary_slot_mass (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (u : Fin (N (S i))) :
    (boundary μ i).real {x | slot i x=u}=1/(N (S i):ℝ) := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  rw [←Alignment.sum_fibers (boundary μ i) {x | slot i x=u} (measurable_label (i+2))]
  have he (v : A (i+2)) : {x | x∈{x | slot i x=u} ∧ label (i+2) x=v}=
      {x | windowKey i x=(v,u)} := by
    ext x
    simp only [Set.mem_ofPred_eq,windowKey,Prod.mk.injEq,and_comm]
  simp only [he,boundary_key_mass μ hT]
  rw [←sum_div]
  have hm := (observed μ (label (i+2)) (measurable_label (i+2))).total
  change (∑ v,μ.real {x | label (i+2) x=v})=1 at hm
  rw [hm]

lemma residue_sum (i c : ℕ) (hc : c ≤ H (S i)) :
    (∑ u : Fin (N (S i)), if u.val%H (S i) < c then (1:ℝ)/N (S i) else 0)=
      (c:ℝ)/H (S i) := by
  classical
  let e : Fin (q (S i)) × Fin (H (S i)) ≃ Fin (N (S i)) :=
    finProdFinEquiv.trans (finCongr (q_mul_H (S i)))
  have he (v : Fin (q (S i)) × Fin (H (S i))) : (e v).val%H (S i)=v.2.val := by
    change (v.2.val+H (S i)*v.1.val)%H (S i)=v.2.val
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod,Nat.add_zero,
      Nat.mod_eq_of_lt v.2.isLt]
  rw [←e.sum_comp]
  simp only [he,Fintype.sum_prod_type]
  have hs : (∑ r : Fin (H (S i)),if r.val < c then (1:ℝ)/N (S i) else 0)=
      (c:ℝ)/N (S i) := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,Fin.card_filter_val_lt,min_eq_right hc,mul_one_div]
  simp only [hs,sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [←q_mul_H (S i),Nat.cast_mul]
  have hq : (q (S i):ℝ)≠0 := by exact_mod_cast (q_pos (S i)).ne'
  field_simp

lemma boundary_residue_mass (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i c : ℕ) (hc : c ≤ H (S i)) :
    (boundary μ i).real {x | (slot i x).val%H (S i) < c}=(c:ℝ)/H (S i) := by
  classical
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  rw [←Alignment.sum_fibers (boundary μ i)
    {x | (slot i x).val%H (S i) < c} (measurable_slot i)]
  have hs (u : Fin (N (S i))) :
      (boundary μ i).real {x | x∈{x | (slot i x).val%H (S i) < c} ∧ slot i x=u}=
      if u.val%H (S i) < c then (1:ℝ)/N (S i) else 0 := by
    split_ifs with hu
    · have he : {x | x∈{x | (slot i x).val%H (S i) < c} ∧ slot i x=u}={x | slot i x=u} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor
        · exact And.right
        · intro hx; exact ⟨by simpa only [hx] using hu,hx⟩
      rw [he,boundary_slot_mass μ hT]
    · have he : {x | x∈{x | (slot i x).val%H (S i) < c} ∧ slot i x=u}=∅ := by
        ext x
        simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
        rintro ⟨hr,hx⟩
        exact hu (by simpa only [hx] using hr)
      rw [he,measureReal_empty]
  simp only [hs]
  exact residue_sum i c hc

/-- The two lists of the actual system pass all graph tests simultaneously
except for the precise group-boundary fraction (2D-2)/H. -/
theorem boundary_graph_probability (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i k : ℕ) (hk : k ≤ K (S i)/8) :
    1-((2*2^k-2:ℕ):ℝ)/H (S i) ≤
      (boundary μ i).real {x | graphWindows i k x} := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  have hD : 0<(2:ℕ)^k := by positivity
  have hH := graph_block_room i k hk
  let c := H (S i)-(2*2^k-1)+1
  have hc : c ≤ H (S i) := by dsimp only [c]; omega
  have he : {x : Extension | (slot i x).val%H (S i) < c}=
      {x | (slot i x).val%H (S i)+(2*2^k-1)≤H (S i)} := by
    ext x
    change (slot i x).val%H (S i) < c ↔
      (slot i x).val%H (S i)+(2*2^k-1)≤H (S i)
    dsimp only [c]
    omega
  have hm := boundary_residue_mass μ hT i c hc
  rw [he] at hm
  have hle : (boundary μ i).real {x | (slot i x).val%H (S i)+(2*2^k-1)≤H (S i)} ≤
      (boundary μ i).real {x | graphWindows i k x} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [boundary_phase_zero μ i] with x hx
    exact fun hg => graphWindows_of_good i k hk x hx hg
  rw [hm] at hle
  have hc' : c=H (S i)-(2*2^k-2) := by dsimp only [c]; omega
  have hsub : 2*2^k-2 ≤ H (S i) := by omega
  rw [hc',Nat.cast_sub hsub] at hle
  have hHp : (H (S i):ℝ)≠0 := by exact_mod_cast (H_pos (S i)).ne'
  convert hle using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end SmoothObstruction.WordHierarchy

end

section

open Finset

namespace SmoothObstruction.FiniteLaw
open MeasureTheory Set Finset
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Every finite observable's real expectation agrees with integration in
its original probability space. No conditional normalization occurs. -/
theorem observed_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) (g : α → ℝ) :
    (∑ a,(observed μ f hf).mass a*g a)=∫ x,g (f x) ∂μ := by
  calc
    _ = ∫ a,g a ∂(μ.map f) := by
      rw [integral_fintype (Integrable.of_finite (μ:=μ.map f))]
      apply sum_congr rfl
      intro a _
      simp only [observed,Measure.real,Measure.map_apply hf (measurableSet_singleton a),
        smul_eq_mul]
      rfl
    _ = _ := integral_map hf.aemeasurable (measurable_of_countable g).aestronglyMeasurable

/-- A lower bound on a success event is a lower bound in the UNCONDITIONED
law. In particular .95 mass at statistic .96 gives expectation .912. -/
theorem integral_lower_of_event (μ : Measure X) [IsProbabilityMeasure μ]
    (Z : X → ℝ) (hZi : Integrable Z μ) (hZn : ∀ x,0≤Z x)
    (G : Set X) (hG : MeasurableSet G) (a b : ℝ) (ha : 0≤a)
    (hGm : b≤μ.real G) (hZG : ∀ x∈G,a≤Z x) :
    a*b≤∫ x,Z x ∂μ := by
  calc
    a*b ≤ μ.real G*a := by nlinarith
    _ = ∫ x,G.indicator (fun _ => a) x ∂μ := by
      rw [integral_indicator_const a hG,smul_eq_mul]
    _ ≤ _ := integral_mono_ae ((integrable_const a).indicator hG) hZi
      (Filter.Eventually.of_forall (fun x => by
        by_cases hx : x∈G
        · simpa only [indicator_of_mem hx] using hZG x hx
        · simpa only [indicator_of_notMem hx] using hZn x))

end SmoothObstruction.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PairBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Classical
open Finset

namespace SmoothObstruction.FiniteLaw
open Finset FiniteEntropy
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma expect_push_sum (P : Law α) (f : α → β) (g : β → ℝ) :
    (∑ b,(push P f).mass b*g b)=∑ a,P.mass a*g (f a) := by
  classical
  simp only [push,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]

/-- The finite push mass, independent of the choice of equality decision procedure. -/
lemma push_mass_canonical [DecidableEq β] (P : Law α) (f : α → β) :
    (push P f).mass=FiniteEntropy.pushMass P.mass f := by
  funext b
  change (∑ a,if f a=b then P.mass a else 0)=_
  unfold FiniteEntropy.pushMass
  apply sum_congr rfl
  intro a _
  split_ifs <;> rfl

lemma mass_le_push (P : Law α) (f : α → β) (a : α) :
    P.mass a≤(push P f).mass (f a) := by
  classical
  change P.mass a≤∑ x,if f x=f a then P.mass x else 0
  have hh := single_le_sum (s:=univ) (f:=fun x => if f x=f a then P.mass x else 0)
    (fun x _ => by split_ifs; exact P.nonneg x; exact le_rfl) (mem_univ a)
  simpa only [ite_true] using hh

/-- The conditioning cost is the actual entropy of the mixing variable;
zero cell masses contribute zero. -/
lemma entropy_mixture_upper (P : Law α) (Q : α → Law β) :
    entropy (mixture P Q)≤entropy P+∑ a,P.mass a*entropy (Q a) := by
  let p : α × β → ℝ := fun z => P.mass z.1*(Q z.1).mass z.2
  have hp : ∀ z,0≤p z := fun z => mul_nonneg (P.nonneg z.1) ((Q z.1).nonneg z.2)
  have hproj : pushMass p Prod.snd=(mixture P Q).mass := by
    classical
    funext b
    simp only [pushMass,Fintype.sum_prod_type,p,mixture]
    simp only [sum_ite_eq',mem_univ,ite_true]
  have hh := FiniteEntropy.entropy_push_le hp Prod.snd
  rw [hproj] at hh
  have hj := FiniteEntropy.entropy_joint P.mass (fun a => (Q a).mass) (fun a => (Q a).total)
  exact hh.trans_eq hj

lemma entropy_card (P : Law α) : entropy P≤Real.log (Fintype.card α) :=
  FiniteEntropy.entropy_le_log_card P.nonneg P.total

/-- Entropy of a finite vector is bounded by the sum of its entry entropies.
The proof works directly for any finite index type, including the empty case. -/
lemma entropy_vector_le {J : Type*} [Fintype J] [DecidableEq J] (P : Law (J → α)) :
    entropy P≤∑ j,entropy (push P (fun w => w j)) := by
  classical
  let q (j : J) := push P (fun w => w j)
  have hsum : (∑ w : J → α,∏ j,(q j).mass (w j))=1 := by
    have hh := prod_univ_sum (fun _ : J => (univ : Finset α)) (fun j a => (q j).mass a)
    simpa only [Fintype.piFinset_univ,(q _).total,prod_const_one] using hh.symm
  have hpoint (w : J → α) : Real.negMulLog (P.mass w)≤
      (∑ j,-P.mass w*Real.log ((q j).mass (w j)))+
        (∏ j,(q j).mass (w j))-P.mass w := by
    rcases (P.nonneg w).eq_or_lt with hz|hp
    · rw [←hz]
      simp only [Real.negMulLog_zero,neg_zero,zero_mul,sum_const_zero,zero_add,sub_zero]
      exact prod_nonneg (fun j _ => (q j).nonneg _)
    · have hqp (j : J) : 0<(q j).mass (w j) := hp.trans_le (mass_le_push P _ w)
      have hh := FiniteEntropy.negMulLog_le_cross hp.le (prod_pos (s:=univ) (fun j _ => hqp j))
      rw [Real.log_prod (fun j _ => (hqp j).ne'),mul_sum] at hh
      exact hh
  have he (j : J) : (∑ w,P.mass w*(-Real.log ((q j).mass (w j))))=entropy (q j) := by
    rw [←expect_push_sum P (fun w => w j) (fun a => -Real.log ((q j).mass a))]
    simp only [entropy,natEntropy,Real.negMulLog_def,mul_neg,neg_mul,q]
  have hs := sum_le_sum (fun w (_ : w∈univ) => hpoint w)
  rw [sum_sub_distrib,sum_add_distrib,sum_comm,hsum,P.total,add_sub_cancel_right] at hs
  simp only [neg_mul,←mul_neg,he] at hs
  exact hs

/-- Finite-vector entropy after conditioning on a finite cell partition.
No product assertion after mixing a shared entry index is used. -/
theorem conditional_entry_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : Law α) (Q : α → Law (J → β)) :
    entropy (mixture P Q)-Real.log (Fintype.card α)≤
      ∑ a,P.mass a*∑ j,entropy (push (Q a) (fun w => w j)) := by
  have h1 := entropy_mixture_upper P Q
  have h2 := entropy_card P
  have h3 := sum_le_sum (fun a (_ : a∈univ) =>
    mul_le_mul_of_nonneg_left (entropy_vector_le (Q a)) (P.nonneg a))
  linarith

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.BinaryCharacter

lemma eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a
lemma sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  rcases eq_zero_or_one a with rfl | rfl <;>
    rcases eq_zero_or_one b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, sign_zero, sign_one]
    norm_num
@[simp] lemma sign_neg (a : ZMod 2) : sign (-a) = sign a := by
  rcases eq_zero_or_one a with rfl | rfl <;>
    simp [show -(1 : ZMod 2) = 1 by decide]
lemma sign_sub (a b : ZMod 2) : sign (a - b) = sign a * sign b := by
  rw [sub_eq_add_neg, sign_add, sign_neg]
lemma one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  exact (eq_zero_or_one a).resolve_left ha

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Character cancellation: translation by any point where a functional is
one changes every summand's sign. No probabilistic estimate is assumed. -/
lemma sum_sign_eq_zero {f : V →ₗ[ZMod 2] ZMod 2}
    (hf : ∃ v, f v ≠ 0) : ∑ v, sign (f v) = 0 := by
  classical
  obtain ⟨w, hw⟩ := hf
  have hw' := one_of_ne_zero hw
  have hsum := Equiv.sum_comp (Equiv.addRight w) (fun v => sign (f v))
  change (∑ v, sign (f (v + w))) = ∑ v, sign (f v) at hsum
  simp only [map_add, sign_add, hw', sign_one, mul_neg_one,
    sum_neg_distrib] at hsum
  linarith

/-- Exact row orthogonality for the full binary bilinear character matrix. -/
lemma row_orthogonality [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (u w : V) :
    ∑ v, sign (B u v) * sign (B w v) = if u = w then (Fintype.card V : ℝ) else 0 := by
  classical
  by_cases huw : u = w
  · subst w
    simp [← sq]
  · rw [ite_eq_right huw]
    have he : ∃ v, B (u - w) v ≠ 0 := by
      by_contra h
      push Not at h
      exact sub_ne_zero.mpr huw (hB.1 (u - w) h)
    convert sum_sign_eq_zero he using 1
    all_goals try with_reducible_and_instances rfl
    apply sum_congr rfl
    intro v _
    simp [LinearMap.map_sub, sign_sub]

lemma column_orthogonality [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (v w : V) :
    ∑ u, sign (B u v) * sign (B u w) = if v = w then (Fintype.card V : ℝ) else 0 := by
  exact row_orthogonality B.flip hB.flip v w

/-- The finite Parseval identity, useful also for nonuniform light laws. -/
lemma parseval (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ℝ) :
    ∑ u, (∑ v, sign (B u v) * q v) ^ 2 = (Fintype.card V : ℝ) * ∑ v, q v ^ 2 := by
  classical
  have hexpand (u : V) : (∑ v, sign (B u v) * q v) ^ 2 =
      ∑ v, ∑ w, q v * q w * (sign (B u v) * sign (B u w)) := by
    rw [sq, sum_mul]
    apply sum_congr rfl
    intro v _
    rw [mul_sum]
    apply sum_congr rfl
    intro w _
    ring
  simp_rw [hexpand]
  rw [sum_comm]
  calc
    _ = ∑ v, ∑ w, q v * q w * (∑ u, sign (B u v) * sign (B u w)) := by
      apply sum_congr rfl
      intro v _
      rw [sum_comm]
      apply sum_congr rfl
      intro w _
      rw [mul_sum]
    _ = _ := by
      simp only [column_orthogonality B hB]
      simp [mul_ite, mul_comm, sq, mul_sum]

/-- Squared spectral estimate with the exact matrix size, obtained from
Parseval and the finite Cauchy--Schwarz inequality. -/
theorem bilinear_sq_le (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (p q : V → ℝ) :
    (∑ u, ∑ v, p u * sign (B u v) * q v) ^ 2 ≤
      (Fintype.card V : ℝ) * (∑ u, p u ^ 2) * (∑ v, q v ^ 2) := by
  classical
  have h := sum_mul_sq_le_sq_mul_sq univ p (fun u => ∑ v, sign (B u v) * q v)
  rw [parseval B hB] at h
  calc
    _ = (∑ u, p u * ∑ v, sign (B u v) * q v) ^ 2 := by
      simp only [mul_sum, mul_assoc]
    _ ≤ _ := h
    _ = _ := by ring

lemma sign_indicator (a : ZMod 2) :
    (if a = 0 then (1 : ℝ) else 0) = (1 + sign a) / 2 := by
  unfold sign
  split_ifs <;> norm_num

section Nonzero
variable [DecidableEq V]

omit [Module (ZMod 2) V] in
lemma sum_remove_zero (f : V → ℝ) (hf : f 0 = 0) :
    ∑ v, f v = ∑ v : {v : V // v ≠ 0}, f v := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0, hf, zero_add]

/-- Restricting the character matrix to nonzero indices retains the full
space spectral bound, including its diagonal entries. -/
lemma nonzero_bilinear_sq_le (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (p q : {v : V // v ≠ 0} → ℝ) :
    (∑ u : {v : V // v ≠ 0}, ∑ v : {v : V // v ≠ 0}, p u * sign (B u v) * q v) ^ 2 ≤
      (Fintype.card V : ℝ) * (∑ u, p u ^ 2) * (∑ v, q v ^ 2) := by
  have h := bilinear_sq_le B hB (extendZero p) (extendZero q)
  have hleft : (∑ u, ∑ v, extendZero p u * sign (B u v) * extendZero q v) =
      ∑ u : {v : V // v ≠ 0}, ∑ v : {v : V // v ≠ 0}, p u * sign (B u v) * q v := by
    rw [sum_remove_zero _ (by simp)]
    apply sum_congr rfl
    intro u _
    rw [sum_remove_zero _ (by simp)]
    simp
  have hp : (∑ u, (extendZero p u) ^ 2) = ∑ u, p u ^ 2 := by
    rw [sum_remove_zero _ (by simp)]
    simp
  have hq : (∑ u, (extendZero q u) ^ 2) = ∑ u, q u ^ 2 := by
    rw [sum_remove_zero _ (by simp)]
    simp
  simpa only [hleft, hp, hq] using h

end Nonzero
end SmoothObstruction.BinaryCharacter

namespace SmoothObstruction.GraphBound
open BinaryCharacter

variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma light_nonneg {τ : ℝ} {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) (i : α) :
    0 ≤ light τ p i := by unfold light; split_ifs; exact hp i; exact le_rfl
omit [Fintype α] in
lemma light_le {τ : ℝ} {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) (i : α) :
    light τ p i ≤ p i := by unfold light; split_ifs; exact le_rfl; exact hp i
omit [Fintype α] in
lemma light_le_threshold {τ : ℝ} (hτ : 0 ≤ τ) (p : α → ℝ) (i : α) :
    light τ p i ≤ τ := by unfold light; split_ifs with h; exact h; exact hτ

lemma sum_light_le_one {τ : ℝ} {p : α → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : ∑ i, light τ p i ≤ 1 := by
  calc
    _ ≤ ∑ i, p i := sum_le_sum (fun i _ => light_le hp i)
    _ = 1 := hsum

lemma sum_light_sq_le {τ : ℝ} (hτ : 0 ≤ τ) {p : α → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, light τ p i ^ 2 ≤ τ := by
  calc
    _ ≤ ∑ i, τ * light τ p i := sum_le_sum (fun i _ => by
      nlinarith [light_nonneg (τ := τ) hp i, light_le_threshold hτ p i])
    _ = τ * ∑ i, light τ p i := by rw [mul_sum]
    _ ≤ τ * 1 := mul_le_mul_of_nonneg_left (sum_light_le_one hp hsum) hτ
    _ = τ := mul_one _

/-- Pointwise removal of all pairs with a heavy coordinate. -/
lemma remove_heavy_pointwise {τ p q t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (_ht : 0 ≤ t) (ht' : t ≤ 1) :
    p * q * t ≤ (if p ≤ τ then p else 0) * (if q ≤ τ then q else 0) * t +
      (p - if p ≤ τ then p else 0) * q + p * (q - if q ≤ τ then q else 0) := by
  split_ifs <;> nlinarith [mul_nonneg hp hq, mul_nonneg (mul_nonneg hp hq) _ht,
    mul_nonneg (mul_nonneg hp hq) (sub_nonneg.mpr ht')]

/-- Exactly the independent law (not a conditioned or resampled law). -/
theorem passing_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (e : α → V) {p q : α → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    {τ β : ℝ}
    (hlight : ∑ u, ∑ v, light τ p u * sign (B (e u) (e v)) * light τ q v ≤ β) :
    passing B e p q ≤ (∑ u, (p u - light τ p u)) +
      (∑ v, (q v - light τ q v)) + (1 + β) / 2 := by
  have heq : passing B e (light τ p) (light τ q) =
      ((∑ u, light τ p u) * (∑ v, light τ q v) +
        ∑ u, ∑ v, light τ p u * sign (B (e u) (e v)) * light τ q v) / 2 := by
    unfold passing
    calc
      _ = ∑ u, ∑ v, (light τ p u * light τ q v +
          light τ p u * sign (B (e u) (e v)) * light τ q v) / 2 := by
        apply sum_congr rfl
        intro u _
        apply sum_congr rfl
        intro v _
        rw [sign_indicator]
        ring
      _ = _ := by
        simp only [← sum_div, sum_add_distrib, ← mul_sum, ← sum_mul]
  have hmass : (∑ u, light τ p u) * (∑ v, light τ q v) ≤ 1 := by
    exact (mul_le_mul (sum_light_le_one hp hpsum) (sum_light_le_one hq hqsum)
      (sum_nonneg (fun i _ => light_nonneg hq i)) zero_le_one).trans_eq (mul_one 1)
  have hll : passing B e (light τ p) (light τ q) ≤ (1 + β) / 2 := by
    rw [heq]
    linarith
  have hpoint := fun (u v : α) => remove_heavy_pointwise (τ := τ) (hp u) (hq v)
    (show (0 : ℝ) ≤ if B (e u) (e v) = 0 then 1 else 0 by split_ifs <;> norm_num)
    (show (if B (e u) (e v) = 0 then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
  have hsum := sum_le_sum (s := univ) (fun u _ =>
    sum_le_sum (s := univ) (fun v _ => hpoint u v))
  change passing B e p q ≤ ∑ u, ∑ v,
    ((light τ p u * light τ q v * if B (e u) (e v) = 0 then 1 else 0) +
      (p u - light τ p u) * q v + p u * (q v - light τ q v)) at hsum
  simp only [sum_add_distrib, ← mul_sum, hqsum, mul_one, ← sum_mul, hpsum, one_mul] at hsum
  change passing B e p q ≤ passing B e (light τ p) (light τ q) +
    (∑ u, (p u - light τ p u)) + (∑ v, (q v - light τ q v)) at hsum
  linarith

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]

lemma light_spectral_bound (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    {p q : {v : V // v ≠ 0} → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    |∑ u : {v : V // v ≠ 0}, ∑ v : {v : V // v ≠ 0},
      light τ p u * sign (B u v) * light τ q v| ≤ Real.sqrt (Fintype.card V) * τ := by
  have h := nonzero_bilinear_sq_le B hB (light τ p) (light τ q)
  have hm : (Fintype.card V : ℝ) * (∑ u, light τ p u ^ 2) * (∑ v, light τ q v ^ 2) ≤
      (Fintype.card V : ℝ) * τ ^ 2 := by
    calc
      _ ≤ (Fintype.card V : ℝ) * τ * τ := by
        gcongr
        · exact sum_light_sq_le hτ hp hpsum
        · exact sum_light_sq_le hτ hq hqsum
      _ = _ := by ring
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hτ)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact h.trans hm

end SmoothObstruction.GraphBound

namespace SmoothObstruction.GraphEntropy
open FiniteEntropy GraphBound BinaryCharacter

lemma spectral_small {L : ℝ} (hL : 1 ≤ L)
    (hlog : 1000 * Real.log 2 ≤ Real.log L) :
    Real.sqrt (L + 1) * Real.exp (-(4 / 5 : ℝ) * Real.log L) ≤ 1 / 50 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : -(3 / 5 : ℝ) * Real.log L ≤ -(14 * Real.log 2) := by linarith
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1 / 50)).mp
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ L + 1), sq (Real.exp _), ← Real.exp_add]
  calc
    _ ≤ 2 * L * Real.exp (-(4 / 5 : ℝ) * Real.log L + -(4 / 5 : ℝ) * Real.log L) := by
      gcongr
      linarith
    _ = 2 * Real.exp (-(3 / 5 : ℝ) * Real.log L) := by
      conv_lhs => rw [mul_assoc, show L = Real.exp (Real.log L) from
        (Real.exp_log (by linarith : 0 < L)).symm]
      rw [← Real.exp_add, Real.log_exp]
      congr 2
      ring
    _ ≤ 2 * Real.exp (-(14 * Real.log 2)) := by gcongr
    _ = 2 / (2 : ℝ) ^ 14 := by
      rw [Real.exp_neg, show (14 : ℝ) * Real.log 2 = (14 : ℕ) * Real.log 2 by norm_num,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ (1 / 50 : ℝ) ^ 2 := by norm_num

variable {α ξ : Type*} [Fintype α] [Nonempty α] [Fintype ξ]

lemma average_heavy_le (w : ξ → ℝ) (p : ξ → α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (hp : ∀ x i, 0 ≤ p x i) (hp1 : ∀ x, ∑ i, p x i = 1)
    (hH : (99 / 100 : ℝ) * Real.log (Fintype.card α) ≤ ∑ x, w x * natEntropy (p x))
    (hlog : 1000 * Real.log 2 ≤ Real.log (Fintype.card α)) :
    ∑ x, w x * heavyMass (4 / 5) (p x) ≤ 11 / 200 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : 0 < Real.log (Fintype.card α) := by linarith
  have hsum := sum_le_sum (s := univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (entropy_le_heavy (hp x) (hp1 x) (4 / 5)) (hw x))
  have hrhs : (∑ x, w x * (Real.log 2 + (1 - (1 - (4 / 5 : ℝ)) *
      heavyMass (4 / 5) (p x)) * Real.log (Fintype.card α))) =
      Real.log 2 + (1 - (1 / 5 : ℝ) * (∑ x, w x * heavyMass (4 / 5) (p x))) *
        Real.log (Fintype.card α) := by
    calc
      _ = ∑ x, (w x * Real.log 2 + w x * Real.log (Fintype.card α) -
          (w x * heavyMass (4 / 5) (p x)) * ((1 / 5 : ℝ) * Real.log (Fintype.card α))) := by
        apply sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← sum_mul, hw1]
        ring
  rw [hrhs] at hsum
  have hh : (1 / 5 : ℝ) * (∑ x, w x * heavyMass (4 / 5) (p x)) *
      Real.log (Fintype.card α) ≤ (11 / 1000 : ℝ) * Real.log (Fintype.card α) := by
    linarith
  have h := (mul_le_mul_iff_left₀ hlogpos).mp hh
  linarith

omit [Nonempty α] in
lemma tail_eq_heavy {p : α → ℝ} :
    (∑ i, (p i - light (Real.exp (-(4 / 5 : ℝ) * Real.log (Fintype.card α))) p i)) =
      heavyMass (4 / 5) p := by
  apply sum_congr rfl
  intro i _
  unfold light
  split_ifs with h h' h'
  · linarith
  · simp
  · simp
  · simp_all only [not_le]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The independent graph-test bound needed in the actual cell experiment.
This retains diagonal pairs and uses the original (not renormalized) input laws.
The finite index includes both the cell and the coordinate of the label list. -/
theorem graph_independent_finite (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (w : ξ → ℝ) (p q : ξ → {v : V // v ≠ 0} → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (hp : ∀ x i, 0 ≤ p x i) (hq : ∀ x i, 0 ≤ q x i)
    (hp1 : ∀ x, ∑ i, p x i = 1) (hq1 : ∀ x, ∑ i, q x i = 1)
    (hHp : (99 / 100 : ℝ) * Real.log (Fintype.card {v : V // v ≠ 0}) ≤
      ∑ x, w x * natEntropy (p x))
    (hHq : (99 / 100 : ℝ) * Real.log (Fintype.card {v : V // v ≠ 0}) ≤
      ∑ x, w x * natEntropy (q x))
    (hlog : 1000 * Real.log 2 ≤ Real.log (Fintype.card {v : V // v ≠ 0})) :
    ∑ x, w x * passing B Subtype.val (p x) (q x) ≤ 31 / 50 := by
  have : Nonempty {v : V // v ≠ 0} := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨v, hv⟩⟩
  let L : ℝ := Fintype.card {v : V // v ≠ 0}
  let τ := Real.exp (-(4 / 5 : ℝ) * Real.log L)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ‹Nonempty {v : V // v ≠ 0}›))
  have hcard : (Fintype.card V : ℝ) = L + 1 := by
    have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : V))
    simp only [Fintype.card_option] at h
    dsimp [L]
    exact_mod_cast h.symm
  have hτ : 0 ≤ τ := Real.exp_nonneg _
  have hβ : Real.sqrt (Fintype.card V) * τ ≤ 1 / 50 := by
    rw [hcard]
    exact spectral_small hL hlog
  have hsingle (x : ξ) : passing B Subtype.val (p x) (q x) ≤
      heavyMass (4 / 5) (p x) + heavyMass (4 / 5) (q x) + 51 / 100 := by
    have hs := light_spectral_bound B hB (hp x) (hq x) (hp1 x) (hq1 x) hτ
    have hh := passing_le B Subtype.val (hp x) (hq x) (hp1 x) (hq1 x)
      ((le_abs_self _).trans (hs.trans hβ))
    rw [tail_eq_heavy, tail_eq_heavy] at hh
    norm_num at hh ⊢
    exact hh
  have havg := sum_le_sum (s := univ) (fun x _ => mul_le_mul_of_nonneg_left (hsingle x) (hw x))
  simp only [mul_add, sum_add_distrib, ← sum_mul, hw1, one_mul] at havg
  have hpH := average_heavy_le w p hw hw1 hp hp1 hHp hlog
  have hqH := average_heavy_le w q hw hw1 hq hq1 hHq hlog
  linarith

end SmoothObstruction.GraphEntropy

namespace SmoothObstruction.IndependentUpper
open Finset FiniteLaw FiniteEntropy
variable {C J V : Type*} [Fintype C] [Fintype J] [DecidableEq J] [Nonempty J]
  [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The independent upper bound of source section 7 from the entropies of
actual whole lists and the finite cell cost. Independence is used only
conditional on the FULL index (cell,entry), never after mixing entries. -/
theorem list_graph_upper (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (P : Law C) (U W : C → Law (J → {v : V // v≠0}))
    (hU : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (mixture P U))
    (hW : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (mixture P W))
    (hC : Real.log (Fintype.card C)≤
      (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}))
    (hlog : 1000*Real.log 2≤Real.log (Fintype.card {v : V // v≠0})) :
    (∑ c,P.mass c*∑ j,GraphBound.passing B Subtype.val
      (push (U c) (fun w => w j)).mass (push (W c) (fun w => w j)).mass)/Fintype.card J≤31/50 := by
  let w : C × J → ℝ := fun z => P.mass z.1/Fintype.card J
  let p : C × J → {v : V // v≠0} → ℝ := fun z => (push (U z.1) (fun a => a z.2)).mass
  let q : C × J → {v : V // v≠0} → ℝ := fun z => (push (W z.1) (fun a => a z.2)).mass
  have hJ : (0:ℝ)<Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hw : ∀ z,0≤w z := fun z => div_nonneg (P.nonneg z.1) hJ.le
  have hw1 : ∑ z,w z=1 := by
    simp only [w,Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul,
      mul_div_cancel₀ _ hJ.ne',P.total]
  have hweight (F : C × J → ℝ) :
      (∑ z,w z*F z)=(∑ c,P.mass c*∑ j,F (c,j))/Fintype.card J := by
    simp only [w,Fintype.sum_prod_type,div_mul_eq_mul_div,←sum_div,mul_sum]
  have hp : (99/100:ℝ)*Real.log (Fintype.card {v : V // v≠0})≤
      ∑ z,w z*natEntropy (p z) := by
    rw [hweight,le_div_iff₀ hJ]
    have hh := conditional_entry_sum P U
    change _≤∑ c,P.mass c*∑ j,entropy (push (U c) (fun a => a j))
    calc
      _ = (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}) -
          (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}) := by ring
      _ ≤ entropy (mixture P U)-Real.log (Fintype.card C) := sub_le_sub hU hC
      _ ≤ _ := by simpa only [entropy,push_mass_canonical] using hh
  have hq : (99/100:ℝ)*Real.log (Fintype.card {v : V // v≠0})≤
      ∑ z,w z*natEntropy (q z) := by
    rw [hweight,le_div_iff₀ hJ]
    have hh := conditional_entry_sum P W
    change _≤∑ c,P.mass c*∑ j,entropy (push (W c) (fun a => a j))
    calc
      _ = (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}) -
          (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}) := by ring
      _ ≤ entropy (mixture P W)-Real.log (Fintype.card C) := sub_le_sub hW hC
      _ ≤ _ := by simpa only [entropy,push_mass_canonical] using hh
  have hh := GraphEntropy.graph_independent_finite B hB w p q hw hw1
    (fun z => (push (U z.1) (fun a => a z.2)).nonneg)
    (fun z => (push (W z.1) (fun a => a z.2)).nonneg)
    (fun z => (push (U z.1) (fun a => a z.2)).total)
    (fun z => (push (W z.1) (fun a => a z.2)).total) hp hq hlog
  rw [hweight] at hh
  exact hh
end SmoothObstruction.IndependentUpper

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset FiniteLaw
open scoped ENNReal
variable {X C A B : Type*} [MeasurableSpace X]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] [Nonempty B]

/-- Exact original-law finite observation formula for the weighted same-cell
pair experiment. Zero-mass cells vanish without renormalizing the experiment. -/
theorem rectangle_conditional (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (U : X → A) (hU : Measurable U)
    (V : X → B) (hV : Measurable V) (a : A) (b : B) :
    (law μ P).real ((U ⁻¹' {a}) ×ˢ (V ⁻¹' {b}))=
      ∑ c,(observed μ P hP).mass c*
        (conditionalObserved μ U hU P hP c).mass a*
        (conditionalObserved μ V hV P hP c).mass b := by
  let := law_probability μ P hP
  let E := (U ⁻¹' {a}) ×ˢ (V ⁻¹' {b})
  have hfin (c : C) : ((μ (P ⁻¹' {c}))⁻¹ • (cell μ P c).prod (cell μ P c)) E≠∞ := by
    apply ne_top_of_le_ne_top (measure_ne_top (law μ P) E)
    rw [law,Measure.finsetSum_apply]
    exact Finset.single_le_sum
      (f := fun cellIndex : C =>
        ((μ (P ⁻¹' {cellIndex}))⁻¹ • (cell μ P cellIndex).prod (cell μ P cellIndex)) E)
      (fun _ _ => bot_le) (mem_univ c)
  change ((law μ P) E).toReal=_
  rw [law,Measure.finsetSum_apply,ENNReal.toReal_sum (fun c _ => hfin c)]
  apply sum_congr rfl
  intro c _
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  rw [show E=(U ⁻¹' {a}) ×ˢ (V ⁻¹' {b}) from rfl,Measure.prod_prod,
    ENNReal.toReal_mul,cell,Measure.restrict_apply (hU (measurableSet_singleton a)),
    Measure.restrict_apply (hV (measurableSet_singleton b))]
  have hEU : (U ⁻¹' {a}) ∩ (P ⁻¹' {c})={x | P x=c ∧ U x=a} := by
    ext x; simp only [mem_inter_iff,Set.mem_preimage,mem_singleton_iff,mem_ofPred_eq,and_comm]
  have hEV : (V ⁻¹' {b}) ∩ (P ⁻¹' {c})={x | P x=c ∧ V x=b} := by
    ext x; simp only [mem_inter_iff,Set.mem_preimage,mem_singleton_iff,mem_ofPred_eq,and_comm]
  rw [hEU,hEV]
  change ((observed μ P hP).mass c)⁻¹*
    (μ.real {x | P x=c ∧ U x=a}*μ.real {x | P x=c ∧ V x=b})=_
  rw [←conditionalObserved_mass μ U hU P hP,←conditionalObserved_mass μ V hV P hP]
  by_cases hz : (observed μ P hP).mass c=0
  · simp only [hz,inv_zero,zero_mul]
  · field_simp

/-- The full pair label law, not merely a product assertion for individual
entries. It determines the single statistic used on both sides of the final
contradiction. -/
theorem observed_pair (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (U : X → A) (hU : Measurable U)
    (V : X → B) (hV : Measurable V) :
    letI := law_probability μ P hP
    ∀ a b,(observed (law μ P) (fun z : X × X => (U z.1,V z.2))
      ((hU.comp measurable_fst).prodMk (hV.comp measurable_snd))).mass (a,b)=
      ∑ c,(observed μ P hP).mass c*
        (conditionalObserved μ U hU P hP c).mass a*
        (conditionalObserved μ V hV P hP c).mass b := by
  intro a b
  change (law μ P).real {z : X × X | (U z.1,V z.2)=(a,b)}=_
  have he : {z : X × X | (U z.1,V z.2)=(a,b)}=(U ⁻¹' {a}) ×ˢ (V ⁻¹' {b}) := by
    ext z; simp only [Set.mem_ofPred_eq,Prod.mk.injEq,mem_prod,Set.mem_preimage,mem_singleton_iff]
  rw [he]
  exact rectangle_conditional μ P hP U hU V hV a b
end SmoothObstruction.PairLaw

namespace SmoothObstruction.PairUpper
open MeasureTheory Set Finset FiniteLaw
open scoped ENNReal
variable {X C J V : Type*} [MeasurableSpace X]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype J] [DecidableEq J] [Nonempty J]
  [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Nontrivial V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Nontrivial V] [Nonempty J] in
lemma product_push_expect {α β γ δ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] (P : Law α) (Q : Law β)
    (f : α → γ) (h : β → δ) (g : γ → δ → ℝ) :
    (∑ a,∑ b,P.mass a*Q.mass b*g (f a) (h b))=
      ∑ c,∑ d,(push P f).mass c*(push Q h).mass d*g c d := by
  simp only [mul_assoc,←mul_sum]
  simp only [expect_push_sum]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Nonempty J] [Nontrivial V] in
lemma product_statistic (B : LinearMap.BilinForm (ZMod 2) V)
    (P Q : Law (J → {v : V // v≠0})) :
    (∑ u,∑ v,P.mass u*Q.mass v*statistic B u v)=
    (∑ j,GraphBound.passing B Subtype.val
      (push P (fun u => u j)).mass (push Q (fun v => v j)).mass)/Fintype.card J := by
  simp only [statistic,←mul_div_assoc,←sum_div,mul_sum]
  congr 1
  conv_lhs => enter [2,u]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simpa only [GraphBound.passing, push_mass_canonical] using
    product_push_expect P Q (fun u => u j) (fun v => v j)
      (fun u v => if B u v=0 then 1 else 0)

omit [Nonempty J] in
/-- The passing statistic on the original pair law. This identifies exactly
its finite expectation with source (7.2), using the full conditional lists. -/
theorem expectation_formula (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V) :
    letI := PairLaw.law_probability μ P hP
    (∑ uv,(observed (PairLaw.law μ P) (fun z : X × X => (U z.1,W z.2))
      ((hU.comp measurable_fst).prodMk (hW.comp measurable_snd))).mass uv*
      statistic B uv.1 uv.2)=
    (∑ c,(observed μ P hP).mass c*∑ j,GraphBound.passing B Subtype.val
      (push (conditionalObserved μ U hU P hP c) (fun u => u j)).mass
      (push (conditionalObserved μ W hW P hP c) (fun v => v j)).mass)/Fintype.card J := by
  let := PairLaw.law_probability μ P hP
  have hm := PairLaw.observed_pair μ P hP U hU W hW
  simp only [Fintype.sum_prod_type,hm,sum_mul]
  conv_lhs => enter [2,u]; rw [sum_comm]
  rw [sum_comm]
  have hp (c : C) := product_statistic B (conditionalObserved μ U hU P hP c)
    (conditionalObserved μ W hW P hP c)
  simp only [mul_assoc,←mul_sum] at hp
  simp only [mul_assoc,←mul_sum,hp,←mul_div_assoc,←sum_div]

/-- Section 7's .62 upper bound for the actual same-cell measure. The two
entropy hypotheses refer to the original input probability, not the retained
or renormalized measure. -/
theorem expectation_upper (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hentU : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ U hU))
    (hentW : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ W hW))
    (hC : Real.log (Fintype.card C)≤
      (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}))
    (hlog : 1000*Real.log 2≤Real.log (Fintype.card {v : V // v≠0})) :
    letI := PairLaw.law_probability μ P hP
    (∑ uv,(observed (PairLaw.law μ P) (fun z : X × X => (U z.1,W z.2))
      ((hU.comp measurable_fst).prodMk (hW.comp measurable_snd))).mass uv*
      statistic B uv.1 uv.2)≤31/50 := by
  let := PairLaw.law_probability μ P hP
  exact (expectation_formula μ P hP U W hU hW B).trans_le (by
    rw [observed_mixture μ U hU P hP] at hentU
    rw [observed_mixture μ W hW P hP] at hentW
    exact IndependentUpper.list_graph_upper B hB (observed μ P hP)
      (conditionalObserved μ U hU P hP) (conditionalObserved μ W hW P hP)
      hentU hentW hC hlog)
end SmoothObstruction.PairUpper

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Recognition
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.WordConcatenation
open Finset
variable {A B : Type*} {m N : ℕ}

lemma mismatches_sum [DecidableEq A] {ι : Type*} [Fintype ι] (u v : ι → A) :
    mismatches u v = ∑ r, if u r=v r then (0 : ℕ) else 1 := by
  classical
  simp only [mismatches,card_eq_sum_ones,sum_filter,ne_eq,ite_not]

lemma mismatches_comp {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (u v : κ → A) :
    mismatches (u ∘ e) (v ∘ e) = mismatches u v := by
  classical
  simp only [mismatches_sum,Function.comp_apply]
  exact e.sum_comp (fun r => if u r=v r then (0 : ℕ) else 1)

lemma mismatches_concat (u : B → Fin m → A) (w v : Fin N → B) :
    mismatches (concat u w) (concat u v) = ∑ b, mismatches (u (w b)) (u (v b)) := by
  classical
  rw [←mismatches_comp pack]
  simp only [mismatches_sum,Function.comp_apply,concat_pack,Fintype.sum_prod_type]

lemma concat_distance {δ : ℝ} (u : B → Fin m → A)
    (hu : ∀ a b, a≠b → δ*m ≤ (mismatches (u a) (u b) : ℝ)) (w v : Fin N → B) :
    δ*m*mismatches w v ≤ (mismatches (concat u w) (concat u v) : ℝ) := by
  classical
  rw [mismatches_concat,Nat.cast_sum,mismatches_sum,Nat.cast_sum,mul_sum]
  apply sum_le_sum
  intro b _
  by_cases he : w b=v b
  · simp only [he,↓reduceIte,Nat.cast_zero,mul_zero]
    exact Nat.cast_nonneg _
  · simpa only [he,↓reduceIte,Nat.cast_one,mul_one] using hu (w b) (v b) he

lemma concat_at [NeZero m] [NeZero N] (u : B → Fin m → A) (w : Fin N → B)
    (k : Fin (m*N)) :
    concat u w k = u (w ⟨k.val/m,(Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr
      (by simpa only [Nat.mul_comm N m] using k.isLt)⟩)
      ⟨k.val%m,Nat.mod_lt _ (NeZero.pos m)⟩ := by
  have he : k=pack (⟨k.val/m,(Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr
      (by simpa only [Nat.mul_comm N m] using k.isLt)⟩,
      ⟨k.val%m,Nat.mod_lt _ (NeZero.pos m)⟩) := by
    apply Fin.ext
    simp only [pack_val]
    exact (Nat.div_add_mod' k.val m).symm
  calc
    _ = concat u w (pack (⟨k.val/m,_⟩,⟨k.val%m,_⟩)) := congrArg (concat u w) he
    _ = _ := concat_pack u w _ _

lemma joined_concat [NeZero m] [NeZero N] (u : B → Fin m → A)
    (w v : Fin N → B) (k : ℕ) :
    joined (concat u w) (concat u v) k =
      u (joined w v (k/m)) ⟨k%m,Nat.mod_lt _ (NeZero.pos m)⟩ := by
  have hiff : k/m < N ↔ k < m*N := by
    rw [Nat.div_lt_iff_lt_mul (NeZero.pos m),Nat.mul_comm N m]
  simp only [joined,hiff]
  split_ifs <;> rw [concat_at] <;> congr 2
  · exact Fin.ext (Nat.mod_mul_right_div_self k m N)
  · exact Nat.mod_mod_of_dvd k (dvd_mul_right m N)
  · exact Fin.ext (Nat.mod_mul_right_div_self k m N)
  · exact Nat.mod_mod_of_dvd k (dvd_mul_right m N)

/-- Every lower-length portion of a shifted concatenation is precisely a
splice of two successive lower words. This identity includes the join of
the two larger words and repeated constituents. -/
lemma splice_chunk [NeZero m] [NeZero N] (u : B → Fin m → A)
    (w v : Fin N → B) (t : Fin (m*N)) (b : Fin N) :
    (fun r => splice (concat u w) (concat u v) t (pack (b,r))) =
      splice (u (joined w v (t.val/m+b.val)))
        (u (joined w v (t.val/m+b.val+1)))
        ⟨t.val%m,Nat.mod_lt _ (NeZero.pos m)⟩ := by
  funext r
  simp only [splice,pack_val,joined_concat]
  have he : t.val+(b.val*m+r.val)=t.val%m+r.val+(t.val/m+b.val)*m := by
    have hh := Nat.div_add_mod' t.val m
    nlinarith
  simp only [he,Nat.add_mul_div_right _ _ (NeZero.pos m),Nat.add_mul_mod_self_right]
  conv_rhs => rw [joined]
  have hs := Nat.mod_lt t.val (NeZero.pos m)
  by_cases hh : t.val%m+r.val < m
  · rw [ite_eq_left hh,Nat.div_eq_of_lt hh]
    simp only [zero_add,Nat.mod_eq_of_lt hh]
  · have hd : (t.val%m+r.val)/m=1 := Nat.div_eq_of_lt_le (by omega)
        (by have := r.isLt; omega)
    rw [ite_eq_right hh,hd]
    congr 2
    omega

lemma mismatches_blocks (w v : Fin (m*N) → A) :
    mismatches w v = ∑ b, mismatches (fun r => w (pack (b,r))) (fun r => v (pack (b,r))) := by
  classical
  rw [←mismatches_comp pack]
  simp only [mismatches_sum,Function.comp_apply,Fintype.sum_prod_type]

lemma splice_aligned [NeZero m] [NeZero N] (u : B → Fin m → A)
    (w v : Fin N → B) (t : Fin (m*N)) (ht : t.val%m=0) :
    splice (concat u w) (concat u v) t =
      concat u (splice w v ⟨t.val/m,(Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr
        (by simpa only [Nat.mul_comm N m] using t.isLt)⟩) := by
  funext j
  obtain ⟨⟨b,r⟩,rfl⟩ := pack.surjective j
  have hh := congrFun (splice_chunk u w v t b) r
  have hz : (⟨t.val%m,Nat.mod_lt _ (NeZero.pos m)⟩ : Fin m)=0 := Fin.ext ht
  rw [hz,splice_zero] at hh
  simpa only [concat_pack,splice] using hh

variable {C : Type*}

theorem recognition_step [NeZero m] [NeZero N] (u : B → Fin m → A)
    (w : C → Fin N → B) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hu : Recognizes u δ) (hw : Recognizes w (1-ε)) :
    Recognizes (fun a => concat u (w a)) (δ*(1-ε)) := by
  intro a b c t ht
  by_cases hmod : t.val%m=0
  · rw [splice_aligned u (w a) (w b) t hmod]
    let t' : Fin N := ⟨t.val/m,(Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr
        (by simpa only [Nat.mul_comm N m] using t.isLt)⟩
    have ht' : t'≠0 ∨ a≠c := by
      rcases ht with ht|ht
      · left
        intro hz
        have hv := congrArg Fin.val hz
        dsimp [t'] at hv
        have hd := Nat.div_add_mod' t.val m
        rw [hv,hmod,zero_mul,zero_add] at hd
        exact ht (Fin.ext hd.symm)
      · exact Or.inr ht
    have hh := hw a b c t' ht'
    have hb := concat_distance (δ:=δ) u
      (fun x y hxy => by simpa only [splice_zero] using hu x x y 0 (Or.inr hxy))
      (splice (w a) (w b) t') (w c)
    have he := mul_le_mul_of_nonneg_left hh (mul_nonneg hδ (Nat.cast_nonneg m))
    push_cast
    dsimp [t'] at hb
    nlinarith
  · rw [mismatches_blocks,Nat.cast_sum]
    have hb (j : Fin N) : δ*m ≤
        (mismatches (fun r => splice (concat u (w a)) (concat u (w b)) t (pack (j,r)))
          (fun r => concat u (w c) (pack (j,r))) : ℝ) := by
      rw [splice_chunk]
      simp only [concat_pack]
      apply hu
      left
      intro hh
      exact hmod (congrArg Fin.val hh)
    have hs := sum_le_sum (fun j (_hj : j ∈ (univ : Finset (Fin N))) => hb j)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    push_cast
    have hn : 0 ≤ δ*(m:ℝ)*N := by positivity
    nlinarith

end SmoothObstruction.WordConcatenation

namespace SmoothObstruction.WordHierarchy
open WordConcatenation WordParameters WordStep Finset

lemma splice_first {α : Type*} {M n : ℕ} [NeZero n] (w : Fin M → Fin n → α)
    (a b : Fin M) (t r : Fin n) :
    splice (w a) (w b) t r =
      w (ShiftComparisons.first a b t r).1 (ShiftComparisons.first a b t r).2 := by
  simp only [splice,joined,ShiftComparisons.first,Nat.add_comm t.val r.val]
  split_ifs <;> rfl

lemma count_complement {α : Type*} [Fintype α] [DecidableEq α]
    {M n : ℕ} [NeZero n] (w : Fin M → Fin n → α) (a b c : Fin M) (t : Fin n) :
    mismatches (splice (w a) (w b) t) (w c)+ShiftComparisons.matchCount w a b c t=n := by
  simp only [mismatches_sum,ShiftComparisons.matchCount,card_eq_sum_ones,sum_filter,
    ←sum_add_distrib]
  calc
    _ = ∑ _r : Fin n, 1 := by
      apply sum_congr rfl
      intro r _
      rw [splice_first]
      split_ifs <;> rfl
    _ = n := by simp

lemma stage_recognizes (i : ℕ) : Recognizes (stage i).word (1-epsilon i) := by
  intro a b c t ht
  let a' := (Fintype.equivFin (A (i+1))) a
  let b' := (Fintype.equivFin (A (i+1))) b
  let c' := (Fintype.equivFin (A (i+1))) c
  have hsep := (stage i).separated a' b' c' t (ht.imp id (fun h h' => h
    ((Fintype.equivFin (A (i+1))).injective h')))
  have hlt : (ShiftComparisons.matchCount (stage i).w a' b' c' t : ℝ) <
      epsilon i*N (S i) := (Nat.lt_ceil.mp hsep)
  have hc := count_complement (stage i).w a' b' c' t
  have hcr : (mismatches (splice ((stage i).word a) ((stage i).word b) t)
      ((stage i).word c) : ℝ)+ShiftComparisons.matchCount (stage i).w a' b' c' t = N (S i) := by
    exact_mod_cast (hc.trans (q_mul_H (S i)))
  have hg : (groupLength i : ℝ) = N (S i) := congrArg Nat.cast (q_mul_H (S i))
  calc
    (1-epsilon i)*(groupLength i : ℝ)=(1-epsilon i)*(N (S i) : ℝ) := by rw [hg]
    _ ≤ _ := by nlinarith only [hcr,hlt]

lemma recognizes_reindex_length {α β : Type*} {m n : ℕ} [NeZero m] [NeZero n]
    (h : m=n) (w : β → Fin m → α) {δ : ℝ} (hw : Recognizes w δ) :
    Recognizes (fun a j => w a ((finCongr h).symm j)) δ := by
  subst n
  simpa only [finCongr_refl,Equiv.refl_symm,Equiv.refl_apply] using hw

lemma children_recognizes (i : ℕ) : Recognizes (children i) (1-epsilon i) :=
  recognizes_reindex_length (q_mul_H (S i)) (stage i).word (stage_recognizes i)

lemma delta_succ (i : ℕ) : delta (i+1)=delta i*(1-epsilon i) := by
  simp [delta,prod_range_succ]
lemma delta_nonneg (i : ℕ) : 0 ≤ delta i := prod_nonneg (fun j _ =>
  sub_nonneg.mpr (epsilon_le_one j))

lemma epsilon_sum (i : ℕ) : (∑ j ∈ range i,epsilon j)=1/4-2*epsilon i := by
  induction i with
  | zero => norm_num [epsilon]
  | succ i ih => rw [sum_range_succ,ih,epsilon_succ]; ring

lemma delta_lower (i : ℕ) : 3/4 ≤ delta i := by
  have hlo : 1-(∑ j ∈ range i,epsilon j) ≤ delta i := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [sum_range_succ,delta_succ]
      have hsum : 0 ≤ ∑ j ∈ range i,epsilon j := sum_nonneg (fun j _ => (epsilon_pos j).le)
      have hh := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr (epsilon_le_one i))
      nlinarith [mul_nonneg hsum (epsilon_pos i).le]
  rw [epsilon_sum] at hlo
  have hh := epsilon_pos i
  linarith

/-- Source recognition at every symbol offset for the actual chosen words,
not only for the constituent-label lists. -/
theorem word_recognizes (i : ℕ) : Recognizes (word i) (delta i) := by
  induction i with
  | zero =>
    intro a b c t ht
    have hz : t=0 := by
      apply Fin.ext
      have hh := t.isLt
      change t.val < 1 at hh
      simp only [Fin.val_zero]
      omega
    subst t
    have hne : a≠c := ht.resolve_left (not_not.mpr rfl)
    rw [splice_zero]
    classical
    have hc : mismatches (word 0 a) (word 0 c)=1 := by
      rw [mismatches_sum]
      simp only [word,hne,ite_false]
      change (∑ _r : Fin 1,(1:ℕ))=1
      decide
    rw [hc]
    norm_num only [delta_zero,length,Nat.cast_one,mul_one]
  | succ i ih =>
    rw [delta_succ]
    exact recognition_step (word i) (children i) (delta_nonneg i) (epsilon_pos i).le ih
      (children_recognizes i)

/-- The uniform fixed-alphabet constant is at least 3/4, hence strictly
positive independently of the level and the three source labels. -/
theorem uniform_recognition (i : ℕ) : Recognizes (word i) (3/4) := by
  intro a b c t ht
  exact (mul_le_mul_of_nonneg_right (delta_lower i) (Nat.cast_nonneg _)).trans
    (word_recognizes i a b c t ht)

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.RecognitionWindow
open Finset WordConcatenation
variable {A B : Type*} {m : ℕ} [NeZero m]

/-- Every arbitrary length-m window is a splice of the two actual adjacent
legal words. This includes negative starts and windows beyond the observed
half-name. -/
theorem window_splice (w : B → Fin m → A) (u : ℤ → A)
    (p : ZMod m) (hu : LegalAt w u p) (t : ℤ) :
    ∃ a b, ∃ o : Fin m, (o.val : ZMod m)=p+(t : ZMod m) ∧
      (fun r : Fin m => u (t+r.val))=splice (w a) (w b) o := by
  let q : ZMod m := p+(t : ZMod m)
  let o : Fin m := ⟨q.val,q.val_lt⟩
  let s : ℤ := t-o.val
  have ho : (o.val : ZMod m)=q := ZMod.natCast_zmod_val q
  have hs : (s : ZMod m)=-p := by
    change ((t-(o.val:ℤ) : ℤ) : ZMod m)=-p
    rw [Int.cast_sub,Int.cast_natCast,ho]
    dsimp only [q]
    ring
  obtain ⟨a,ha⟩ := hu s hs
  obtain ⟨b,hb⟩ := hu (s+m) (by
    rw [Int.cast_add,Int.cast_natCast,ZMod.natCast_self,add_zero,hs])
  refine ⟨a,b,o,ho,?_⟩
  funext r
  simp only [splice,joined]
  by_cases hr : o.val+r.val < m
  · rw [ite_eq_left hr,←ha]
    congr 1
    change t+(r.val:ℤ)=s+(((o.val+r.val)%m:ℕ):ℤ)
    rw [Nat.mod_eq_of_lt hr]
    dsimp only [s]
    push_cast
    ring
  · rw [ite_eq_right hr,←hb]
    have hmod : (o.val+r.val)%m=o.val+r.val-m := by
      have ho' := o.isLt
      have hr' := r.isLt
      rw [Nat.mod_eq_sub_mod (by omega : m≤o.val+r.val),Nat.mod_eq_of_lt (by omega)]
    change u (t+(r.val:ℤ))=u (s+(m:ℤ)+(((o.val+r.val)%m:ℕ):ℤ))
    rw [hmod,Nat.cast_sub (by omega : m≤o.val+r.val)]
    dsimp only [s]
    congr 1
    push_cast
    ring

lemma mismatches_symm {ι : Type*} [Fintype ι] (u v : ι → A) :
    mismatches u v=mismatches v u := by
  classical
  simp only [mismatches,ne_comm]

/-- Recognition forces a fixed cost on every aligned block whenever the
other sequence has a different phase. -/
lemma phase_block_cost (w : B → Fin m → A) {δ : ℝ} (hw : Recognizes w δ)
    (u v : ℤ → A) (p q : ZMod m) (hu : LegalAt w u p) (hv : LegalAt w v q)
    (hpq : p≠q) (t : ℤ) (ht : (t : ZMod m)=-p) :
    δ*m≤(mismatches (fun r : Fin m => u (t+r.val))
      (fun r : Fin m => v (t+r.val)) : ℝ) := by
  obtain ⟨c,hc⟩ := hu t ht
  obtain ⟨a,b,o,ho,hv'⟩ := window_splice w v q hv t
  have ho0 : o≠0 := by
    intro hz
    have hq : q-p=0 := by
      simpa only [hz,Fin.val_zero,Nat.cast_zero,ht,←sub_eq_add_neg] using ho.symm
    exact hpq (sub_eq_zero.mp hq).symm
  have hu' : (fun r : Fin m => u (t+r.val))=w c := funext hc
  rw [hu',hv',mismatches_symm]
  exact hw a b c o (Or.inl ho0)

lemma mismatches_injection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (u v : κ → A) :
    mismatches (u ∘ e) (v ∘ e)≤ mismatches u v := by
  classical
  simp only [mismatches_sum,Function.comp_apply]
  calc
    _ = ∑ k∈univ.map e,if u k=v k then (0:ℕ) else 1 := (sum_map _ _ _).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

/-- The whole-window mismatch count dominates the sum of all complete
aligned block counts. No stochastic independence is involved. -/
lemma complete_blocks_le (D a : ℕ) (ha : a < m) (u v : ℤ → A) (t : ℤ) :
    (∑ j : Fin (D-1),mismatches
      (fun r : Fin m => u (t+(a+j.val*m+r.val : ℕ)))
      (fun r : Fin m => v (t+(a+j.val*m+r.val : ℕ))))≤
    mismatches (fun r : Fin (D*m) => u (t+r.val)) (fun r : Fin (D*m) => v (t+r.val)) := by
  have hh := mismatches_injection (blocksEmbedding D a ha)
    (fun r : Fin (D*m) => u (t+r.val)) (fun r : Fin (D*m) => v (t+r.val))
  change mismatches
    (fun jr : Fin (D-1) × Fin m => u (t+(a+jr.1.val*m+jr.2.val : ℕ)))
    (fun jr : Fin (D-1) × Fin m => v (t+(a+jr.1.val*m+jr.2.val : ℕ)))≤
      mismatches (fun r : Fin (D*m) => u (t+r.val)) (fun r : Fin (D*m) => v (t+r.val)) at hh
  classical
  simpa only [mismatches_sum,Fintype.sum_prod_type] using hh

/-- Small mismatch on one half-name recovers the ORIGINAL phase. It does
not choose or shift entry indices after the geometric switch. -/
theorem phase_recovery (w : B → Fin m → A) {δ : ℝ} (_hδ : 0<δ)
    (hw : Recognizes w δ) (u v : ℤ → A) (p q : ZMod m)
    (hu : LegalAt w u p) (hv : LegalAt w v q)
    (D : ℕ) (hD : 2≤D) (a : ℕ) (ha : a < m) (haP : (a : ZMod m)=-p)
    (hclose : (mismatches (fun r : Fin (D*m) => u r.val)
      (fun r : Fin (D*m) => v r.val) : ℝ)<δ*(D*m)/100) : p=q := by
  by_contra hpq
  have hc (j : Fin (D-1)) : δ*m≤(mismatches
      (fun r : Fin m => u ((a+j.val*m+r.val : ℕ):ℤ))
      (fun r : Fin m => v ((a+j.val*m+r.val : ℕ):ℤ)) : ℝ) := by
    have ht : (((a+j.val*m : ℕ):ℤ):ZMod m)=-p := by
      simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,
        mul_zero,add_zero,haP]
    have hh := phase_block_cost w hw u v p q hu hv hpq ((a+j.val*m : ℕ):ℤ) ht
    simpa only [Nat.cast_add,Nat.cast_mul] using hh
  have hb := complete_blocks_le D a ha u v 0
  have hbr : (∑ j : Fin (D-1),(mismatches
      (fun r : Fin m => u ((a+j.val*m+r.val : ℕ):ℤ))
      (fun r : Fin m => v ((a+j.val*m+r.val : ℕ):ℤ)) : ℝ))≤
      (mismatches (fun r : Fin (D*m) => u r.val) (fun r : Fin (D*m) => v r.val) : ℝ) := by
    exact_mod_cast (by simpa only [zero_add] using hb)
  have hsum := (sum_le_sum (fun j (_ : j∈univ) => hc j)).trans hbr
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_sub (by omega : 1≤D),
    Nat.cast_one] at hsum
  have hm : (0:ℝ) < m := by exact_mod_cast NeZero.pos m
  have hDr : (2:ℝ)≤D := by exact_mod_cast hD
  have hh : δ*(D*m)/2≤(D-1)*(δ*m) := by nlinarith
  nlinarith
end SmoothObstruction.RecognitionWindow

namespace SmoothObstruction.RecognitionWindow
open Finset WordConcatenation
variable {A B : Type*} {m : ℕ} [NeZero m]

lemma distinct_word_cost (w : B → Fin m → A) {δ : ℝ} (hw : Recognizes w δ)
    {a b : B} (hab : a≠b) : δ*m≤(mismatches (w a) (w b):ℝ) := by
  have hh := hw a a b 0 (Or.inr hab)
  simpa only [splice_zero] using hh

/-- Once the original phases have been recovered, the original entry labels
cannot disagree with the switched labels at many positions. No new alignment
or reindexing of entries is permitted. -/
theorem entry_recovery (w : B → Fin m → A) {δ : ℝ} (hδ : 0<δ)
    (hw : Recognizes w δ) (u v : ℤ → A) (D a : ℕ) (ha : a < m) (t : ℤ)
    (U V : Fin (D-1) → B)
    (hU : ∀ j r,u (t+(a+j.val*m+r.val:ℕ))=w (U j) r)
    (hV : ∀ j r,v (t+(a+j.val*m+r.val:ℕ))=w (V j) r)
    (hclose : (mismatches (fun r : Fin (D*m) => u (t+r.val))
      (fun r : Fin (D*m) => v (t+r.val)):ℝ)<δ*(D*m)/100) :
    (mismatches U V:ℝ)<D/100 := by
  classical
  have hpoint (j : Fin (D-1)) :
      (if U j=V j then (0:ℝ) else 1)*(δ*m)≤(mismatches
        (fun r : Fin m => u (t+(a+j.val*m+r.val:ℕ)))
        (fun r : Fin m => v (t+(a+j.val*m+r.val:ℕ))):ℝ) := by
    by_cases hj : U j=V j
    · simp only [hj,ite_true,zero_mul]
      exact Nat.cast_nonneg _
    · rw [ite_eq_right hj,one_mul,show (fun r : Fin m => u (t+(a+j.val*m+r.val:ℕ)))=w (U j) by
        funext r; exact hU j r,
        show (fun r : Fin m => v (t+(a+j.val*m+r.val:ℕ)))=w (V j) by
        funext r; exact hV j r]
      exact distinct_word_cost w hw hj
  have hs := sum_le_sum (fun j (_ : j∈univ) => hpoint j)
  have hsum : (mismatches U V:ℝ)*(δ*m)≤(mismatches
      (fun r : Fin (D*m) => u (t+r.val)) (fun r : Fin (D*m) => v (t+r.val)):ℝ) := by
    calc
      _ = ∑ j : Fin (D-1),(if U j=V j then (0:ℝ) else 1)*(δ*m) := by
        rw [←sum_mul,mismatches_sum]
        simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
      _ ≤ _ := hs
      _ ≤ _ := by exact_mod_cast complete_blocks_le D a ha u v t
  have hm : (0:ℝ) < m := by exact_mod_cast NeZero.pos m
  have hp : 0<δ*m := mul_pos hδ hm
  apply (mul_lt_mul_iff_left₀ hp).mp
  calc
    (mismatches U V:ℝ)*(δ*m) ≤ _ := hsum
    _ < _ := hclose
    _ = (D/100)*(δ*m) := by ring

/-- Pure entry pairing: two small label-error sets remove at most their sum
from a graph window. In particular the source constants give the literal .96
passing bound in the unchanged index order. -/
theorem paired_graph_bound {D : ℕ} (hD : 2≤D) (R : B → B → Prop)
    [DecidableRel R] (U V Z W : Fin (D-1) → B)
    (hgraph : ∀ j,R (Z j) (W j))
    (hU : (mismatches U Z:ℝ)<D/100) (hV : (mismatches V W:ℝ)<D/100) :
    (24/25:ℝ)≤(∑ j,if R (U j) (V j) then (1:ℝ) else 0)/(D-1) := by
  classical
  have hj (j : Fin (D-1)) :
      (1:ℝ)≤(if R (U j) (V j) then 1 else 0)+
        (if U j=Z j then 0 else 1)+(if V j=W j then 0 else 1) := by
    by_cases h₁ : U j=Z j
    · by_cases h₂ : V j=W j
      · simp only [h₁,h₂,hgraph j,ite_true]; norm_num
      · simp only [h₁,h₂,ite_true,ite_false]; split_ifs <;> norm_num
    · simp only [h₁,ite_false]; split_ifs <;> norm_num
  have hs := sum_le_sum (fun j (_ : j∈univ) => hj j)
  have he (L K : Fin (D-1) → B) :
      (∑ j,if L j=K j then (0:ℝ) else 1)=(mismatches L K:ℝ) := by
    rw [mismatches_sum]
    simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
  simp only [sum_add_distrib,he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one,Nat.cast_sub (by omega : 1≤D),Nat.cast_one] at hs
  have hDr : (2:ℝ)≤D := by exact_mod_cast hD
  rw [le_div_iff₀ (by linarith : (0:ℝ)<D-1)]
  linarith
end SmoothObstruction.RecognitionWindow

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw

lemma actual_legal (i : ℕ) (x : Extension) :
    RecognitionWindow.LegalAt (word i) x.val.1 (phase i x) := by
  intro t ht
  obtain ⟨a,ha⟩ := (x.property i).2 t ht
  exact ⟨a,fun r => (congrFun ha r).symm⟩

lemma actual_iterate_symbol (x : Extension) (j : ℕ) (t : ℤ) :
    ((T^[j] x).val).1 t=x.val.1 (t+j) := by
  rw [iterate_coe,PhaseDynamics.iterate_symbol]

lemma advance_phase (i : ℕ) (x : Extension) : phase i (advance i x)=0 :=
  Alignment.align_phase T (phase i) (fun _ => rfl) x

lemma firstList_word (i D : ℕ) (x : Extension) (j : Fin (D-1)) (r : Fin (length 40000 i)) :
    x.val.1 (((-phase i x).val+j.val*length 40000 i+r.val:ℕ):ℤ)=
      word i (firstList i D x j) r := by
  let a := (-phase i x).val
  have hp : phase i ((T^[j.val*length 40000 i]) (advance i x))=0 := by
    rw [phase_iterate,advance_phase,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero]
  have hh := congrFun (word_label i ((T^[j.val*length 40000 i]) (advance i x))) r
  change word i (firstList i D x j) r=
    ((T^[j.val*length 40000 i] (advance i x)).val).1 (-(phase i ((T^[j.val*length 40000 i]) (advance i x))).val+(r.val:ℤ)) at hh
  rw [hp,ZMod.val_zero,Nat.cast_zero,neg_zero,zero_add,actual_iterate_symbol] at hh
  change word i (firstList i D x j) r=((T^[a] x).val).1 ((r.val:ℤ)+(j.val*length 40000 i:ℕ)) at hh
  rw [actual_iterate_symbol] at hh
  rw [hh]
  dsimp only [a]
  push_cast
  ring_nf

/-- On the actual extension, source symbol agreement recovers both the true
phase and all but D/100 of the original ordered labels. -/
theorem actual_recovery (i D : ℕ) (hD : 2≤D) (x z : Extension)
    (hclose : (mismatches (fun r : Fin (D*length 40000 i) => x.val.1 r.val)
      (fun r : Fin (D*length 40000 i) => z.val.1 r.val):ℝ)<
        (3/4:ℝ)*(D*length 40000 i)/100) :
    phase i x=phase i z ∧ (mismatches (firstList i D x) (firstList i D z):ℝ)<D/100 := by
  have hp := RecognitionWindow.phase_recovery (word i) (by norm_num : (0:ℝ)<3/4)
    (uniform_recognition i) x.val.1 z.val.1 (phase i x) (phase i z)
    (actual_legal i x) (actual_legal i z) D hD (-phase i x).val
    (ZMod.val_lt _) (ZMod.natCast_zmod_val _) hclose
  refine ⟨hp,?_⟩
  apply RecognitionWindow.entry_recovery (word i) (by norm_num : (0:ℝ)<3/4)
    (uniform_recognition i) x.val.1 z.val.1 D (-phase i x).val (ZMod.val_lt _) 0
    (firstList i D x) (firstList i D z)
  · intro j r
    simpa only [zero_add] using firstList_word i D x j r
  · intro j r
    simpa only [zero_add,hp] using firstList_word i D z j r
  · simpa only [zero_add] using hclose

lemma measurable_form_pair (i : ℕ) :
    Measurable (fun p : A i × A i => WordAlphabet.form (S i) p.1.val p.2.val) :=
  measurable_of_countable _

lemma measurable_graphWindows_at (i k : ℕ) (j : Fin (2^k-1)) :
    MeasurableSet {x : Extension | WordAlphabet.form (S i)
      (label i ((T^[j.val*length 40000 i]) x)).val
      (label i ((T^[(j.val+2^k)*length 40000 i]) x)).val=0} := by
  have hl : Measurable (fun x : Extension => label i ((T^[j.val*length 40000 i]) x)) :=
    (measurable_label i).comp (measurable_T.iterate _)
  have hr : Measurable (fun x : Extension => label i ((T^[(j.val+2^k)*length 40000 i]) x)) :=
    (measurable_label i).comp (measurable_T.iterate _)
  exact ((measurable_form_pair i).comp (hl.prodMk hr)) (measurableSet_singleton (0 : ZMod 2))

lemma measurable_graphWindows (i k : ℕ) : MeasurableSet {x | graphWindows i k x} := by
  change MeasurableSet {x | ∀ j : Fin (2^k-1), WordAlphabet.form (S i)
      (label i ((T^[j.val*length 40000 i]) x)).val
      (label i ((T^[(j.val+2^k)*length 40000 i]) x)).val=0}
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (measurable_graphWindows_at i k)

/-- Actual graph-event probability under the stationary law, obtained by
pushing its first-boundary advance, never by assuming uniform parents. -/
theorem stationary_graph_probability (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i k : ℕ) (hk : k≤K (S i)/8) :
    1-((2*2^k-2:ℕ):ℝ)/H (S i)≤
      μ.real {x | graphWindows i k (advance i x)} := by
  have hh := boundary_graph_probability μ hT i k hk
  rw [←advance_map μ hT i] at hh
  simpa only [Measure.real,Measure.map_apply (measurable_advance i) (measurable_graphWindows i k),
    Set.preimage_ofPred_eq] using hh

end SmoothObstruction.WordHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SymbolCores
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.SymbolCores
open MeasureTheory Set
open scoped ENNReal NNReal
variable {M A : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- A finite measurable observation is uniformly stable at nearby points of
one compact core, losing arbitrarily little of the original probability. -/
theorem compact_core (μ : Measure M) [IsFiniteMeasure μ]
    (f : M → A) (hf : Measurable f) {κ : ℝ} (hκ : 0<κ) :
    ∃ (C : Set M) (δ : ℝ≥0), IsCompact C ∧ μ Cᶜ≤ENNReal.ofReal κ ∧
      0<δ ∧ ∀ x∈C,∀ y∈C,edist x y<(δ : ℝ≥0∞) → f x=f y := by
  classical
  let ε := ENNReal.ofReal κ/(Fintype.card A : ℝ≥0∞)
  have he : ε≠0 := by
    dsimp [ε]
    exact ne_of_gt (ENNReal.div_pos (by positivity) (by finiteness))
  have hc : (Fintype.card A : ℝ≥0∞)≠0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hex (a : A) := (hf (measurableSet_singleton a)).exists_isCompact_sdiff_lt
    (measure_ne_top μ _) he
  choose K hK hKc hKm using hex
  let C := ⋃ a,K a
  have hCc : IsCompact C := isCompact_iUnion hKc
  have hmass : μ Cᶜ≤ENNReal.ofReal κ := by
    have hsub : Cᶜ ⊆ ⋃ a, (f ⁻¹' {a}) \ K a := by
      intro x hx
      refine mem_iUnion.mpr ⟨f x,?_,?_⟩
      · rfl
      · intro hk
        exact hx (mem_iUnion.mpr ⟨f x,hk⟩)
    calc
      μ Cᶜ ≤ μ (⋃ a, (f ⁻¹' {a}) \ K a) := measure_mono hsub
      _ ≤ ∑' a,μ ((f ⁻¹' {a}) \ K a) := measure_iUnion_le _
      _ ≤ ∑' _ : A,ε := ENNReal.tsum_le_tsum (fun a => (hKm a).le)
      _ = ENNReal.ofReal κ := by
        rw [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        dsimp [ε]
        rw [ENNReal.mul_div_cancel hc (by finiteness)]
  have hsep (p : A × A) : ∃ r : ℝ≥0, 0 < r ∧ ∀ x∈K p.1,∀ y∈K p.2,
      p.1≠p.2 → (r : ℝ≥0∞)<edist x y := by
    by_cases hh : p.1=p.2
    · exact ⟨1,by norm_num,fun _ _ _ _ hn => (hn hh).elim⟩
    have hd : Disjoint (K p.1) (K p.2) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hh ((hK _ hx).symm.trans (hK _ hy))
    obtain ⟨r,hr,hrr⟩ := Metric.exists_pos_forall_lt_edist (hKc p.1) (hKc p.2).isClosed hd
    exact ⟨r,hr,fun x hx y hy _ => hrr x hx y hy⟩
  choose r hr hrr using hsep
  let δ := Finset.univ.inf' Finset.univ_nonempty r
  refine ⟨C,δ,hCc,hmass,?_,?_⟩
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun p _ => hr p)
  · intro x hx y hy hxy
    obtain ⟨a,ha⟩ := mem_iUnion.mp hx
    obtain ⟨b,hb⟩ := mem_iUnion.mp hy
    by_contra hn
    have hab : a≠b := by
      intro h
      exact hn ((hK _ ha).trans (h.trans (hK _ hb).symm))
    have hd : δ ≤ r (a,b) := Finset.inf'_le _ (Finset.mem_univ _)
    have hd' : (δ : ℝ≥0∞) ≤ r (a,b) := by exact_mod_cast hd
    exact (not_lt_of_ge hd') (hrr (a,b) x ha y hb hab |>.trans hxy)

end SmoothObstruction.SymbolCores

namespace SmoothObstruction.SymbolMass
open MeasureTheory Set
open scoped ENNReal NNReal
variable {Ω M A : Type*} [MeasurableSpace Ω] [MetricSpace M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace A]

omit [MeasurableSpace A] in
/-- The per-time mismatch estimate in the original, unnormalized retained
law. Only its actual dominated marginals are used. -/
theorem mismatch_mass (σ : Measure Ω) (μ : Measure M)
    (f : M → A) (C : Set M) (hC : IsClosed C) {δ : ℝ≥0}
    (hcore : ∀ x∈C,∀ y∈C,edist x y<(δ : ℝ≥0∞) → f x=f y)
    (u v : Ω → M) (hu : Measurable u) (hv : Measurable v)
    (a b : ℝ≥0∞) (hU : σ.map u≤a•μ) (hV : σ.map v≤b•μ)
    (hdist : ∀ᵐ ω ∂σ,edist (u ω) (v ω)<(δ : ℝ≥0∞)) :
    σ {ω | f (u ω)≠f (v ω)}≤(a+b)*μ Cᶜ := by
  have hs : (fun ω => ω∈{ω | f (u ω)≠f (v ω)}) ≤ᵐ[σ] (fun ω => ω∈(u ⁻¹' Cᶜ ∪ v ⁻¹' Cᶜ)) := by
    filter_upwards [hdist] with ω hω
    intro hbad
    change u ω∉C ∨ v ω∉C
    by_contra hh
    push Not at hh
    exact hbad (hcore _ hh.1 _ hh.2 hω)
  have hUc := Measure.le_iff.mp hU Cᶜ hC.measurableSet.compl
  have hVc := Measure.le_iff.mp hV Cᶜ hC.measurableSet.compl
  rw [Measure.map_apply hu hC.measurableSet.compl,Measure.smul_apply,smul_eq_mul] at hUc
  rw [Measure.map_apply hv hC.measurableSet.compl,Measure.smul_apply,smul_eq_mul] at hVc
  calc
    σ {ω | f (u ω)≠f (v ω)} ≤ σ (u ⁻¹' Cᶜ ∪ v ⁻¹' Cᶜ) := measure_mono_ae hs
    _ ≤ σ (u ⁻¹' Cᶜ)+σ (v ⁻¹' Cᶜ) := measure_union_le _ _
    _ ≤ a*μ Cᶜ+b*μ Cᶜ := add_le_add hUc hVc
    _ = (a+b)*μ Cᶜ := (add_mul _ _ _).symm

omit [MetricSpace M] [BorelSpace M] in
/-- Invariance transports output domination to every observation time. -/
theorem transported_domination (σ : Measure Ω) (μ : Measure M)
    (z : Ω → M) (hz : Measurable z) (S : M → M)
    (hS : MeasurePreserving S μ μ) (a : ℝ≥0∞) (hzle : σ.map z≤a•μ) :
    σ.map (S ∘ z)≤a•μ := by
  rw [←Measure.map_map hS.measurable hz]
  have hh := Measure.map_mono hzle hS.measurable
  rwa [Measure.map_smul a,hS.map_eq] at hh

end SmoothObstruction.SymbolMass

namespace SmoothObstruction.SymbolMass
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_errors (N : ℕ) (bad : Fin N → Set Ω)
    (hb : ∀ t,MeasurableSet (bad t)) : Measurable (errors N bad) := by
  exact Finset.measurable_sum _ (fun t _ => measurable_const.indicator (hb t))

/-- The finite-time Markov bound. The factor N cancels; no mixing in time
and no renormalized law is required. -/
theorem fraction_bad (σ : Measure Ω) (N : ℕ) (hN : 0<N)
    (bad : Fin N → Set Ω) (hb : ∀ t,MeasurableSet (bad t))
    (ε θ : ℝ≥0∞) (hθ : θ≠0) (hθt : θ≠∞)
    (hm : ∀ t,σ (bad t)≤ε) :
    σ {ω | (N:ℝ≥0∞)*θ≤errors N bad ω}≤ε/θ := by
  have hNz : (N:ℝ≥0∞)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNt : (N:ℝ≥0∞)≠∞ := ENNReal.natCast_ne_top N
  have hi : (∫⁻ ω,errors N bad ω ∂σ)≤(N:ℝ≥0∞)*ε := by
    change (∫⁻ ω,∑ t : Fin N, (bad t).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂σ)≤_
    rw [lintegral_finsetSum _ (fun t _ => measurable_const.indicator (hb t))]
    calc
      ∑ t : Fin N, (∫⁻ ω,(bad t).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂σ)
        ≤ ∑ t : Fin N,σ (bad t) := Finset.sum_le_sum (fun t _ => lintegral_indicator_one_le (bad t))
      _ ≤ ∑ _t : Fin N, ε := Finset.sum_le_sum (fun t _ => hm t)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ (∫⁻ ω,errors N bad ω ∂σ)/((N:ℝ≥0∞)*θ) :=
      meas_ge_le_lintegral_div (measurable_errors N bad hb).aemeasurable
        (mul_ne_zero hNz hθ) (ENNReal.mul_ne_top hNt hθt)
    _ ≤ ((N:ℝ≥0∞)*ε)/((N:ℝ≥0∞)*θ) := by gcongr
    _ = ε/θ := ENNReal.mul_div_mul_left ε θ hNz hNt

/-- Both half-names lose at most twice the one-half Markov bound. -/
theorem two_halves_bad (σ : Measure Ω) (N : ℕ) (hN : 0<N)
    (bad₁ bad₂ : Fin N → Set Ω)
    (hb₁ : ∀ t,MeasurableSet (bad₁ t)) (hb₂ : ∀ t,MeasurableSet (bad₂ t))
    (ε θ : ℝ≥0∞) (hθ : θ≠0) (hθt : θ≠∞)
    (hm₁ : ∀ t,σ (bad₁ t)≤ε) (hm₂ : ∀ t,σ (bad₂ t)≤ε) :
    σ ({ω | (N:ℝ≥0∞)*θ≤errors N bad₁ ω} ∪
      {ω | (N:ℝ≥0∞)*θ≤errors N bad₂ ω})≤2*(ε/θ) := by
  calc
    _ ≤ σ {ω | (N:ℝ≥0∞)*θ≤errors N bad₁ ω}+
        σ {ω | (N:ℝ≥0∞)*θ≤errors N bad₂ ω} := measure_union_le _ _
    _ ≤ ε/θ+ε/θ := add_le_add (fraction_bad σ N hN bad₁ hb₁ ε θ hθ hθt hm₁)
      (fraction_bad σ N hN bad₂ hb₂ ε θ hθ hθt hm₂)
    _ = _ := (two_mul _).symm
end SmoothObstruction.SymbolMass

namespace SmoothObstruction.SymbolMass
open MeasureTheory Set Filter Topology WordConcatenation
open scoped ENNReal
variable {M A : Type} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma errors_eq_mismatches (N : ℕ) (u v : Fin N → M×M → A) (p : M×M) :
    errors N (fun t => {p | u t p≠v t p}) p =
      (mismatches (fun t => u t p) (fun t => v t p):ℝ≥0∞) := by
  classical
  simp only [errors,mismatches_sum,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : u t p=v t p
  · simp [h]
  · simp [h]

/-- Compact symbol cores give simultaneous full-half-name recovery with
original (not conditionally normalized) mass at least .98. -/
theorem symbol_success (μ : Measure M) [IsProbabilityMeasure μ]
    (S Sinv : M → M) (hS : MeasurePreserving S μ μ) (hSi : MeasurePreserving Sinv μ μ)
    (f : M → A) (hf : Measurable f) :
    ∃ δ : ℝ,0<δ ∧ ∀ (D : SwitchData μ) (n : ℕ),0<n →
      (99/100:ℝ)≤D.law.real D.carrier → D.retained.map D.point≤(2:ℝ≥0∞) • μ →
      (∀ p∈D.carrier,∀ t v : Fin (n+1),
        dist (S^[t.val] (D.point p)) (S^[t.val] p.1)+
        dist (Sinv^[v.val] (D.point p)) (Sinv^[v.val] p.2)<δ) →
      ∃ H : Set (M×M),MeasurableSet H ∧ H⊆D.carrier ∧ (98/100:ℝ)≤D.law.real H ∧
        ∀ p∈H,
          (mismatches (fun t : Fin n => f (S^[t.val] p.1))
            (fun t : Fin n => f (S^[t.val] (D.point p))):ℝ)<(3/400:ℝ)*n ∧
          (mismatches (fun t : Fin n => f (Sinv^[n-t.val] p.2))
            (fun t : Fin n => f (Sinv^[n-t.val] (D.point p))):ℝ)<(3/400:ℝ)*n := by
  classical
  obtain ⟨C,δ,hC,hCm,hδ,hsep⟩ := SymbolCores.compact_core μ f hf (by norm_num : (0:ℝ)<1/1000000)
  refine ⟨δ,hδ,?_⟩
  intro D n hn hmass hdom hshadow
  let : IsProbabilityMeasure D.law := PairLaw.law_probability μ D.label D.label_measurable
  let σ := D.retained
  let : IsFiniteMeasure σ := inferInstanceAs (IsFiniteMeasure (D.law.restrict D.carrier))
  have hσfst : σ.map Prod.fst≤(1:ℝ≥0∞) • μ := by
    rw [one_smul,←PairLaw.first_marginal μ D.label D.label_measurable]
    exact Measure.map_mono Measure.restrict_le_self measurable_fst
  have hσsnd : σ.map Prod.snd≤(1:ℝ≥0∞) • μ := by
    rw [one_smul,←PairLaw.second_marginal μ D.label D.label_measurable]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd
  let b₁ : Fin n → Set (M×M) := fun t => {p | f (S^[t.val] p.1)≠f (S^[t.val] (D.point p))}
  let b₂ : Fin n → Set (M×M) := fun t => {p | f (Sinv^[n-t.val] p.2)≠f (Sinv^[n-t.val] (D.point p))}
  have hb₁ (t : Fin n) : MeasurableSet (b₁ t) :=
    (measurableSet_eq_fun (hf.comp ((hS.iterate _).measurable.comp measurable_fst))
      (hf.comp ((hS.iterate _).measurable.comp D.point_measurable))).compl
  have hb₂ (t : Fin n) : MeasurableSet (b₂ t) :=
    (measurableSet_eq_fun (hf.comp ((hSi.iterate _).measurable.comp measurable_snd))
      (hf.comp ((hSi.iterate _).measurable.comp D.point_measurable))).compl
  have hm₁ (t : Fin n) : σ (b₁ t)≤3*ENNReal.ofReal (1/1000000:ℝ) := by
    have hh := mismatch_mass σ μ f C hC.isClosed hsep
      (fun p => S^[t.val] p.1) (fun p => S^[t.val] (D.point p))
      ((hS.iterate _).measurable.comp measurable_fst)
      ((hS.iterate _).measurable.comp D.point_measurable) 1 2
      (transported_domination σ μ Prod.fst measurable_fst (S^[t.val]) (hS.iterate _) 1 hσfst)
      (transported_domination σ μ D.point D.point_measurable (S^[t.val]) (hS.iterate _) 2 hdom)
      (by
        filter_upwards [ae_restrict_mem D.carrier_measurable] with p hp
        rw [edist_dist,ENNReal.coe_nnreal_eq]
        apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
        have hs := hshadow p hp ⟨t.val,by omega⟩ ⟨0,by omega⟩
        rw [dist_comm]
        exact lt_of_le_of_lt (le_add_of_nonneg_right dist_nonneg) hs)
    calc σ (b₁ t) ≤ (1+2)*μ Cᶜ := hh
      _ ≤ 3*ENNReal.ofReal (1/1000000:ℝ) := by norm_num; gcongr
  have hm₂ (t : Fin n) : σ (b₂ t)≤3*ENNReal.ofReal (1/1000000:ℝ) := by
    have hh := mismatch_mass σ μ f C hC.isClosed hsep
      (fun p => Sinv^[n-t.val] p.2) (fun p => Sinv^[n-t.val] (D.point p))
      ((hSi.iterate _).measurable.comp measurable_snd)
      ((hSi.iterate _).measurable.comp D.point_measurable) 1 2
      (transported_domination σ μ Prod.snd measurable_snd (Sinv^[n-t.val]) (hSi.iterate _) 1 hσsnd)
      (transported_domination σ μ D.point D.point_measurable (Sinv^[n-t.val]) (hSi.iterate _) 2 hdom)
      (by
        filter_upwards [ae_restrict_mem D.carrier_measurable] with p hp
        rw [edist_dist,ENNReal.coe_nnreal_eq]
        apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
        have hs := hshadow p hp ⟨0,by omega⟩ ⟨n-t.val,by omega⟩
        rw [dist_comm]
        exact lt_of_le_of_lt (le_add_of_nonneg_left dist_nonneg) hs)
    calc σ (b₂ t) ≤ (1+2)*μ Cᶜ := hh
      _ ≤ 3*ENNReal.ofReal (1/1000000:ℝ) := by norm_num; gcongr
  let B := {p | (n:ℝ≥0∞)*ENNReal.ofReal (3/400:ℝ)≤errors n b₁ p} ∪
    {p | (n:ℝ≥0∞)*ENNReal.ofReal (3/400:ℝ)≤errors n b₂ p}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const (measurable_errors n b₁ hb₁)).union
      (measurableSet_le measurable_const (measurable_errors n b₂ hb₂))
  have hBm : σ B≤ENNReal.ofReal (1/100:ℝ) := by
    have hh := two_halves_bad σ n hn b₁ b₂ hb₁ hb₂ (3*ENNReal.ofReal (1/1000000:ℝ))
      (ENNReal.ofReal (3/400:ℝ)) (by norm_num) (by finiteness) hm₁ hm₂
    apply hh.trans
    calc
      _ = ENNReal.ofReal (2*(3*(1/1000000)/(3/400):ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
          ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3/400),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
        norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by norm_num)
  let H := Bᶜ∩D.carrier
  have hHm : (98/100:ℝ)≤D.law.real H := by
    have he : D.law.real H=σ.real Bᶜ := by
      change (D.law H).toReal=((D.law.restrict D.carrier) Bᶜ).toReal
      rw [Measure.restrict_apply hB.compl]
    rw [he,measureReal_compl hB]
    have hu : σ.real univ=D.law.real D.carrier := by
      simp only [σ,SwitchData.retained,Measure.real,Measure.restrict_apply_univ]
    rw [hu]
    have hBr : σ.real B≤1/100 := (ENNReal.toReal_mono (by finiteness) hBm).trans_eq (by norm_num)
    linarith
  refine ⟨H,hB.compl.inter D.carrier_measurable,inter_subset_right, hHm,?_⟩
  intro p hp
  have hh₁ : errors n b₁ p<(n:ℝ≥0∞)*ENNReal.ofReal (3/400:ℝ) := lt_of_not_ge (fun hh => hp.1 (Or.inl hh))
  have hh₂ : errors n b₂ p<(n:ℝ≥0∞)*ENNReal.ofReal (3/400:ℝ) := lt_of_not_ge (fun hh => hp.1 (Or.inr hh))
  rw [errors_eq_mismatches] at hh₁ hh₂
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  constructor
  · have hh := ENNReal.toReal_lt_toReal (by finiteness) (by finiteness) |>.mpr hh₁
    norm_num [ENNReal.toReal_mul,b₁] at hh
    simpa only [mul_comm] using hh
  · have hh := ENNReal.toReal_lt_toReal (by finiteness) (by finiteness) |>.mpr hh₂
    norm_num [ENNReal.toReal_mul,b₂] at hh
    simpa only [mul_comm] using hh
end SmoothObstruction.SymbolMass

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.PairUpper
open MeasureTheory Set Finset FiniteLaw
open scoped ENNReal
variable {X C J V : Type*} [MeasurableSpace X]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype J] [DecidableEq J] [Nonempty J]
  [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Nontrivial V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

omit [DecidableEq J] [Fintype V] [DecidableEq V] [Nonempty J] [Nontrivial V] [MeasurableSpace V] [MeasurableSingletonClass V] in
lemma statistic_nonneg (B : LinearMap.BilinForm (ZMod 2) V)
    (u v : J → {v : V // v≠0}) : 0 ≤ statistic B u v := by
  unfold statistic
  positivity

/-- The upper bound is genuinely an integral in the original same-cell
law. Entropies are the original input-observable entropies. -/
theorem integral_upper (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hentU : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ U hU))
    (hentW : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ W hW))
    (hC : Real.log (Fintype.card C)≤
      (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}))
    (hlog : 1000*Real.log 2≤ Real.log (Fintype.card {v : V // v≠0})) :
    (∫ z,statistic B (U z.1) (W z.2) ∂(PairLaw.law μ P))≤ 31/50 := by
  let := PairLaw.law_probability μ P hP
  have hh := expectation_upper μ P hP U W hU hW B hB hentU hentW hC hlog
  rwa [observed_integral] at hh

omit [Nonempty J] [Nontrivial V] in
omit [DecidableEq J] [DecidableEq V] in
/-- The success set is measured in the unconditioned law. -/
theorem integral_success_lower (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V)
    (G : Set (X × X)) (hG : MeasurableSet G)
    (hGm : (19/20:ℝ) ≤ (PairLaw.law μ P).real G)
    (hZG : ∀ z∈G,(24/25:ℝ) ≤ statistic B (U z.1) (W z.2)) :
    (114/125:ℝ) ≤ ∫ z,statistic B (U z.1) (W z.2) ∂(PairLaw.law μ P) := by
  let := PairLaw.law_probability μ P hP
  have hobs : Measurable (fun z : X × X => (U z.1,W z.2)) :=
    (hU.comp measurable_fst).prodMk (hW.comp measurable_snd)
  have hZi : Integrable (fun z : X × X => statistic B (U z.1) (W z.2)) (PairLaw.law μ P) := by
    let f := fun z : X × X => (U z.1,W z.2)
    let g := fun uv : (J → {v : V // v≠0}) × (J → {v : V // v≠0}) => statistic B uv.1 uv.2
    exact (Integrable.of_finite (f:=g) (μ:=(PairLaw.law μ P).map f)).comp_aemeasurable hobs.aemeasurable
  have hl := integral_lower_of_event (PairLaw.law μ P) _ hZi
    (fun z => statistic_nonneg B (U z.1) (W z.2)) G hG (24/25) (19/20)
    (by norm_num) hGm hZG
  have hnum : (24/25:ℝ)*(19/20)=114/125 := by norm_num
  rwa [hnum] at hl

/-- Section7's two conflicting bounds are checked on the SAME original
probability. In particular an event of mass .95 with value≥ .96 is impossible;
no assertion of independence is made on that event or its complement. -/
theorem no_success_event (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hentU : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ U hU))
    (hentW : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ W hW))
    (hC : Real.log (Fintype.card C)≤
      (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}))
    (hlog : 1000*Real.log 2≤ Real.log (Fintype.card {v : V // v≠0}))
    (G : Set (X × X)) (hG : MeasurableSet G)
    (hGm : (19/20:ℝ)≤ (PairLaw.law μ P).real G)
    (hZG : ∀ z∈G,(24/25:ℝ)≤ statistic B (U z.1) (W z.2)) : False := by
  have hl := integral_success_lower μ P hP U W hU hW B G hG hGm hZG
  have hu := integral_upper μ P hP U W hU hW B hB hentU hentW hC hlog
  linarith
end SmoothObstruction.PairUpper

namespace SmoothObstruction.FiniteLaw
open MeasureTheory Set
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
lemma observed_preserving (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : X → Y) (hf : MeasurePreserving f μ ν)
    (g : Y → A) (hg : Measurable g) :
    observed μ (g ∘ f) (hg.comp hf.measurable)=observed ν g hg := by
  apply observed_ext
  funext a
  change μ.real (f ⁻¹' {y | g y=a})=ν.real {y | g y=a}
  rw [Measure.real,←Measure.map_apply hf.measurable (measurableSet_eq_fun hg measurable_const),hf.map_eq]
  rfl
end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw
open scoped ENNReal
lemma firstList_entropy (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {i D : ℕ} (hi : 1 ≤ i) (hD : 2≤D)
    (hDmax : D-1≤WordStep.D (S i)) :
    (249/250:ℝ)*(D-1:ℕ)*Real.log (Fintype.card (A i))≤
      entropy (observed μ (firstList i D) (measurable_firstList i D)) := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  have ha : MeasurePreserving (advance i) μ (boundary μ i) :=
    ⟨measurable_advance i,advance_map μ hT i⟩
  have he := observed_preserving μ (boundary μ i) (advance i) ha (labelList i (D-1))
    (measurable_labelList i (D-1))
  change observed μ (firstList i D) (measurable_firstList i D)=_ at he
  rw [he]
  simpa only [show (249/250:ℝ)=996/1000 by norm_num] using
    stationary_window_entropy_996 μ hT hi (by omega : 1≤D-1) hDmax

lemma advance_block (i D : ℕ) (x : Extension) :
    advance i (T^[D*length 40000 i] x)=T^[D*length 40000 i] (advance i x) := by
  have hp : phase i (T^[D*length 40000 i] x)=phase i x := by
    rw [phase_iterate,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero]
  change T^[(-phase i (T^[D*length 40000 i] x)).val] (T^[D*length 40000 i] x)=_
  rw [hp]
  change T^[(-phase i x).val] (T^[D*length 40000 i] x)=T^[D*length 40000 i] (T^[(-phase i x).val] x)
  rw [←Function.iterate_add_apply,←Function.iterate_add_apply,Nat.add_comm]

lemma graph_firstLists (i k : ℕ) (x : Extension)
    (hg : graphWindows i k (advance i x)) :
    ∀ j : Fin (2^k-1),form (S i) (firstList i (2^k) x j).val
      (firstList i (2^k) (T^[2^k*length 40000 i] x) j).val=0 := by
  intro j
  have hh := hg j
  dsimp only [firstList,labelList]
  rw [advance_block,←Function.iterate_add_apply]
  have he : j.val*length 40000 i+2^k*length 40000 i=(j.val+2^k)*length 40000 i := by ring
  rw [he]
  exact hh

lemma actual_passing_lower (i k : ℕ) (hk : 2≤2^k) (x y z : Extension)
    (hy : (mismatches (firstList i (2^k) y) (firstList i (2^k) z):ℝ)<(2^k:ℕ)/100)
    (hx : (mismatches (firstList i (2^k) x)
      (firstList i (2^k) (T^[2^k*length 40000 i] z)):ℝ)<(2^k:ℕ)/100)
    (hg : graphWindows i k (advance i z)) :
    (24/25:ℝ)≤PairUpper.statistic (form (S i)) (firstList i (2^k) y) (firstList i (2^k) x) := by
  simpa only [PairUpper.statistic,Fintype.card_fin,Nat.cast_sub (by omega : 1≤2^k),Nat.cast_one] using RecognitionWindow.paired_graph_bound hk (fun a b : A i => form (S i) a.val b.val=0)
    (firstList i (2^k) y) (firstList i (2^k) x) (firstList i (2^k) z)
    (firstList i (2^k) (T^[2^k*length 40000 i] z)) (graph_firstLists i k z hg) hy hx

lemma graph_bad_small (i k : ℕ) (hk : k≤K (S i)/8) :
    ((2*2^k-2:ℕ):ℝ)/H (S i)≤1/1000 := by
  have hK := (step_conditions initial_threshold i).1
  change 256≤K (S i) at hK
  have hp : 2048*(2^k:ℕ)≤H (S i) := by
    calc
      _ = 2^(k+11) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hH : (0:ℝ)<H (S i) := by dsimp only [H]; positivity
  apply (div_le_iff₀ hH).mpr
  have hr : (1000:ℝ)*((2*2^k-2:ℕ):ℝ)≤H (S i) := by
    exact_mod_cast (show 1000*(2*2^k-2)≤H (S i) by omega)
  linarith

lemma alphabet_log_large (i : ℕ) : 1000*Real.log 2≤Real.log (Fintype.card (A i)) := by
  rw [log_card]
  apply mul_le_mul_of_nonneg_right _ (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hK := (step_conditions initial_threshold i).1
  change 256≤K (S i) at hK
  have he := (K_bounds (S i)).1
  have hKr : (256:ℝ)≤K (S i) := by exact_mod_cast hK
  nlinarith
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.SwitchData
open MeasureTheory Set
open scoped ENNReal
variable {M : Type} [MeasurableSpace M] (μ : Measure M) [IsProbabilityMeasure μ]

lemma real_preimage_le {X : Type*} [MeasurableSpace X] (σ : Measure X) [IsFiniteMeasure σ]
    (f : X → M) (hf : Measurable f) (C : ℝ≥0∞) (hC : C≠∞)
    (hd : σ.map f≤C • μ) (E : Set M) (hE : MeasurableSet E) :
    σ.real (f ⁻¹' E)≤C.toReal*μ.real E := by
  have hh := hd E
  rw [Measure.map_apply hf hE,Measure.smul_apply,smul_eq_mul] at hh
  exact (ENNReal.toReal_mono (ENNReal.mul_ne_top hC (measure_ne_top _ _)) hh).trans_eq
    (ENNReal.toReal_mul)

/-- Null transport guards and the rare graph exception are removed from
an already successful set using the ORIGINAL, unnormalized retained law. -/
theorem retain_statistic (D : SwitchData μ)
    (hdom : D.retained.map D.point≤(2:ℝ≥0∞) • μ)
    (H : Set (M×M)) (hH : MeasurableSet H) (hHG : H⊆D.carrier)
    (hHm : (98/100:ℝ)≤D.law.real H)
    (B E : Set M) (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hBc : μ Bᶜ=0) (hEc : μ.real Eᶜ≤1/1000) :
    ∃ K : Set (M×M),MeasurableSet K ∧ K⊆H ∧ (19/20:ℝ)≤D.law.real K ∧
      ∀ p∈K,p.1∈B ∧ p.2∈B ∧ D.point p∈B ∧ D.point p∈E := by
  let : IsProbabilityMeasure D.law := PairLaw.law_probability μ D.label D.label_measurable
  let σ := D.retained
  let : IsFiniteMeasure σ := inferInstanceAs (IsFiniteMeasure (D.law.restrict D.carrier))
  have hf : σ.map Prod.fst≤(1:ℝ≥0∞) • μ := by
    rw [one_smul,←PairLaw.first_marginal μ D.label D.label_measurable]
    exact Measure.map_mono Measure.restrict_le_self measurable_fst
  have hs : σ.map Prod.snd≤(1:ℝ≥0∞) • μ := by
    rw [one_smul,←PairLaw.second_marginal μ D.label D.label_measurable]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd
  have hBr : μ.real Bᶜ=0 := by simp only [Measure.real,hBc,ENNReal.toReal_zero]
  have hm₁ := real_preimage_le μ σ Prod.fst measurable_fst 1 (by norm_num) hf Bᶜ hB.compl
  have hm₂ := real_preimage_le μ σ Prod.snd measurable_snd 1 (by norm_num) hs Bᶜ hB.compl
  have hm₃ := real_preimage_le μ σ D.point D.point_measurable 2 (by norm_num) hdom Bᶜ hB.compl
  have hm₄ := real_preimage_le μ σ D.point D.point_measurable 2 (by norm_num) hdom Eᶜ hE.compl
  simp only [hBr,mul_zero,ENNReal.toReal_ofNat,ENNReal.toReal_one] at hm₁ hm₂ hm₃ hm₄
  let W : Set (M×M) := Prod.fst ⁻¹' Bᶜ ∪ Prod.snd ⁻¹' Bᶜ ∪ D.point ⁻¹' Bᶜ ∪ D.point ⁻¹' Eᶜ
  have hW : MeasurableSet W := (((hB.compl.preimage measurable_fst).union
    (hB.compl.preimage measurable_snd)).union (hB.compl.preimage D.point_measurable)).union
    (hE.compl.preimage D.point_measurable)
  have hWm : σ.real W≤2/1000 := by
    have h₁ := measureReal_union_le (μ:=σ) (s₁:=Prod.fst ⁻¹' Bᶜ) (s₂:=Prod.snd ⁻¹' Bᶜ)
    have h₂ := measureReal_union_le (μ:=σ) (s₁:=Prod.fst ⁻¹' Bᶜ ∪ Prod.snd ⁻¹' Bᶜ) (s₂:=D.point ⁻¹' Bᶜ)
    have h₃ := measureReal_union_le (μ:=σ) (s₁:=Prod.fst ⁻¹' Bᶜ ∪ Prod.snd ⁻¹' Bᶜ ∪ D.point ⁻¹' Bᶜ) (s₂:=D.point ⁻¹' Eᶜ)
    dsimp only [W]
    linarith
  let K := H\(W∩D.carrier)
  have hKm : (19/20:ℝ)≤D.law.real K := by
    have he : D.law.real (W∩D.carrier)=σ.real W := by
      simp only [σ,SwitchData.retained,Measure.real,Measure.restrict_apply hW]
    have hh := le_measureReal_sdiff (μ:=D.law) (s₁:=H) (s₂:=W∩D.carrier)
    rw [he] at hh
    change _≤D.law.real K at hh
    linarith
  refine ⟨K,hH.diff (hW.inter D.carrier_measurable),sdiff_subset,hKm,?_⟩
  intro p hp
  have hpW : p∉W := fun hh => hp.2 ⟨hh,hHG hp.1⟩
  change ¬(((p.1∉B ∨ p.2∉B) ∨ D.point p∉B) ∨ D.point p∉E) at hpW
  tauto
end SmoothObstruction.SwitchData

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Filter Topology WordParameters WordAlphabet WordStep WordConcatenation

lemma cell_cost {J : Type*} [Fintype J] [Nonempty J]
    (i Q n : ℕ) (hQ : 2 ≤ Q) (hn : length 40000 i*Q=n)
    {B C : ℝ} (hB : 0≤B)
    (hc : |C| *(B/rate 40000 i)≤(3/1000:ℝ)*Real.log 2)
    (hcard : (Fintype.card J:ℝ)≤Real.exp (C*B*n)) :
    Real.log (Fintype.card J)≤(3/500:ℝ)*(Q-1:ℕ)*Real.log (Fintype.card (A i)) := by
  have hm : (0:ℝ)<length 40000 i := by exact_mod_cast length_pos 40000 i
  have hL : 0≤ell (S i) := ell_nonneg _
  have hR : 0 < rate 40000 i := rate_pos initial_threshold i
  have hrate : rate 40000 i*(length 40000 i:ℝ)=ell (S i) := by
    dsimp only [rate,S]
    exact div_mul_cancel₀ _ hm.ne'
  have hc' : C*B≤(3/1000:ℝ)*Real.log 2*rate 40000 i := by
    have hh : |C| *B≤(3/1000:ℝ)*Real.log 2*rate 40000 i := by
      apply (div_le_iff₀ hR).mp
      simpa only [mul_div_assoc] using hc
    exact (mul_le_mul_of_nonneg_right (le_abs_self C) hB).trans hh
  have hnR : (n:ℝ)=(length 40000 i:ℝ)*Q := by exact_mod_cast hn.symm
  have hc'' : C*B*n≤(3/1000:ℝ)*Q*Real.log (Fintype.card (A i)) := by
    have hh := mul_le_mul_of_nonneg_right hc' (show (0:ℝ)≤length 40000 i*Q by positivity)
    rw [←hnR] at hh
    apply hh.trans_eq
    rw [WordHierarchy.log_card,hnR]
    calc
      _ = (3/1000:ℝ)*Q*(rate 40000 i*length 40000 i)*Real.log 2 := by ring
      _ = _ := by rw [hrate]; ring
  have hlog : 0≤Real.log (Fintype.card (A i)) := by
    rw [WordHierarchy.log_card]
    exact mul_nonneg hL (Real.log_nonneg (by norm_num))
  have hQr : (Q:ℝ)≤2*(Q-1:ℕ) := by exact_mod_cast (show Q≤2*(Q-1) by omega)
  calc
    Real.log (Fintype.card J) ≤ C*B*n := (Real.log_le_iff_le_exp (by exact_mod_cast Fintype.card_pos)).mpr hcard
    _ ≤ _ := hc''
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hQr hlog]

lemma cheap_index_tendsto (i j : ℕ → ℕ) (hi : Tendsto i atTop atTop)
    (hj : ∀ a,j a∈testScales 40000 (i a)) : Tendsto j atTop atTop := by
  apply tendsto_atTop_mono (fun a => ?_) hi
  have hh := (Finset.mem_Icc.mp (hj a)).1
  have hl : i a ≤ logLevel 40000 (i a) := (logLevel_strictMono initial_threshold).id_le (i a)
  omega
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open Set MeasureTheory WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw
open scoped ENNReal

lemma measurable_initialSymbol : Measurable initialSymbol := by
  unfold initialSymbol
  fun_prop

lemma iterate_forward_inverse {X : Type*} (e : X ≃ X) (n t : ℕ) (ht : t ≤ n) (x : X) :
    (e^[t]) ((e.symm^[n]) x)=(e.symm^[n-t]) x := by
  calc
    _ = (e^[t]) ((e.symm^[t]) ((e.symm^[n-t]) x)) := by
      rw [←Function.iterate_add_apply,Nat.add_sub_of_le ht]
    _ = _ := (Function.LeftInverse.iterate (fun x => e.apply_symm_apply x) t) _

lemma statistic_symm (i Q : ℕ) (u v : Fin (Q-1) → A i) :
    PairUpper.statistic (form (S i)) u v=PairUpper.statistic (form (S i)) v u := by
  unfold PairUpper.statistic
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [form_symm]

variable {M : Type} [MeasurableSpace M]
  (μ : Measure Extension) [IsProbabilityMeasure μ]
  (ν : Measure M) [IsProbabilityMeasure ν]
  (R : M ≃ M) (hR : MeasurePreserving R ν ν) (hRi : MeasurePreserving R.symm ν ν)
  (r : M → Extension) (hr : MeasurePreserving r ν μ)
  (B : Set M) (hBinv : R.symm ⁻¹' B=B)
  (hforward : ∀ t,∀ x∈B,r ((R^[t]) x)=(T^[t]) (r x))

include hforward in
omit [MeasurableSpace M] in
lemma pull_symbol (t : ℕ) (x : M) (hx : x∈B) :
    initialSymbol (r ((R^[t]) x))=(r x).val.1 t := by
  rw [hforward t x hx]
  exact (actual_iterate_symbol (r x) t 0).trans (by rw [zero_add])

include hBinv hforward in
omit [MeasurableSpace M] in
lemma pull_past_symbol (n t : ℕ) (ht : t ≤ n) (x : M) (hx : x∈B) :
    initialSymbol (r ((R.symm^[n-t]) x))=(r ((R.symm^[n]) x)).val.1 t := by
  have hb := ConullTransport.invariant_iterates R.symm B hBinv n x hx
  have hh := pull_symbol R r B hforward t ((R.symm^[n]) x) hb
  rwa [iterate_forward_inverse R n t ht] at hh

include hBinv hforward in
omit [MeasurableSpace M] in
lemma pull_past_advance (n : ℕ) (x : M) (hx : x∈B) :
    (T^[n]) (r ((R.symm^[n]) x))=r x := by
  have hb := ConullTransport.invariant_iterates R.symm B hBinv n x hx
  rw [←hforward n _ hb,iterate_forward_inverse R n n le_rfl,Nat.sub_self,Function.iterate_zero_apply]

include hr hRi in
lemma transported_graph_bad (hT : MeasurePreserving T μ μ) (i k n : ℕ)
    (hk : k ≤ K (S i)/8) :
    ν.real {x | graphWindows i k (advance i (r ((R.symm^[n]) x)))}ᶜ ≤ 1/1000 := by
  have hp := hr.comp (hRi.iterate n)
  have hG : MeasurableSet {x | graphWindows i k (advance i x)} :=
    (measurable_graphWindows i k).preimage (measurable_advance i)
  have he : ν.real {x | graphWindows i k (advance i (r ((R.symm^[n]) x)))}=
      μ.real {x | graphWindows i k (advance i x)} := by
    simp only [Measure.real]
    rw [←hp.map_eq,Measure.map_apply hp.measurable hG]
    rfl
  have hE : MeasurableSet {x | graphWindows i k (advance i (r ((R.symm^[n]) x)))} :=
    hG.preimage hp.measurable
  rw [measureReal_compl hE,probReal_univ,he]
  have hh := stationary_graph_probability μ hT i k hk
  have hb := graph_bad_small i k hk
  linarith

include hr hRi hBinv hforward in
/-- Conull guards, both full-half original names, and the graph test are joined
in the ORIGINAL cell-weighted law. The two entries keep their original order. -/
theorem transported_success (hT : MeasurePreserving T μ μ)
    (hB : MeasurableSet B) (hBc : ν Bᶜ=0)
    (i k : ℕ) (hk : k ≤ K (S i)/8) (hQ : 2 ≤ 2^k)
    (D : SwitchData ν) (hdom : D.retained.map D.point≤(2:ℝ≥0∞) • ν)
    (H : Set (M×M)) (hH : MeasurableSet H) (hHG : H⊆D.carrier)
    (hHm : (98/100:ℝ)≤D.law.real H)
    (hgood : ∀ p∈H,
      (mismatches (fun t : Fin (2^k*length 40000 i) => initialSymbol (r ((R^[t.val]) p.1)))
        (fun t : Fin (2^k*length 40000 i) => initialSymbol (r ((R^[t.val]) (D.point p)))):ℝ)<
          (3/400:ℝ)*(2^k*length 40000 i) ∧
      (mismatches (fun t : Fin (2^k*length 40000 i) => initialSymbol (r ((R.symm^[2^k*length 40000 i-t.val]) p.2)))
        (fun t : Fin (2^k*length 40000 i) => initialSymbol (r ((R.symm^[2^k*length 40000 i-t.val]) (D.point p)))):ℝ)<
          (3/400:ℝ)*(2^k*length 40000 i)) :
    ∃ F : Set (M×M),MeasurableSet F ∧ (19/20:ℝ)≤D.law.real F ∧
      ∀ p∈F,(24/25:ℝ)≤PairUpper.statistic (form (S i))
        (firstList i (2^k) (r p.1))
        (firstList i (2^k) (r ((R.symm^[2^k*length 40000 i]) p.2))) := by
  let n := 2^k*length 40000 i
  let E := {x | graphWindows i k (advance i (r ((R.symm^[n]) x)))}
  have hE : MeasurableSet E := (measurable_graphWindows i k).preimage
    ((measurable_advance i).comp (hr.measurable.comp (hRi.measurable.iterate n)))
  have hEc : ν.real Eᶜ≤1/1000 := transported_graph_bad μ ν R hRi r hr hT i k n hk
  obtain ⟨F,hF,hFH,hFm,hguard⟩ := D.retain_statistic ν hdom H hH hHG hHm B E hB hE hBc hEc
  refine ⟨F,hF,hFm,?_⟩
  intro p hp
  obtain ⟨hx,hy,hz,hgraph⟩ := hguard p hp
  obtain ⟨hf,hp'⟩ := hgood p (hFH hp)
  have hfc : (mismatches (fun t : Fin n => (r p.1).val.1 t.val)
      (fun t : Fin n => (r (D.point p)).val.1 t.val):ℝ)<(3/4:ℝ)*(2^k*length 40000 i)/100 := by
    have he₁ : (fun t : Fin n => initialSymbol (r ((R^[t.val]) p.1)))=
        (fun t : Fin n => (r p.1).val.1 t.val) := by
      funext t; exact pull_symbol R r B hforward t.val p.1 hx
    have he₂ : (fun t : Fin n => initialSymbol (r ((R^[t.val]) (D.point p))))=
        (fun t : Fin n => (r (D.point p)).val.1 t.val) := by
      funext t; exact pull_symbol R r B hforward t.val (D.point p) hz
    rw [he₁,he₂] at hf
    convert hf using 1 <;> first | rfl | ring
  have hpc : (mismatches (fun t : Fin n => (r ((R.symm^[n]) p.2)).val.1 t.val)
      (fun t : Fin n => (r ((R.symm^[n]) (D.point p))).val.1 t.val):ℝ)<(3/4:ℝ)*(2^k*length 40000 i)/100 := by
    have he₁ : (fun t : Fin n => initialSymbol (r ((R.symm^[n-t.val]) p.2)))=
        (fun t : Fin n => (r ((R.symm^[n]) p.2)).val.1 t.val) := by
      funext t; exact pull_past_symbol R r B hBinv hforward n t.val (Nat.le_of_lt t.isLt) p.2 hy
    have he₂ : (fun t : Fin n => initialSymbol (r ((R.symm^[n-t.val]) (D.point p))))=
        (fun t : Fin n => (r ((R.symm^[n]) (D.point p))).val.1 t.val) := by
      funext t; exact pull_past_symbol R r B hBinv hforward n t.val (Nat.le_of_lt t.isLt) (D.point p) hz
    rw [he₁,he₂] at hp'
    convert hp' using 1 <;> first | rfl | ring
  have hfr := (actual_recovery i (2^k) hQ (r p.1) (r (D.point p)) (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hfc)).2
  have hpr := (actual_recovery i (2^k) hQ (r ((R.symm^[n]) p.2))
    (r ((R.symm^[n]) (D.point p))) (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hpc)).2
  have had := pull_past_advance R r B hBinv hforward n (D.point p) hz
  have hfr' : (mismatches (firstList i (2^k) (r p.1))
      (firstList i (2^k) ((T^[n]) (r ((R.symm^[n]) (D.point p))))):ℝ)<(2^k:ℕ)/100 := by
    rw [had]
    exact hfr
  have hh := actual_passing_lower i k hQ (r p.1) (r ((R.symm^[n]) p.2))
    (r ((R.symm^[n]) (D.point p))) hpr hfr' hgraph
  rwa [statistic_symm] at hh
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Filter Topology WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw
open scoped ENNReal

/-- The obstruction for the genuine word extension, using the entire smooth
switching property and exact invariant-conull transport, not a factor-only
or globally defined conjugacy substitute. -/
theorem no_switching_oai {M : Type} [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    (μ : Measure Extension) [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (ν : Measure M) [IsProbabilityMeasure ν]
    (R : M ≃ M) (hR : MeasurePreserving R ν ν) (hRi : MeasurePreserving R.symm ν ν)
    (r : M → Extension) (hr : MeasurePreserving r ν μ)
    (B : Set M) (hB : MeasurableSet B) (hBc : ν Bᶜ=0) (hBinv : R.symm ⁻¹' B=B)
    (hforward : ∀ t,∀ x∈B,r ((R^[t]) x)=(T^[t]) (r x))
    (hswitch : SmoothSwitching ν R R.symm) : False := by
  classical
  obtain ⟨δ,hδ,hδworks⟩ := SymbolMass.symbol_success ν R R.symm hR hRi
    (initialSymbol ∘ r) (measurable_initialSymbol.comp hr.measurable)
  obtain ⟨b,C,Ds,hb,hbs,hDs,hshadow⟩ := hswitch (1/100) (by norm_num)
  obtain ⟨ii,jj,hij,hjt,hit,hcheap,hwindow⟩ := actual_cheap_scales initial_threshold hb hbs
  have hjtend := cheap_index_tendsto ii jj hit hjt
  have heC : ∀ᶠ a in atTop,|C| *(b (jj a)/rate 40000 (ii a))≤(3/1000:ℝ)*Real.log 2 := by
    have h : Tendsto (fun a => |C| *(b (jj a)/rate 40000 (ii a))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hcheap.const_mul |C|
    have hp : (0:ℝ)<(3/1000:ℝ)*Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
    exact h.eventually_le_const hp
  have hei : ∀ᶠ a in atTop,1 ≤ ii a := hit.eventually (eventually_ge_atTop 1)
  obtain ⟨a,hai,haC,haD,hash⟩ := (hei.and (heC.and ((hjtend.eventually hDs).and
    (hjtend.eventually (hshadow δ hδ))))).exists
  obtain ⟨k,hkmin,hk,hwin,hQ⟩ := hwindow a
  let i := ii a
  let j := jj a
  let D := Ds j
  have hin : 1 ≤ i := hai
  have hkn : k≤K (S i)/8 := hk
  have hwin' : 2^k*length 40000 i=2^j := by simpa only [Nat.mul_comm] using hwin
  have hm : (99/100:ℝ)≤D.law.real D.carrier := by
    have hh := haD.2.1
    norm_num at hh
    exact hh
  have hn : 0<2^j := by positivity
  obtain ⟨H,hH,hHG,hHm,hgood⟩ := hδworks D (2^j) hn hm haD.2.2 hash
  rw [←hwin'] at hgood
  obtain ⟨F,hF,hFm,hpass⟩ := transported_success μ ν R hRi r hr B hBinv hforward
    hT hB hBc i k hkn hQ D haD.2.2 H hH hHG hHm
      (by simpa only [Function.comp_apply,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hgood)
  let U : M → Fin (2^k-1) → A i := firstList i (2^k) ∘ r
  let W : M → Fin (2^k-1) → A i := firstList i (2^k) ∘ r ∘ (R.symm^[2^k*length 40000 i])
  have hU : Measurable U := (measurable_firstList i (2^k)).comp hr.measurable
  have hpast := hr.comp (hRi.iterate (2^k*length 40000 i))
  have hW : Measurable W := (measurable_firstList i (2^k)).comp hpast.measurable
  have hDmax : 2^k-1≤WordStep.D (S i) := by
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) hkn)
  have hent := firstList_entropy μ hT hin hQ hDmax
  have hentU : (249/250:ℝ)*(2^k-1:ℕ)*Real.log (Fintype.card (A i))≤
      entropy (observed ν U hU) := by
    have hh := observed_preserving ν μ r hr (firstList i (2^k)) (measurable_firstList i (2^k))
    change observed ν U hU=_ at hh
    rw [hh]
    exact hent
  have hentW : (249/250:ℝ)*(2^k-1:ℕ)*Real.log (Fintype.card (A i))≤
      entropy (observed ν W hW) := by
    have hh := observed_preserving ν μ (r ∘ (R.symm^[2^k*length 40000 i])) hpast
      (firstList i (2^k)) (measurable_firstList i (2^k))
    change observed ν W hW=_ at hh
    rw [hh]
    exact hent
  let : Nonempty D.J := ⟨D.label (Classical.choice ‹Nonempty M›)⟩
  have hC : Real.log (Fintype.card D.J)≤(3/500:ℝ)*(2^k-1:ℕ)*Real.log (Fintype.card (A i)) :=
    cell_cost i (2^k) (2^j) hQ hwin (hb _).le haC haD.1
  let : NeZero (2^k-1) := ⟨by omega⟩
  let v : A i := Classical.choice (levelNonempty i)
  let : Nontrivial (Space (S i)) := ⟨⟨v.val,0,v.property⟩⟩
  apply PairUpper.no_success_event ν D.label D.label_measurable U W hU hW (form (S i))
    (form_nondegenerate _) (by simpa only [Fintype.card_fin] using hentU)
    (by simpa only [Fintype.card_fin] using hentW)
    (by simpa only [Fintype.card_fin] using hC) (alphabet_log_large i) F hF hFm
  exact hpass
end SmoothObstruction.WordHierarchy

end

end OAI
end

theorem solution : type_of% @OAI.SmoothObstruction.WordHierarchy.no_switching_oai := @OAI.SmoothObstruction.WordHierarchy.no_switching_oai
