-- Prove2me | solution 1 for GraphAlignment.Impossible.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T19:15:09.198505+00:00
-- url     : https://prove2.me/submissions/e9076cec-9ae1-412e-9841-2c30bbb70b95

import Mathlib
import Definitions.Def_GraphAlignment_Impossible_Setting

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

abbrev Triple (n : ℕ) := Equiv.Perm (Fin n) × Config n × Equiv.Perm (Fin n)

noncomputable def tripleLaw {n : ℕ} (r : Bool × Bool → ℝ) (alg : Alg n)
    (z : Triple n) : ℝ :=
  (1 / (n.factorial : ℝ)) * cfgLaw r z.2.1 * alg.k (obs z.1 z.2.1) z.2.2

noncomputable def matchCount {n : ℕ} (pi rho : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => pi i = rho i).card

noncomputable def matchMass {n : ℕ} (r : Bool × Bool → ℝ) (m : ℕ) (alg : Alg n) : ℝ :=
  ∑ z : Triple n, tripleLaw r alg z * (if m ≤ matchCount z.2.2 z.1 then 1 else 0)

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

noncomputable def prodLaw {I X : Type*} [Fintype I] (p : X → ℝ) (x : I → X) : ℝ :=
  ∏ i, p (x i)

lemma prodLaw_nonneg {I X : Type*} [Fintype I] (p : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : I → X) : 0 ≤ prodLaw p x :=
  Finset.prod_nonneg fun i _ => hp (x i)

lemma prodLaw_sum {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] (p : X → ℝ)
    (hp : ∑ x, p x = 1) : ∑ x : I → X, prodLaw p x = 1 := by
  classical
  unfold prodLaw
  rw [← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]

lemma prodLaw_pos {I X : Type*} [Fintype I] (p : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : I → X) : 0 < prodLaw p x ↔ ∀ i, 0 < p (x i) := by
  classical
  constructor
  · intro h i
    have hn := Finset.prod_ne_zero_iff.mp (ne_of_gt h)
    exact lt_of_le_of_ne (hp (x i)) (Ne.symm (hn i (Finset.mem_univ i)))
  · intro h
    exact Finset.prod_pos fun i _ => h i

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma entropy_atom (p q g : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) :
    p * g ≤ p * Real.log (p/q) + q * Real.exp g - p := by
  by_cases hp0 : p = 0
  · simp only [hp0, zero_mul, sub_zero]
    positivity
  have hp1 : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq1 := hs hp1
  have hx : 0 < q * Real.exp g / p := by positivity
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hp
  rw [Real.log_div (ne_of_gt (mul_pos hq1 (Real.exp_pos g))) hp0,
    Real.log_mul (ne_of_gt hq1) (ne_of_gt (Real.exp_pos g)), Real.log_exp] at hh
  rw [Real.log_div hp0 (ne_of_gt hq1)]
  have he : p * (q * Real.exp g / p - 1) = q * Real.exp g - p := by
    field_simp
  rw [he] at hh
  nlinarith

lemma finite_entropy {X : Type*} [Fintype X] (P Q g : X → ℝ)
    (hp : ∀ x, 0 ≤ P x) (hq : ∀ x, 0 ≤ Q x)
    (hpsum : ∑ x, P x = 1) (hs : ∀ x, 0 < P x → 0 < Q x) :
    (∑ x, P x * g x) ≤ kl P Q + (∑ x, Q x * Real.exp (g x)) - 1 := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => entropy_atom (P x) (Q x) (g x) (hp x) (hq x) (hs x))
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hpsum, kl] using hh

lemma finite_kl_nonneg {X : Type*} [Fintype X] (P Q : X → ℝ)
    (hp : ∀ x, 0 ≤ P x) (hq : ∀ x, 0 ≤ Q x)
    (hpsum : ∑ x, P x = 1) (hqsum : ∑ x, Q x = 1)
    (hs : ∀ x, 0 < P x → 0 < Q x) : 0 ≤ kl P Q := by
  simpa only [mul_zero, Finset.sum_const_zero, Real.exp_zero, mul_one,
    hqsum, add_sub_cancel_right] using finite_entropy P Q (fun _ => 0) hp hq hpsum hs

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma pLaw_nonneg {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) (hs : s ≤ 1)
    (a : Bool × Bool) : 0 ≤ pLaw q s a := by
  have hq1 : q ≤ 1 := hqs.trans hs
  have hs0 : 0 ≤ s := hq.trans hqs
  have hh := mul_nonneg hq (sub_nonneg.mpr hqs)
  rcases a with ⟨a,b⟩
  cases a <;> cases b <;> simp only [pLaw] <;> nlinarith [sq_nonneg (1-q)]

lemma qLaw_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (a : Bool × Bool) : 0 ≤ qLaw q a := by
  rcases a with ⟨a,b⟩
  cases a <;> cases b <;> simp only [qLaw] <;> nlinarith [sq_nonneg (1-q),sq_nonneg q]

lemma pLaw_sum (q s : ℝ) : ∑ a, pLaw q s a = 1 := by
  simp [Fintype.sum_prod_type, pLaw]
  ring

lemma qLaw_sum (q : ℝ) : ∑ a, qLaw q a = 1 := by
  simp [Fintype.sum_prod_type, qLaw]
  ring

lemma pLaw_support {q s : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (a : Bool × Bool) (hp : 0 < pLaw q s a) : 0 < qLaw q a := by
  by_cases hq0 : q = 0
  · subst q
    rcases a with ⟨a,b⟩
    cases a <;> cases b <;> norm_num [pLaw, qLaw] at *
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  rcases a with ⟨a,b⟩
  cases a <;> cases b <;> simp only [qLaw] <;>
    nlinarith [sq_pos_of_pos (show 0 < 1-q by linarith), mul_pos hqp (show 0 < 1-q by linarith),sq_pos_of_pos hqp]

lemma klPQ_nonneg {q s : ℝ} (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1) :
    0 ≤ klPQ q s :=
  finite_kl_nonneg (pLaw q s) (qLaw q) (pLaw_nonneg hq hqs.le hs)
    (qLaw_nonneg hq (hqs.le.trans hs)) (pLaw_sum q s) (qLaw_sum q)
    (pLaw_support hq (hqs.trans_le hs))

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma cfgLaw_sum {n : ℕ} (r : Bool × Bool → ℝ) (hr : ∑ a, r a = 1) :
    ∑ w : Config n, cfgLaw r w = 1 := prodLaw_sum r hr

lemma cfgLaw_nonneg {n : ℕ} (r : Bool × Bool → ℝ) (hr : ∀ a, 0 ≤ r a)
    (w : Config n) : 0 ≤ cfgLaw r w := prodLaw_nonneg r hr w

lemma tripleLaw_nonneg {n : ℕ} (r : Bool × Bool → ℝ) (hr : ∀ a, 0 ≤ r a)
    (alg : Alg n) (z : Triple n) : 0 ≤ tripleLaw r alg z :=
  mul_nonneg (mul_nonneg (by positivity) (cfgLaw_nonneg r hr z.2.1))
    (alg.nonneg _ _)

lemma tripleLaw_sum {n : ℕ} (r : Bool × Bool → ℝ) (hr : ∑ a, r a = 1)
    (alg : Alg n) : ∑ z : Triple n, tripleLaw r alg z = 1 := by
  classical
  have hc := cfgLaw_sum (n := n) r hr
  simp only [Triple, Fintype.sum_prod_type, tripleLaw, ← Finset.mul_sum,
    alg.sum_one, mul_one, hc, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

lemma matchMass_nonneg {n : ℕ} (r : Bool × Bool → ℝ) (hr : ∀ a, 0 ≤ r a)
    (m : ℕ) (alg : Alg n) : 0 ≤ matchMass r m alg := by
  classical
  apply Finset.sum_nonneg
  intro z _
  exact mul_nonneg (tripleLaw_nonneg r hr alg z) (by split_ifs <;> norm_num)

lemma failProb_eq_triple {n : ℕ} (q s a : ℝ) (alg : Alg n) :
    failProb q s a alg = ∑ z : Triple n, tripleLaw (pLaw q s) alg z *
      (if overlap z.2.2 z.1 < a then 1 else 0) := by
  classical
  simp only [Triple, Fintype.sum_prod_type, tripleLaw, failProb, cfgProb,
    Finset.mul_sum, mul_assoc]

lemma failProb_bounds {n : ℕ} {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) (hs : s ≤ 1)
    (a : ℝ) (alg : Alg n) : 0 ≤ failProb q s a alg ∧ failProb q s a alg ≤ 1 := by
  classical
  rw [failProb_eq_triple]
  have hp := tripleLaw_nonneg (pLaw q s) (pLaw_nonneg hq hqs hs) alg
  constructor
  · exact Finset.sum_nonneg fun z _ => mul_nonneg (hp z) (by split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ z : Triple n, tripleLaw (pLaw q s) alg z := by
        apply Finset.sum_le_sum
        intro z _
        split_ifs
        · simp only [mul_one, le_refl]
        · simpa only [mul_zero] using hp z
      _ = 1 := tripleLaw_sum _ (pLaw_sum q s) alg

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma prodLaw_coordinate {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (p f : X → ℝ) (hp : ∑ a, p a = 1) (j : I) :
    (∑ x : I → X, prodLaw p x * f (x j)) = ∑ a, p a * f a := by
  classical
  calc
    _ = ∑ x : I → X, ∏ i, p (x i) * (if i = j then f (x i) else 1) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib]
      simp [prodLaw]
    _ = ∏ i : I, ∑ a : X, p a * (if i = j then f a else 1) :=
      (Fintype.prod_sum (fun i : I => fun a : X => p a * (if i = j then f a else 1))).symm
    _ = _ := by
      simp [mul_ite, hp]

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma prodLaw_support {I X : Type*} [Fintype I] (p q : X → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hs : ∀ a, 0 < p a → 0 < q a) (x : I → X)
    (hx : 0 < prodLaw p x) : 0 < prodLaw q x :=
  (prodLaw_pos q hq x).2 fun i => hs (x i) ((prodLaw_pos p hp x).1 hx i)

lemma product_kl {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (p q : X → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (hs : ∀ a, 0 < p a → 0 < q a) :
    kl (prodLaw p : (I → X) → ℝ) (prodLaw q) = (Fintype.card I : ℝ) * kl p q := by
  classical
  have he (x : I → X) : prodLaw p x * Real.log (prodLaw p x / prodLaw q x) =
      prodLaw p x * ∑ i, Real.log (p (x i) / q (x i)) := by
    by_cases hz : prodLaw p x = 0
    · simp only [hz, zero_mul]
    have hpos : 0 < prodLaw p x := lt_of_le_of_ne (prodLaw_nonneg p hp x) (Ne.symm hz)
    have hpi (i : I) : 0 < p (x i) := (prodLaw_pos p hp x).1 hpos i
    have hqi (i : I) : 0 < q (x i) := hs (x i) (hpi i)
    congr 1
    simp only [prodLaw, ← Finset.prod_div_distrib]
    exact Real.log_prod fun i _ => ne_of_gt (div_pos (hpi i) (hqi i))
  unfold kl
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [prodLaw_coordinate p (fun a => Real.log (p a / q a)) hpsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma kl_mul_common (a p q : ℝ) :
    (a*p) * Real.log ((a*p)/(a*q)) = a * (p * Real.log (p/q)) := by
  by_cases ha : a = 0
  · simp only [ha, zero_mul]
  rw [mul_div_mul_left p q ha]
  ring

lemma triple_kl_eq_cfg {n : ℕ} (p q : Bool × Bool → ℝ) (alg : Alg n) :
    kl (tripleLaw p alg) (tripleLaw q alg) =
      kl (cfgLaw p : Config n → ℝ) (cfgLaw q) := by
  classical
  have he (z : Triple n) : tripleLaw p alg z * Real.log (tripleLaw p alg z / tripleLaw q alg z) =
      (1 / (n.factorial : ℝ)) * (cfgLaw p z.2.1 * Real.log (cfgLaw p z.2.1 / cfgLaw q z.2.1)) *
        alg.k (obs z.1 z.2.1) z.2.2 := by
    unfold tripleLaw
    rw [show (1 / (n.factorial : ℝ)) * cfgLaw p z.2.1 * alg.k (obs z.1 z.2.1) z.2.2 =
      ((1 / (n.factorial : ℝ)) * alg.k (obs z.1 z.2.1) z.2.2) * cfgLaw p z.2.1 by ring]
    rw [show (1 / (n.factorial : ℝ)) * cfgLaw q z.2.1 * alg.k (obs z.1 z.2.1) z.2.2 =
      ((1 / (n.factorial : ℝ)) * alg.k (obs z.1 z.2.1) z.2.2) * cfgLaw q z.2.1 by ring]
    rw [kl_mul_common]
    ring
  unfold kl
  simp_rw [he]
  simp only [Triple, Fintype.sum_prod_type, ← Finset.mul_sum, alg.sum_one, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

lemma triple_kl_eq {n : ℕ} {q s : ℝ} (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1)
    (alg : Alg n) :
    kl (tripleLaw (pLaw q s) alg) (tripleLaw (qLaw q) alg) =
      (Fintype.card (Pair n) : ℝ) * klPQ q s := by
  rw [triple_kl_eq_cfg]
  exact product_kl (pLaw q s) (qLaw q) (pLaw_nonneg hq hqs.le hs)
    (pLaw_sum q s) (pLaw_support hq (hqs.trans_le hs))

lemma tripleLaw_support {n : ℕ} {q s : ℝ} (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1)
    (alg : Alg n) (z : Triple n) (hp : 0 < tripleLaw (pLaw q s) alg z) :
    0 < tripleLaw (qLaw q) alg z := by
  have hc0 := cfgLaw_nonneg (pLaw q s) (pLaw_nonneg hq hqs.le hs) z.2.1
  have hu : 0 < (1 / (n.factorial : ℝ)) := by positivity
  have hk0 := alg.nonneg (obs z.1 z.2.1) z.2.2
  have hpk : 0 < cfgLaw (pLaw q s) z.2.1 ∧ 0 < alg.k (obs z.1 z.2.1) z.2.2 := by
    have hh : 0 < cfgLaw (pLaw q s) z.2.1 * alg.k (obs z.1 z.2.1) z.2.2 := by
      exact (mul_pos_iff_of_pos_left hu).mp (by simpa only [tripleLaw, mul_assoc] using hp)
    rcases mul_pos_iff.mp hh with h | h
    · exact h
    · exfalso
      linarith [h.1]
  have hcq := prodLaw_support (pLaw q s) (qLaw q) (pLaw_nonneg hq hqs.le hs)
    (qLaw_nonneg hq (hqs.le.trans hs)) (pLaw_support hq (hqs.trans_le hs)) z.2.1 hpk.1
  exact mul_pos (mul_pos hu hcq) hpk.2

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma finite_event_information {X : Type*} [Fintype X] (P Q : X → ℝ)
    (E : X → Prop) [DecidablePred E] (M : ℝ) (hM : 0 < M)
    (hp : ∀ x, 0 ≤ P x) (hq : ∀ x, 0 ≤ Q x)
    (hpsum : ∑ x, P x = 1) (hqsum : ∑ x, Q x = 1)
    (hs : ∀ x, 0 < P x → 0 < Q x)
    (href : M * (∑ x, Q x * (if E x then 1 else 0)) ≤ 1) :
    (∑ x, P x * (if E x then 1 else 0)) * Real.log M ≤ kl P Q + 1 := by
  let g := fun x => if E x then Real.log M else 0
  have he : (∑ x, P x * g x) = (∑ x, P x * (if E x then 1 else 0)) * Real.log M := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [g]
    split_ifs <;> simp
  have hex : (∑ x, Q x * Real.exp (g x)) ≤ 2 := by
    calc
      _ ≤ ∑ x, (Q x + M * (Q x * (if E x then 1 else 0))) := by
        apply Finset.sum_le_sum
        intro x _
        dsimp [g]
        split_ifs
        · rw [Real.exp_log hM]
          simp only [mul_one]
          nlinarith [hq x]
        · simp only [Real.exp_zero, mul_one, mul_zero, add_zero, le_refl]
      _ = 1 + M * (∑ x, Q x * (if E x then 1 else 0)) := by
        rw [Finset.sum_add_distrib, hqsum, ← Finset.mul_sum]
      _ ≤ 2 := by linarith
  have hh := finite_entropy P Q g hp hq hpsum hs
  rw [he] at hh
  linarith

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma match_information {n : ℕ} {q s : ℝ} (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1)
    (m : ℕ) (alg : Alg n)
    (href : matchMass (qLaw q) m alg ≤ 1 / (m.factorial : ℝ)) :
    matchMass (pLaw q s) m alg * Real.log (m.factorial : ℝ) ≤
      (Fintype.card (Pair n) : ℝ) * klPQ q s + 1 := by
  classical
  have hM : 0 < (m.factorial : ℝ) := by positivity
  have hb : (m.factorial : ℝ) * matchMass (qLaw q) m alg ≤ 1 := by
    have hh := (le_div_iff₀ hM).mp href
    simpa only [mul_comm] using hh
  have h := finite_event_information (tripleLaw (pLaw q s) alg) (tripleLaw (qLaw q) alg)
    (fun z : Triple n => m ≤ matchCount z.2.2 z.1) (m.factorial : ℝ) hM
    (tripleLaw_nonneg _ (pLaw_nonneg hq hqs.le hs) alg)
    (tripleLaw_nonneg _ (qLaw_nonneg hq (hqs.le.trans hs)) alg)
    (tripleLaw_sum _ (pLaw_sum q s) alg) (tripleLaw_sum _ (qLaw_sum q) alg)
    (tripleLaw_support hq hqs hs alg) hb
  rw [triple_kl_eq hq hqs hs alg] at h
  exact h

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma matchCount_of_overlap {n m : ℕ} (hn : 0 < n) (a : ℝ)
    (hm : (m : ℝ) ≤ a * n) (pi rho : Equiv.Perm (Fin n))
    (ha : a ≤ overlap pi rho) : m ≤ matchCount pi rho := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right ha hnR.le
  have heq : overlap pi rho * n = (matchCount pi rho : ℝ) := by
    unfold overlap matchCount
    field_simp
  rw [heq] at hmul
  exact_mod_cast hm.trans hmul

lemma one_sub_failProb_le_matchMass {n m : ℕ} {q s a : ℝ}
    (hq : 0 ≤ q) (hqs : q ≤ s) (hs : s ≤ 1) (hn : 0 < n)
    (hm : (m : ℝ) ≤ a * n) (alg : Alg n) :
    1 - failProb q s a alg ≤ matchMass (pLaw q s) m alg := by
  classical
  have hp := tripleLaw_nonneg (pLaw q s) (pLaw_nonneg hq hqs hs) alg
  have hsum := tripleLaw_sum (pLaw q s) (pLaw_sum q s) alg
  have hb : 1 ≤ failProb q s a alg + matchMass (pLaw q s) m alg := by
    rw [← hsum, failProb_eq_triple, matchMass, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    by_cases hf : overlap z.2.2 z.1 < a
    · simp only [hf, ite_true, mul_one]
      have hm0 : 0 ≤ tripleLaw (pLaw q s) alg z *
          (if m ≤ matchCount z.2.2 z.1 then 1 else 0) :=
        mul_nonneg (hp z) (by split_ifs <;> norm_num)
      linarith
    · have hmatch := matchCount_of_overlap hn a hm z.2.2 z.1 (le_of_not_gt hf)
      simp [hf, hmatch]
  linarith

end GraphAlignment.Impossible.GAFresh
end

section

namespace GraphAlignment.Impossible.GAFresh

lemma pair_card_le_square_nat (n : ℕ) : Fintype.card (Pair n) ≤ n^2 := by
  have hsub : Fintype.card (Pair n) ≤ Fintype.card (Sym2 (Fin n)) :=
    Fintype.card_le_of_injective (fun e : Pair n => e.val) Subtype.val_injective
  have hquot : Fintype.card (Sym2 (Fin n)) ≤ Fintype.card (Fin n × Fin n) :=
    Fintype.card_le_of_surjective _ Sym2.mk_surjective
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hsub.trans hquot

lemma pair_card_le_square (n : ℕ) : (Fintype.card (Pair n) : ℝ) ≤ (n : ℝ)^2 := by
  exact_mod_cast pair_card_le_square_nat n

end GraphAlignment.Impossible.GAFresh
end

section

namespace GraphAlignment.Impossible.GAFresh

lemma finite_failure_information {n m : ℕ} {q s a : ℝ}
    (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1) (hn : 0 < n)
    (hm : (m : ℝ) ≤ a * n) (alg : Alg n)
    (href : matchMass (qLaw q) m alg ≤ 1 / (m.factorial : ℝ)) :
    (1 - failProb q s a alg) * Real.log (m.factorial : ℝ) ≤ (n : ℝ)^2 * klPQ q s + 1 := by
  have hlog : 0 ≤ Real.log (m.factorial : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m))
  calc
    _ ≤ matchMass (pLaw q s) m alg * Real.log (m.factorial : ℝ) :=
      mul_le_mul_of_nonneg_right (one_sub_failProb_le_matchMass hq hqs.le hs hn hm alg) hlog
    _ ≤ (Fintype.card (Pair n) : ℝ) * klPQ q s + 1 := match_information hq hqs hs m alg href
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (pair_card_le_square n)
      (klPQ_nonneg hq hqs hs)) le_rfl

end GraphAlignment.Impossible.GAFresh
end

section

namespace GraphAlignment.Impossible.GAFresh

noncomputable def pairRelabel {n : ℕ} (sigma : Equiv.Perm (Fin n)) : Pair n ≃ Pair n where
  toFun e := ⟨e.val.map sigma, by
    rw [Sym2.isDiag_map sigma.injective]
    exact e.property⟩
  invFun e := ⟨e.val.map sigma.symm, by
    rw [Sym2.isDiag_map sigma.symm.injective]
    exact e.property⟩
  left_inv e := by
    apply Subtype.ext
    simp only [Sym2.map_map, Function.comp_def, Equiv.symm_apply_apply, Sym2.map_id', id_eq]
  right_inv e := by
    apply Subtype.ext
    simp only [Sym2.map_map, Function.comp_def, Equiv.apply_symm_apply, Sym2.map_id', id_eq]

lemma pairRelabel_pairOf {n : ℕ} (sigma : Equiv.Perm (Fin n)) (i j : Fin n) (h : i ≠ j) :
    pairRelabel sigma (pairOf i j h) = pairOf (sigma i) (sigma j) (sigma.injective.ne h) := by
  apply Subtype.ext
  rfl

lemma pairRelabel_symm_pairOf {n : ℕ} (sigma : Equiv.Perm (Fin n)) (i j : Fin n) (h : i ≠ j) :
    (pairRelabel sigma).symm (pairOf i j h) =
      pairOf (sigma.symm i) (sigma.symm j) (sigma.symm.injective.ne h) := by
  apply Subtype.ext
  rfl

noncomputable def configRelabel {n : ℕ} (sigma : Equiv.Perm (Fin n)) : Config n ≃ Config n where
  toFun omega := fun e => ((omega e).1, (omega ((pairRelabel sigma).symm e)).2)
  invFun omega := fun e => ((omega e).1, (omega (pairRelabel sigma e)).2)
  left_inv omega := by
    funext e
    simp only [Equiv.symm_apply_apply, Prod.eta]
  right_inv omega := by
    funext e
    simp only [Equiv.apply_symm_apply, Prod.eta]

lemma configRelabel_first {n : ℕ} (sigma : Equiv.Perm (Fin n)) (omega : Config n) (e : Pair n) :
    (configRelabel sigma omega e).1 = (omega e).1 := rfl

lemma configRelabel_second {n : ℕ} (sigma : Equiv.Perm (Fin n)) (omega : Config n) (e : Pair n) :
    (configRelabel sigma omega e).2 = (omega ((pairRelabel sigma).symm e)).2 := rfl

lemma obs_relabel {n : ℕ} (sigma : Equiv.Perm (Fin n)) (omega : Config n) :
    obs sigma omega = obs 1 (configRelabel sigma omega) := by
  apply Prod.ext
  · change adjA omega = adjA (configRelabel sigma omega)
    funext i j
    unfold adjA
    split_ifs <;> rfl
  · change adjB sigma omega = adjB 1 (configRelabel sigma omega)
    funext i j
    change (if h : sigma.symm i = sigma.symm j then false
      else (omega (pairOf (sigma.symm i) (sigma.symm j) h)).2) =
      (if h : i = j then false else (configRelabel sigma omega (pairOf i j h)).2)
    by_cases h : i = j
    · subst j
      simp
    · simp only [h, sigma.symm.injective.ne h, dite_false, configRelabel_second,
        pairRelabel_symm_pairOf]

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

noncomputable def bitWeight (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

lemma qLaw_factor (q : ℝ) (a : Bool × Bool) :
    qLaw q a = bitWeight q a.1 * bitWeight q a.2 := by
  rcases a with ⟨a,b⟩
  cases a <;> cases b <;> simp [qLaw, bitWeight] <;> ring

lemma cfgLaw_q_relabel {n : ℕ} (q : ℝ) (sigma : Equiv.Perm (Fin n)) (omega : Config n) :
    cfgLaw (qLaw q) (configRelabel sigma omega) = cfgLaw (qLaw q) omega := by
  classical
  simp only [cfgLaw, qLaw_factor, configRelabel_first, configRelabel_second,
    Finset.prod_mul_distrib]
  congr 1
  exact (pairRelabel sigma).symm.prod_comp (fun e => bitWeight q (omega e).2)

lemma reference_obs_sum {n : ℕ} (q : ℝ) (sigma : Equiv.Perm (Fin n))
    (f : Obs n → ℝ) :
    (∑ omega : Config n, cfgLaw (qLaw q) omega * f (obs sigma omega)) =
      ∑ omega : Config n, cfgLaw (qLaw q) omega * f (obs 1 omega) := by
  classical
  calc
    _ = ∑ omega : Config n, cfgLaw (qLaw q) (configRelabel sigma omega) *
        f (obs 1 (configRelabel sigma omega)) := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [cfgLaw_q_relabel, ← obs_relabel]
    _ = _ := (configRelabel sigma).sum_comp
      (fun omega => cfgLaw (qLaw q) omega * f (obs 1 omega))

lemma cfgLaw_q_sum {n : ℕ} (q : ℝ) : ∑ omega : Config n, cfgLaw (qLaw q) omega = 1 := by
  exact prodLaw_sum (qLaw q) (qLaw_sum q)

lemma cfgLaw_q_nonneg {n : ℕ} {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (omega : Config n) : 0 ≤ cfgLaw (qLaw q) omega :=
  prodLaw_nonneg (qLaw q) (qLaw_nonneg hq hq1) omega

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma card_fixing_le {V : Type*} [Fintype V] [DecidableEq V] (F : Finset V) :
    (Finset.univ.filter (fun pi : Equiv.Perm V => ∀ i ∈ F, pi i = i)).card ≤
      (Fintype.card V - F.card).factorial := by
  classical
  let X := {pi : Equiv.Perm V // ∀ i ∈ F, pi i = i}
  have hpres (pi : X) (v : V) : pi.val v ∉ F ↔ v ∉ F := by
    constructor
    · intro h hv
      exact h (by rw [pi.property v hv]; exact hv)
    · intro h hv
      have hf := pi.property (pi.val v) hv
      have he : pi.val v = v := pi.val.injective hf
      exact h (he ▸ hv)
  let f : X → Equiv.Perm {v : V // v ∉ F} := fun pi => pi.val.subtypePerm (hpres pi)
  have hinj : Function.Injective f := by
    intro pi rho h
    apply Subtype.ext
    ext v
    by_cases hv : v ∈ F
    · rw [pi.property v hv, rho.property v hv]
    · have hh := congrArg (fun e : Equiv.Perm {v : V // v ∉ F} => (e ⟨v,hv⟩).val) h
      exact hh
  have hc := Fintype.card_le_of_injective f hinj
  have hcomp : Fintype.card {v : V // v ∉ F} = Fintype.card V - F.card := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_subtype, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Fintype.card_perm, hcomp] at hc
  simpa only [X, Fintype.card_subtype] using hc

lemma card_agreeing_subset_le {n : ℕ} (pi : Equiv.Perm (Fin n)) (F : Finset (Fin n)) :
    (Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => ∀ i ∈ F, pi i = rho i)).card ≤
      (n - F.card).factorial := by
  classical
  let X := {rho : Equiv.Perm (Fin n) // ∀ i ∈ F, pi i = rho i}
  let Y := {rho : Equiv.Perm (Fin n) // ∀ i ∈ F, rho i = i}
  let f : X → Y := fun rho => ⟨rho.val.trans pi.symm, by
    intro i hi
    change pi.symm (rho.val i) = i
    rw [← rho.property i hi, pi.symm_apply_apply]⟩
  have hinj : Function.Injective f := by
    intro rho sigma h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have hh := congrArg (fun z : Y => pi (z.val i)) h
    simpa only [f, Equiv.trans_apply, Equiv.apply_symm_apply] using hh
  have hc := Fintype.card_le_of_injective f hinj
  have hc' : (Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => ∀ i ∈ F, pi i = rho i)).card ≤
      (Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => ∀ i ∈ F, rho i = i)).card := by
    simpa only [X, Y, Fintype.card_subtype] using hc
  apply hc'.trans
  convert (card_fixing_le F) using 1
  all_goals first | rfl | simp only [Fintype.card_fin] | congr 1
  all_goals ext rho; simp only [Finset.mem_filter]

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

lemma card_many_agreements_le {n : ℕ} (pi : Equiv.Perm (Fin n)) (m : ℕ) :
    (Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => m ≤ matchCount pi rho)).card ≤
      n.choose m * (n - m).factorial := by
  classical
  let family := (Finset.univ : Finset (Fin n)).powersetCard m
  let agreeing := fun F : Finset (Fin n) =>
    Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => ∀ i ∈ F, pi i = rho i)
  have hsub : Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => m ≤ matchCount pi rho) ⊆
      family.biUnion agreeing := by
    intro rho hrho
    have hm : m ≤ (Finset.univ.filter (fun i => pi i = rho i)).card :=
      (Finset.mem_filter.mp hrho).2
    obtain ⟨F, hF, hcard⟩ := Finset.exists_subset_card_eq hm
    apply Finset.mem_biUnion.mpr
    refine ⟨F, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ F, hcard⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ rho, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hF hi)).2
  calc
    _ ≤ (family.biUnion agreeing).card := Finset.card_le_card hsub
    _ ≤ ∑ F ∈ family, (agreeing F).card := Finset.card_biUnion_le
    _ ≤ ∑ _F ∈ family, (n-m).factorial := by
      apply Finset.sum_le_sum
      intro F hF
      have hm := (Finset.mem_powersetCard.mp hF).2
      simpa only [agreeing, hm] using card_agreeing_subset_le pi F
    _ = _ := by simp [family]

lemma card_many_agreements_mul_factorial {n : ℕ} (pi : Equiv.Perm (Fin n))
    (m : ℕ) (hm : m ≤ n) :
    (Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => m ≤ matchCount pi rho)).card * m.factorial ≤
      n.factorial := by
  have h := Nat.mul_le_mul_right m.factorial (card_many_agreements_le pi m)
  have he : (n.choose m * (n-m).factorial) * m.factorial = n.factorial := by
    rw [mul_right_comm]
    exact Nat.choose_mul_factorial_mul_factorial hm
  exact h.trans_eq he

lemma uniform_agreement_probability {n : ℕ} (pi : Equiv.Perm (Fin n))
    (m : ℕ) (hm : m ≤ n) :
    (1 / (n.factorial : ℝ)) * ∑ rho : Equiv.Perm (Fin n),
      (if m ≤ matchCount pi rho then (1 : ℝ) else 0) ≤ 1 / (m.factorial : ℝ) := by
  classical
  have hs : (∑ rho : Equiv.Perm (Fin n), (if m ≤ matchCount pi rho then (1 : ℝ) else 0)) =
      ((Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => m ≤ matchCount pi rho)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hs]
  have hc : ((Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => m ≤ matchCount pi rho)).card : ℝ) *
      (m.factorial : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast card_many_agreements_mul_factorial pi m hm
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < m.factorial)).mpr
  have hn : (0 : ℝ) < n.factorial := by positivity
  calc
    _ = (((Finset.univ.filter (fun rho : Equiv.Perm (Fin n) => m ≤ matchCount pi rho)).card : ℝ) *
        (m.factorial : ℝ)) / (n.factorial : ℝ) := by ring
    _ ≤ 1 := (div_le_one hn).mpr hc

end GraphAlignment.Impossible.GAFresh
end

section

open scoped BigOperators
namespace GraphAlignment.Impossible.GAFresh

noncomputable def referenceOutput {n : ℕ} (q : ℝ) (alg : Alg n)
    (pi : Equiv.Perm (Fin n)) : ℝ :=
  ∑ omega : Config n, cfgLaw (qLaw q) omega * alg.k (obs 1 omega) pi

lemma referenceOutput_nonneg {n : ℕ} {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (alg : Alg n) (pi : Equiv.Perm (Fin n)) : 0 ≤ referenceOutput q alg pi := by
  exact Finset.sum_nonneg fun omega _ =>
    mul_nonneg (cfgLaw_q_nonneg hq hq1 omega) (alg.nonneg _ _)

lemma referenceOutput_sum {n : ℕ} (q : ℝ) (alg : Alg n) :
    ∑ pi, referenceOutput q alg pi = 1 := by
  classical
  unfold referenceOutput
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, alg.sum_one, mul_one]
  exact cfgLaw_q_sum q

lemma reference_matchMass_eq {n : ℕ} (q : ℝ) (m : ℕ) (alg : Alg n) :
    matchMass (qLaw q) m alg = ∑ pi, referenceOutput q alg pi *
      ((1 / (n.factorial : ℝ)) * ∑ sigma, if m ≤ matchCount pi sigma then (1 : ℝ) else 0) := by
  classical
  unfold matchMass
  simp only [Fintype.sum_prod_type, tripleLaw]
  calc
    _ = ∑ sigma : Equiv.Perm (Fin n), ∑ pi : Equiv.Perm (Fin n),
        ((1 / (n.factorial : ℝ)) *
          (∑ omega : Config n, cfgLaw (qLaw q) omega * alg.k (obs sigma omega) pi)) *
            (if m ≤ matchCount pi sigma then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pi _
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ = ∑ sigma : Equiv.Perm (Fin n), ∑ pi : Equiv.Perm (Fin n),
        ((1 / (n.factorial : ℝ)) * referenceOutput q alg pi) *
          (if m ≤ matchCount pi sigma then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro sigma _
      apply Finset.sum_congr rfl
      intro pi _
      rw [reference_obs_sum q sigma (fun o => alg.k o pi)]
      rfl
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pi _
      rw [← Finset.mul_sum]
      ring

lemma reference_matchMass_bound {n : ℕ} {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : m ≤ n) (alg : Alg n) :
    matchMass (qLaw q) m alg ≤ 1 / (m.factorial : ℝ) := by
  classical
  rw [reference_matchMass_eq]
  calc
    _ ≤ ∑ pi, referenceOutput q alg pi * (1 / (m.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro pi _
      exact mul_le_mul_of_nonneg_left (uniform_agreement_probability pi m hm)
        (referenceOutput_nonneg hq hq1 alg pi)
    _ = _ := by rw [← Finset.sum_mul, referenceOutput_sum, one_mul]

end GraphAlignment.Impossible.GAFresh
end

section

open Filter Topology
namespace GraphAlignment.Impossible.GAFresh

lemma log_factorial_lower (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * Real.log m - m ≤ Real.log (m.factorial : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h := Stirling.le_log_factorial_stirling hm0
  linarith

lemma floor_scaled_log_factorial (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ Nat.floor (c * n) ≤ n ∧
      (c/8) * n * Real.log n ≤ Real.log ((Nat.floor (c*n)).factorial : ℝ) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcn := hn.const_mul_atTop hc
  have hln := Real.tendsto_log_atTop.comp hn
  filter_upwards [eventually_ge_atTop (1 : ℕ), hcn.eventually_ge_atTop 2,
    hln.eventually_ge_atTop 4, hln.eventually_ge_atTop (-2 * Real.log (c/2))] with n hn1 hcn2 hln4 hlnc
  simp only [Function.comp_apply] at hln4 hlnc
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcn0 : 0 ≤ c * (n : ℝ) := by positivity
  have hf := Nat.floor_le hcn0
  have hfl := Nat.lt_floor_add_one (c * (n : ℝ))
  have hmlo : c/2 * (n : ℝ) ≤ (Nat.floor (c*n) : ℝ) := by linarith
  have hmpos : 0 < (Nat.floor (c*n) : ℝ) := lt_of_lt_of_le (by positivity) hmlo
  have hm1 : 1 ≤ Nat.floor (c*n) := by exact_mod_cast (show 0 < Nat.floor (c*n) by exact_mod_cast hmpos)
  have hmupper : Nat.floor (c*n) ≤ n := by
    exact_mod_cast (hf.trans (mul_le_of_le_one_left hnR.le hc1))
  have hlogmul : Real.log (c/2 * (n : ℝ)) = Real.log (c/2) + Real.log n :=
    Real.log_mul (by positivity) (ne_of_gt hnR)
  have hloglo : Real.log (n : ℝ) / 2 ≤ Real.log (Nat.floor (c*n) : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < c/2 * (n : ℝ)) hmlo
    rw [hlogmul] at h
    linarith
  have ha : (Nat.floor (c*n) : ℝ) * (Real.log (n : ℝ) / 2 - 1) ≤
      (Nat.floor (c*n) : ℝ) * Real.log (Nat.floor (c*n) : ℝ) - Nat.floor (c*n) := by
    nlinarith [mul_nonneg hmpos.le (sub_nonneg.mpr hloglo)]
  have hb : (Nat.floor (c*n) : ℝ) * (Real.log (n : ℝ) / 4) ≤
      (Nat.floor (c*n) : ℝ) * (Real.log (n : ℝ) / 2 - 1) := by
    nlinarith [mul_nonneg hmpos.le (show 0 ≤ Real.log (n : ℝ)/4-1 by linarith)]
  have hd := mul_le_mul_of_nonneg_right hmlo (show 0 ≤ Real.log (n : ℝ)/4 by linarith)
  refine ⟨hn0, hmupper, ?_⟩
  have he := log_factorial_lower (Nat.floor (c*n)) hm1
  nlinarith

end GraphAlignment.Impossible.GAFresh
end

section

open Filter Topology
namespace GraphAlignment.Impossible.GAFresh

lemma normalized_information_tendsto (D α : ℕ → ℝ)
    (hD0 : ∀ n, 0 ≤ D n) (hα : ∀ n, 0 < α n ∧ α n < 1)
    (hD : Tendsto (fun n : ℕ => D n / α n / (Real.log n / n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * D n / Real.log n) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hD
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (hD0 n)) hlog.le
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have ha0 : 0 < α n := (hα n).1
    have hd0 : 0 ≤ D n := hD0 n
    have hratio : 0 ≤ D n / α n / (Real.log n / n) := by positivity
    have heq : (n : ℝ) * D n / Real.log n =
        α n * (D n / α n / (Real.log n / n)) := by
      field_simp
    rw [heq]
    exact mul_le_of_le_one_left hratio (hα n).2.le

lemma failure_tendsto_of_factorial_information (D α f : ℕ → ℝ)
    (hD0 : ∀ n, 0 ≤ D n) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1)
    (hα : ∀ n, 0 < α n ∧ α n < 1)
    (hαc : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ α n)
    (hD : Tendsto (fun n : ℕ => D n / α n / (Real.log n / n)) atTop (𝓝 0))
    (hfinite : ∀ n m : ℕ, 0 < n → m ≤ n → (m : ℝ) ≤ α n * n →
      (1-f n) * Real.log (m.factorial : ℝ) ≤ (n : ℝ)^2 * D n + 1) :
    Tendsto f atTop (𝓝 1) := by
  obtain ⟨c, hc, hca⟩ := hαc
  let b := min c (1/2 : ℝ)
  have hb : 0 < b := lt_min hc (by norm_num)
  have hb1 : b ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hbc : b ≤ c := min_le_left _ _
  have hgrowth := floor_scaled_log_factorial b hb hb1
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hln := Real.tendsto_log_atTop.comp hn
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.atTop_mul_atTop₀ hln)
  have hnorm := normalized_information_tendsto D α hD0 hα hD
  have hbound : Tendsto (fun n : ℕ => (8/b) *
      ((n : ℝ) * D n / Real.log n + 1 / ((n : ℝ) * Real.log n))) atTop (𝓝 0) := by
    simpa using (hnorm.add hinv).const_mul (8/b)
  have hsuccess : Tendsto (fun n => 1-f n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => sub_nonneg.mpr (hf n).2) _ hbound
    filter_upwards [hgrowth, hca, eventually_ge_atTop (2 : ℕ)] with n hg hcan hn2
    have hn0 := hg.1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    let m := Nat.floor (b * (n : ℝ))
    have hmα : (m : ℝ) ≤ α n * n :=
      (Nat.floor_le (by positivity : 0 ≤ b * (n : ℝ))).trans
        (mul_le_mul_of_nonneg_right (hbc.trans hcan) hnR.le)
    have hfin := hfinite n m hn0 hg.2.1 hmα
    have hlow := mul_le_mul_of_nonneg_left hg.2.2 (sub_nonneg.mpr (hf n).2)
    have hden : 0 < (b/8) * (n : ℝ) * Real.log n := by positivity
    calc
      1-f n ≤ ((n : ℝ)^2 * D n + 1) / ((b/8) * n * Real.log n) := by
        apply (le_div_iff₀ hden).mpr
        exact hlow.trans hfin
      _ = (8/b) * ((n : ℝ) * D n / Real.log n + 1 / ((n : ℝ) * Real.log n)) := by
        field_simp
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hsuccess
  simpa only [sub_sub_cancel, sub_zero] using h

end GraphAlignment.Impossible.GAFresh
end

section

namespace GraphAlignment.Impossible

open Filter Topology

theorem GAFresh.impossibility_theorem (q s α : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n) (hqs : ∀ n, q n < s n) (hs : ∀ n, s n ≤ 1)
    (hα : ∀ n, 0 < α n ∧ α n < 1) (hαc : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ α n)
    (hD : Tendsto (fun n : ℕ => klPQ (q n) (s n) / α n / (Real.log n / n)) atTop (𝓝 0))
    (alg : ∀ n, Alg n) :
    Tendsto (fun n => failProb (q n) (s n) (α n) (alg n)) atTop (𝓝 1)  := by
  apply GAFresh.failure_tendsto_of_factorial_information
    (fun n => klPQ (q n) (s n)) α (fun n => failProb (q n) (s n) (α n) (alg n))
    (fun n => GAFresh.klPQ_nonneg (hq n) (hqs n) (hs n))
    (fun n => GAFresh.failProb_bounds (hq n) (hqs n).le (hs n) (α n) (alg n))
    hα hαc hD
  intro n m hn hm hma
  exact GAFresh.finite_failure_information (hq n) (hqs n) (hs n) hn hma (alg n)
    (GAFresh.reference_matchMass_bound (hq n) ((hqs n).le.trans (hs n)) m hm (alg n))

end GraphAlignment.Impossible
end

open GraphAlignment.Impossible Filter Topology

theorem solution (q s α : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n) (hqs : ∀ n, q n < s n) (hs : ∀ n, s n ≤ 1)
    (hα : ∀ n, 0 < α n ∧ α n < 1) (hαc : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ α n)
    (hD : Tendsto (fun n : ℕ => klPQ (q n) (s n) / α n / (Real.log n / n)) atTop (𝓝 0))
    (alg : ∀ n, Alg n) :
    Tendsto (fun n => failProb (q n) (s n) (α n) (alg n)) atTop (𝓝 1) := by
  exact GAFresh.impossibility_theorem q s α hq hqs hs hα hαc hD alg
