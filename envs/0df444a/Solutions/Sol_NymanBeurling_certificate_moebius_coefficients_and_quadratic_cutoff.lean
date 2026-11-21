-- Prove2me | solution 1 for NymanBeurling.certificate_moebius_coefficients_and_quadratic_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:52:33.578262+00:00
-- url     : https://prove2.me/submissions/ba099d14-3b51-48e8-a9ac-b76752bc0b9d

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Sqrt


open Finset



private lemma inverse_square_budget (n : ℕ) :
    ∑ d ∈ range (n+1), (1:ℚ)/(d:ℚ)^2 ≤ 2 - 2/((n:ℚ)+1) := by
  induction n with
  | zero => norm_num
  | succ n h =>
    rw [sum_range_succ]
    push_cast
    apply (add_le_add h (le_refl _)).trans
    have ha : (0:ℚ) < (n:ℚ)+1 := by positivity
    have hb : (0:ℚ) < (n:ℚ)+1+1 := by positivity
    field_simp
    nlinarith [Nat.cast_nonneg (α:=ℚ) n]

private theorem divisor_square_budget (n : ℕ) :
    ∑ d ∈ n.divisors, (d:ℚ)^2 ≤ 2*(n:ℚ)^2 := by
  rw [← Nat.sum_div_divisors n (fun d => (d:ℚ)^2)]
  have hc (d : ℕ) (hd : d ∈ n.divisors) : (↑(n/d):ℚ)^2=(n:ℚ)^2*(1/(d:ℚ)^2) := by
    have hp := Nat.pos_of_mem_divisors hd
    have hh : (↑(n/d):ℚ)*(d:ℚ)=(n:ℚ) := by exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    have hd0 : (0:ℚ)<d := by exact_mod_cast hp
    field_simp
    nlinarith [congrArg (fun x : ℚ => x^2) hh]
  rw [sum_congr rfl hc, ← mul_sum, mul_comm (2:ℚ)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hsub : n.divisors ⊆ range (n+1) := by
    intro d hd; exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)))
  calc _ ≤ ∑ d ∈ range (n+1), (1:ℚ)/(d:ℚ)^2 :=
          sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
       _ ≤ 2-2/((n:ℚ)+1) := inverse_square_budget n
       _ ≤ _ := sub_le_self _ (by positivity)

namespace BagchiCertificate

def residual (c : ℕ →₀ ℚ) (m : ℕ) : ℚ :=
  1 - ∑ k ∈ c.support, c k * ((m % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ)

def mass (c : ℕ →₀ ℚ) : ℚ := 1 + ∑ k ∈ c.support, |c k|

def term (c : ℕ →₀ ℚ) (i : ℕ) : ℚ :=
  residual c (i+1)^2 / (((i:ℚ)+1)*((i:ℚ)+2))

def cost (c : ℕ →₀ ℚ) (H : ℕ) : ℚ := ∑ n ∈ range H, term c n + (mass c)^2/((H:ℚ)+1)

private lemma mass_nonneg (c : ℕ →₀ ℚ) : 0 ≤ mass c := by unfold mass; positivity
private lemma term_nonneg (c : ℕ →₀ ℚ) (n : ℕ) : 0 ≤ term c n := by unfold term; positivity

private lemma mod_step {n u : ℕ} (hu : 2 ≤ u) (h : ¬u ∣ n+1) :
    (n+1)%u = n%u+1 := by
  have hone : 1%u = 1 := Nat.mod_eq_of_lt (by omega)
  have hne : (n+1)%u ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
  have hb : n % u < u := Nat.mod_lt _ (by omega)
  have hlt : n%u+1 < u := by
    by_contra! hn
    have he : n%u+1=u := by omega
    apply hne
    rw [Nat.add_mod, hone, he, Nat.mod_self]
  simpa only [hone] using Nat.add_mod_of_add_mod_lt (a:=n) (b:=1) (c:=u) (by simpa only [hone] using hlt)

private lemma residual_delta (c : ℕ →₀ ℚ) (r : ℕ) :
    residual c (r+1) - residual c r =
      residual c 1 - 1 + ∑ j ∈ c.support, if (j+2) ∣ (r+1) then c j else 0 := by
  classical
  let T (m j : ℕ) := c j * ((m % (j+2) : ℕ) : ℚ) / ((j+2 : ℕ) : ℚ)
  have hi (j : ℕ) : T 1 j + T r j - T (r+1) j =
      if (j+2) ∣ (r+1) then c j else 0 := by
    have he : 1 % (j+2) = 1 := Nat.mod_eq_of_lt (by omega)
    by_cases h : (j+2) ∣ (r+1)
    · have hm0 : (r+1) % (j+2) = 0 := Nat.mod_eq_zero_of_dvd h
      have hm1 : r % (j+2) + 1 = j+2 := by
        have hu := Nat.mod_lt r (show 0 < j+2 by omega)
        by_contra hne
        have hlt : r % (j+2)+1 < j+2 := by omega
        have hz := Nat.add_mod_of_add_mod_lt (a:=r) (b:=1) (c:=j+2) (by simpa [he] using hlt)
        rw [hm0, he] at hz
        omega
      simp only [T, he, hm0, if_pos h, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one,
        zero_div, sub_zero]
      have hmQ : (r % (j+2) : ℕ) + (1 : ℚ) = (j+2 : ℕ) := by exact_mod_cast hm1
      have hneq : ((j+2 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [← add_div, div_eq_iff hneq, ←hmQ]
      ring
    · have hm := mod_step (u:=j+2) (by omega) h
      simp only [T, he, hm, Nat.cast_add, Nat.cast_one, mul_one, if_neg h]
      ring
  have hsum := sum_congr (s₁:=c.support) rfl (fun j _ => hi j)
  simp only [sum_sub_distrib, sum_add_distrib] at hsum
  change (1-∑ j ∈ c.support, T (r+1) j) - (1-∑ j ∈ c.support, T r j) =
    (1-∑ j ∈ c.support, T 1 j) - 1 + _
  linarith

private lemma all_coefficient_identity (c : ℕ →₀ ℚ) (n : ℕ) (hn : 2 ≤ n) :
    c (n-2) + (ArithmeticFunction.moebius n : ℚ) =
      (∑ d ∈ n.divisors.filter (1 < ·), (ArithmeticFunction.moebius (n/d):ℚ) * residual c d) -
      (∑ d ∈ n.divisors.filter (1 < ·), (ArithmeticFunction.moebius (n/d):ℚ) * residual c (d-1)) +
      (ArithmeticFunction.moebius n : ℚ) * residual c 1 := by
  classical
  let f (i : ℕ) : ℚ := (if 1 = i then residual c 1 - 1 else 0) +
    ∑ j ∈ c.support, if j+2 = i then c j else 0
  let g (d : ℕ) : ℚ := residual c d - residual c (d-1)
  have hg (m : ℕ) (hm : 0 < m) : ∑ i ∈ m.divisors, f i = g m := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp only [f, sum_add_distrib, g, Nat.succ_sub_one]
    rw [sum_comm (s:= (r+1).divisors) (t:=c.support)]
    simpa [Nat.mem_divisors, Nat.succ_ne_zero] using (residual_delta c r).symm
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f:=f) (g:=g)).mp hg n (by omega)
  rw [Nat.sum_divisorsAntidiagonal' (f:=fun x y => (ArithmeticFunction.moebius x : ℚ) * g y)] at hinv
  have hf : f n = c (n-2) := by
    have he (j : ℕ) : j+2 = n ↔ j=n-2 := by omega
    simp only [f, if_neg (by omega : ¬1=n), zero_add, he]
    by_cases h : n-2 ∈ c.support
    · simp [h]
    · simp [h, Finsupp.notMem_support_iff.mp h]
  rw [hf] at hinv
  let S := n.divisors.filter (1 < ·)
  have hsplit : n.divisors = insert 1 S := by
    ext d
    simp only [S, mem_insert, mem_filter]
    constructor
    · intro hd
      have hh := Nat.pos_of_mem_divisors hd
      by_cases h : d=1
      · exact Or.inl h
      · exact Or.inr ⟨hd,by omega⟩
    · rintro (rfl|⟨h,_⟩)
      · exact Nat.one_mem_divisors.mpr (by omega)
      · exact h
  have hnot : 1 ∉ S := by simp [S]
  rw [hsplit, sum_insert hnot] at hinv
  have hzero : residual c 0 = 1 := by simp [residual]
  simp only [g, Nat.div_one, Nat.sub_self, hzero, mul_sub, sum_sub_distrib] at hinv
  change _ = (∑ d ∈ S, _) - (∑ d ∈ S, _) + _
  linarith

private lemma sum_le_cost (c : ℕ →₀ ℚ) (H : ℕ) (u : Finset ℕ) (hu : u ⊆ range H) :
    ∑ i ∈ u, term c i ≤ cost c H := by
  apply (sum_le_sum_of_subset_of_nonneg hu (fun i _ _ => term_nonneg c i)).trans
  unfold cost
  linarith [div_nonneg (sq_nonneg (mass c)) (show 0≤(H:ℚ)+1 by positivity)]

private lemma selected_residual_bound (c : ℕ →₀ ℚ) (H n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ n.divisors) (shift : ℕ → ℕ)
    (hinj : Set.InjOn shift (S : Set ℕ)) (hH : ∀ d ∈ S, shift d < H)
    (hw : ∀ d ∈ S, ((shift d:ℚ)+1)*((shift d:ℚ)+2) ≤ 2*(d:ℚ)^2)
    (w : ℕ → ℚ) (habs : ∀ d ∈ S, |w d| ≤ 1) :
    (∑ d ∈ S, w d * residual c (shift d+1))^2 ≤ 4*(n:ℚ)^2*cost c H := by
  classical
  let F (d : ℕ) := w d * residual c (shift d+1)
  let G (d : ℕ) : ℚ := ((shift d:ℚ)+1)*((shift d:ℚ)+2)
  have hp (d : ℕ) : 0 < G d := by dsimp [G]; positivity
  have hcost : 0 ≤ cost c H := by
    unfold cost; exact add_nonneg (sum_nonneg (fun i _ => term_nonneg c i)) (by positivity)
  rcases S.eq_empty_or_nonempty with rfl|hne
  · simp; positivity
  have hgs : 0 < ∑ d ∈ S, G d := Finset.sum_pos (fun d _ => hp d) hne
  have hG : ∑ d ∈ S, G d ≤ 4*(n:ℚ)^2 := by
    have hsubset := sum_le_sum_of_subset_of_nonneg hS (by intro d _ _; exact sq_nonneg (d:ℚ))
    have hdiv := divisor_square_budget n
    have hsum := sum_le_sum hw
    rw [←mul_sum] at hsum
    change ∑ d ∈ S, G d ≤ 4*(n:ℚ)^2
    linarith
  have hcost' : ∑ d ∈ S, (F d)^2/G d ≤ cost c H := by
    calc _ ≤ ∑ d ∈ S, term c (shift d) := by
              apply sum_le_sum
              intro d hd
              change (w d * residual c (shift d+1))^2 / G d ≤ (residual c (shift d+1))^2 / G d
              apply div_le_div_of_nonneg_right _ (hp d).le
              rw [mul_pow]
              apply mul_le_of_le_one_left (sq_nonneg _)
              have h := abs_le.mp (habs d hd)
              nlinarith [mul_nonneg (show 0 ≤ 1-w d by linarith [h.2]) (show 0 ≤ 1+w d by linarith [h.1])]
         _ = ∑ i ∈ S.image shift, term c i := (sum_image hinj).symm
         _ ≤ cost c H := sum_le_cost c H _ (by
              intro x hx; obtain ⟨d,hd,rfl⟩ := mem_image.mp hx; exact mem_range.mpr (hH d hd))
  have h := sq_sum_div_le_sum_sq_div S F (g:=G) (fun d _ => hp d)
  have h2 := (div_le_iff₀ hgs).mp (h.trans hcost')
  exact h2.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hG hcost)

private lemma all_coefficient_from_identity (c : ℕ →₀ ℚ) (n H : ℕ) (hn : 2 ≤ n)
    (hident : c (n-2) + (ArithmeticFunction.moebius n : ℚ) =
      (∑ d ∈ n.divisors.filter (1 < ·), (ArithmeticFunction.moebius (n/d):ℚ) * residual c d) -
      (∑ d ∈ n.divisors.filter (1 < ·), (ArithmeticFunction.moebius (n/d):ℚ) * residual c (d-1)) +
      (ArithmeticFunction.moebius n : ℚ) * residual c 1) :
    (c (n-2) + (ArithmeticFunction.moebius n : ℚ))^2 ≤ 30*(n:ℚ)^2*cost c H := by
  classical
  have hmn (i : ℕ) : |(ArithmeticFunction.moebius i : ℚ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=i))
  have hc : 0 ≤ cost c H := by
    unfold cost; exact add_nonneg (sum_nonneg (fun i _ => term_nonneg c i)) (by positivity)
  have hnq : (2:ℚ) ≤ n := by exact_mod_cast hn
  by_cases hh : H < n
  · have hb : |c (n-2) + (ArithmeticFunction.moebius n : ℚ)| ≤ mass c := by
      refine (abs_add_le ..).trans ?_
      rw [mass, add_comm (1:ℚ)]
      refine add_le_add ?_ (hmn n)
      by_cases hs : n-2 ∈ c.support
      · exact single_le_sum (fun i _ => abs_nonneg (c i)) hs
      · simp [Finsupp.notMem_support_iff.mp hs, sum_nonneg (fun i _ => abs_nonneg (c i))]
    have hsq : (c (n-2)+(ArithmeticFunction.moebius n:ℚ))^2 ≤ (mass c)^2 := by
      nlinarith [sq_abs (c (n-2)+(ArithmeticFunction.moebius n:ℚ)),
        mul_nonneg (sub_nonneg.mpr hb) (add_nonneg (mass_nonneg c) (abs_nonneg (c (n-2)+(ArithmeticFunction.moebius n:ℚ))))]
    have ht : (mass c)^2/((H:ℚ)+1) ≤ cost c H := by
      unfold cost
      linarith [sum_nonneg (s:=range H) (fun i _ => term_nonneg c i)]
    have hr : (H:ℚ)+1 ≤ n := by exact_mod_cast (show H+1≤n by omega)
    have hden : (H:ℚ)+1 ≤ 30*(n:ℚ)^2 := by nlinarith [sq_nonneg ((n:ℚ)-1)]
    exact hsq.trans <| ((div_le_iff₀ (by positivity)).mp ht).trans
      (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hden hc)
  let S := n.divisors.filter (1 < ·)
  let w (d : ℕ) : ℚ := ArithmeticFunction.moebius (n/d)
  have hS : S ⊆ n.divisors := filter_subset .. 
  have hn0 : n ≠ 0 := by omega
  have hmem {d : ℕ} (hd : d ∈ S) : 2 ≤ d ∧ d ≤ n := by
    obtain ⟨h,u⟩ := mem_filter.mp hd
    exact ⟨u,Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors h)⟩
  have hh0 (j : ℕ) (hj : j ≤ 2) (hj' : 1 ≤ j) :
      (∑ d ∈ S, w d * residual c (d-j+1))^2 ≤ 4*(n:ℚ)^2*cost c H := by
    apply selected_residual_bound _ _ _ _ hS
    · intro x hx y hy h
      change x-j=y-j at h
      have := (hmem hx).1; have := (hmem hy).1; omega
    · intro d hd; obtain ⟨hl,hu⟩:=hmem hd; omega
    · intro d hd
      have hl := (hmem hd).1
      rw [Nat.cast_sub (by omega : j≤d)]
      have hjq : (1:ℚ) ≤ j := by exact_mod_cast hj'
      have hjq' : (j:ℚ) ≤ 2 := by exact_mod_cast hj
      have hdq : (2:ℚ) ≤ d := by exact_mod_cast hl
      have hjd : (j:ℚ) ≤ d := by linarith
      have hp1 : (d:ℚ) - j + 1 ≤ d := by linarith
      have hp2 : (d:ℚ) - j + 2 ≤ 2*d := by linarith
      have hmul := mul_le_mul hp1 hp2 (by linarith) (by positivity)
      nlinarith
    · intro d _; exact hmn _
  let A := ∑ d ∈ S, w d * residual c d
  let B := ∑ d ∈ S, w d * residual c (d-1)
  let Z := (ArithmeticFunction.moebius n:ℚ) * residual c 1
  have hA : A^2 ≤ 4*(n:ℚ)^2*cost c H := by
    have r := hh0 1 (by decide) (by decide)
    convert r using 2
    apply sum_congr rfl; intro d hd
    rw [show d-1+1=d by have := (hmem hd).1; omega]
  have hB : B^2 ≤ 4*(n:ℚ)^2*cost c H := by
    have r := hh0 2 (by decide) (by decide)
    convert r using 2
    apply sum_congr rfl; intro d hd
    rw [show d-2+1=d-1 by have := (hmem hd).1; omega]
  have hZ : Z^2 ≤ 2*cost c H := by
    have ht := sum_le_cost c H {0} (by intro i hi; simp at hi; subst i; exact mem_range.mpr (by omega))
    norm_num [term] at ht
    dsimp only [Z]; rw [mul_pow]
    have hu := abs_le.mp (hmn n)
    have hμ : (ArithmeticFunction.moebius n:ℚ)^2 ≤ 1 := by
      nlinarith [mul_nonneg (show 0≤1-(ArithmeticFunction.moebius n:ℚ) by linarith [hu.2])
        (show 0≤1+(ArithmeticFunction.moebius n:ℚ) by linarith [hu.1])]
    refine (mul_le_of_le_one_left (sq_nonneg _) hμ).trans ?_; linarith
  change c (n-2) + (ArithmeticFunction.moebius n:ℚ) = A-B+Z at hident
  rw [hident]
  have hn2 : (1:ℚ) ≤ (n:ℚ)^2 := by nlinarith [sq_nonneg ((n:ℚ)-1)]
  nlinarith [sq_nonneg (A+B),sq_nonneg (A-Z),sq_nonneg (B+Z),mul_nonneg (sub_nonneg.mpr hn2) hc]

end BagchiCertificate


open Finset

private theorem reciprocal_squares_from_two_bound (N : ℕ) :
    (∑ i ∈ range N, 1 / ((i : ℝ) + 2)^2) ≤ 3 / 4 := by
  have h (k : ℕ) : (∑ i ∈ range (k+1), 1 / ((i : ℝ)+2)^2) + 1/((k : ℝ)+2) ≤ 3/4 := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [sum_range_succ]
      push_cast
      have htel : 1/((k : ℝ)+3)^2 + 1/((k : ℝ)+3) ≤ 1/((k : ℝ)+2) := by
        field_simp
        nlinarith
      rw [show (k : ℝ) + 1 + 2 = k + 3 by ring]
      linarith
  cases N with
  | zero => norm_num
  | succ k => linarith [h k, show 0 ≤ 1 / ((k : ℝ)+2) by positivity]

/-- At least one quarter of the integers from one through `N` are squarefree. -/
private theorem quarter_le_squarefree_count (N : ℕ) :
    N ≤ 4 * ((range N).filter fun k ↦ Squarefree (k+1)).card := by
  classical
  let bad := (range N).filter fun k ↦ ¬ Squarefree (k+1)
  let multiples (i : ℕ) := (range N).filter fun k ↦ (i+2)^2 ∣ k+1
  have hcover : bad ⊆ (range N).biUnion multiples := by
    intro k hk
    obtain ⟨hkN, hbad⟩ := mem_filter.mp hk
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push Not at hbad
    obtain ⟨p, hp, hdvd⟩ := hbad
    have hpk : p ≤ k+1 := Nat.le_of_dvd (Nat.succ_pos _) ((dvd_mul_right p p).trans hdvd)
    have hp2 := hp.two_le
    have hkn := mem_range.mp hkN
    refine mem_biUnion.mpr ⟨p-2, mem_range.mpr (by omega), mem_filter.mpr ⟨hkN, ?_⟩⟩
    rw [Nat.sub_add_cancel hp2, pow_two]
    exact hdvd
  have hnat : bad.card ≤ ∑ i ∈ range N, N / (i+2)^2 := by
    exact (card_le_card hcover).trans <| card_biUnion_le.trans <| sum_le_sum (fun i _ ↦ (Nat.card_multiples N ((i+2)^2)).le)
  have hreal : (bad.card : ℝ) ≤ (N : ℝ)*(3/4) := by
    calc (bad.card : ℝ) ≤ (∑ i ∈ range N, N / (i+2)^2 : ℕ) := by exact_mod_cast hnat
         _ = ∑ i ∈ range N, ((N / (i+2)^2 : ℕ) : ℝ) := by norm_cast
         _ ≤ ∑ i ∈ range N, (N : ℝ) * (1/((i : ℝ)+2)^2) := by
           refine sum_le_sum fun i _ ↦ ?_
           rw [mul_one_div]
           have he : (((i+2)^2 : ℕ) : ℝ) = ((i : ℝ)+2)^2 := by norm_cast
           rw [← he]
           exact Nat.cast_div_le
         _ = (N : ℝ) * ∑ i ∈ range N, 1 / ((i : ℝ)+2)^2 := (mul_sum ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_squares_from_two_bound N) (by positivity)
  have htotal : ((range N).filter fun k ↦ Squarefree (k+1)).card + bad.card = N := by
    simpa [bad] using (card_filter_add_card_filter_not (s := range N) (fun k ↦ Squarefree (k+1)))
  have hreal' : (N : ℝ) ≤ 4 * (((range N).filter fun k ↦ Squarefree (k+1)).card : ℝ) := by
    have htot : (((range N).filter fun k ↦ Squarefree (k+1)).card : ℝ) + bad.card = N := by exact_mod_cast htotal
    linarith
  exact_mod_cast hreal'



open Finset

private theorem quadratic_budget_from_all_coefficients (c : ℕ →₀ ℚ) (J H : ℕ) (cost : ℚ)
    (hcost : cost < 1/((J:ℚ)+1))
    (htail : (1 + ∑ k ∈ c.support, |c k|)^2/((H:ℚ)+1) ≤ cost)
    (hcoeff : ∀ n : ℕ, 2 ≤ n → (c (n-2)+(ArithmeticFunction.moebius n:ℚ))^2 ≤ 30*(n:ℚ)^2*cost)
    (hdensity : ∀ R : ℕ, R ≤ 4 * ((range R).filter (fun k => Squarefree (k+1))).card) :
    (J+1)^2 < 7680*(H+1) := by
  classical
  let Y := (J+1)/120
  let R := Y.sqrt
  have hr0 : 120*R^2 ≤ J+1 := by
    calc 120*R^2 ≤ 120*Y := Nat.mul_le_mul_left _ (Nat.sqrt_le' _)
         _ ≤ _ := by dsimp [Y]; simpa [mul_comm] using Nat.div_mul_le_self (J+1) 120
  have hr1 : J+1 < 120*(R+1)^2 := by
    have h : Y < (R+1)^2 := Nat.lt_succ_sqrt' Y
    have h' := (Nat.div_lt_iff_lt_mul (by decide : 0<120)).mp h
    simpa [mul_comm] using h'
  let Q := (range R).filter (fun k => Squarefree (k+1))
  let S := Q.erase 0
  have hQ : Q.card ≤ S.card+1 := by
    by_cases hz : 0 ∈ Q
    · exact (card_erase_add_one hz).symm.le
    · simp [S,erase_eq_of_notMem hz]
  have hj : (0:ℚ) < (J:ℚ)+1 := by positivity
  have hstrong (k : ℕ) (hk : k ∈ S) : (1/2:ℚ) < |c (k-1)| := by
    obtain ⟨h0,hQ⟩ := mem_erase.mp hk
    obtain ⟨hkR,hsq⟩ := mem_filter.mp hQ
    have hnk : k+1 ≤ R := mem_range.mp hkR
    have hnk2 : 2 ≤ k+1 := by omega
    have hr : 120*(k+1)^2 ≤ J+1 := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnk 2)).trans hr0
    have hrat : 120*((k:ℚ)+1)^2 ≤ (J:ℚ)+1 := by exact_mod_cast hr
    have hc := hcoeff (k+1) hnk2
    rw [show k+1-2=k-1 by omega] at hc
    push_cast at hc
    have hsmall : (c (k-1)+(ArithmeticFunction.moebius (k+1):ℚ))^2 < 1/4 := by
      apply hc.trans_lt
      calc 30*((k:ℚ)+1)^2*cost < 30*((k:ℚ)+1)^2/((J:ℚ)+1) := by
                simpa [div_eq_mul_inv] using mul_lt_mul_of_pos_left hcost (show 0<30*((k:ℚ)+1)^2 by positivity)
           _ ≤ 1/4 := (div_le_iff₀ hj).mpr (by linarith)
    have hab : |(ArithmeticFunction.moebius (k+1):ℚ)| = 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq
    have hlin := abs_sub (c (k-1)+(ArithmeticFunction.moebius (k+1):ℚ)) (c (k-1))
    rw [add_sub_cancel_left,hab] at hlin
    have hax : |c (k-1)+(ArithmeticFunction.moebius (k+1):ℚ)| < 1/2 := by
      apply (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mp
      rw [sq_abs]
      norm_num
      exact hsmall
    linarith
  let i (k : ℕ) := k-1
  have hinj : Set.InjOn i (S:Set ℕ) := by
    intro x hx y hy he
    have hx0 := (mem_erase.mp hx).1; have hy0 := (mem_erase.mp hy).1
    dsimp [i] at he; omega
  have him : S.image i ⊆ c.support := by
    intro x hx; obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
    refine Finsupp.mem_support_iff.mpr ?_
    have hs := hstrong k hk
    intro hh; change c (k-1)=0 at hh; rw [hh,abs_zero] at hs; linarith
  let B : ℚ := 1+∑ k ∈ c.support, |c k|
  have hB : 1+(S.card:ℚ)/2 ≤ B := by
    have hsum : ∑ k ∈ S, (1/2:ℚ) ≤ ∑ k ∈ S, |c (i k)| := sum_le_sum (fun k hk => (hstrong k hk).le)
    rw [← sum_image (f := fun k => |c k|) hinj] at hsum
    have hum := sum_le_sum_of_subset_of_nonneg him (fun x _ _=>abs_nonneg (c x))
    simp at hsum
    dsimp [B]; linarith
  have hrq : (R:ℚ) ≤ 4*(Q.card:ℚ) := by exact_mod_cast hdensity R
  have hcq : (Q.card:ℚ) ≤ (S.card:ℚ)+1 := by exact_mod_cast hQ
  have hR : ((R:ℚ)+1)/8 ≤ B := by linarith
  have hR0 : 0 ≤ ((R:ℚ)+1)/8 := by positivity
  have hsquare : (((R:ℚ)+1)/8)^2 ≤ B^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (show 0≤B+((R:ℚ)+1)/8 by linarith)]
  have htail' : B^2/((H:ℚ)+1) < 1/((J:ℚ)+1) := htail.trans_lt hcost
  have hbound : ((J:ℚ)+1)*B^2 < (H:ℚ)+1 := by
    have ht := (div_lt_div_iff₀ (by positivity : (0:ℚ)<H+1) hj).mp htail'
    linarith
  have hrq' : (J:ℚ)+1 < 120*((R:ℚ)+1)^2 := by exact_mod_cast hr1
  have hj2 := mul_lt_mul_of_pos_left hrq' hj
  have hb2 := mul_le_mul_of_nonneg_left hsquare hj.le
  have hjH : ((J:ℚ)+1)^2 < 7680*((H:ℚ)+1) := by nlinarith
  exact_mod_cast hjH
theorem solution (c : ℕ →₀ ℚ) (H : ℕ) :
    let C : ℚ := ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ)
    (∀ n : ℕ, 2 ≤ n → (c (n-2) + (ArithmeticFunction.moebius n : ℚ))^2
      ≤ 30*(n:ℚ)^2*C) ∧ (∀ J : ℕ, C < 1/((J:ℚ)+1) → (J+1)^2 < 7680*(H+1)) := by
  change (∀ n : ℕ, 2 ≤ n → _ ≤ 30*(n:ℚ)^2*BagchiCertificate.cost c H) ∧
    (∀ J : ℕ, BagchiCertificate.cost c H < 1/((J:ℚ)+1) → (J+1)^2 < 7680*(H+1))
  have hall (n : ℕ) (hn : 2 ≤ n) :=
    BagchiCertificate.all_coefficient_from_identity c n H hn (BagchiCertificate.all_coefficient_identity c n hn)
  refine ⟨hall, ?_⟩
  intro J hJ
  apply quadratic_budget_from_all_coefficients c J H _ hJ _ hall quarter_le_squarefree_count
  unfold BagchiCertificate.cost BagchiCertificate.mass
  linarith [sum_nonneg (s:=range H) (fun i _ => BagchiCertificate.term_nonneg c i)]
