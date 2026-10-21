-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.canonical_log_products_separated_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:48:59.156906+00:00
-- url     : https://prove2.me/submissions/591ac654-972f-4b9b-a329-2d0aa7f6c413

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

/-- A largest differing index supplies a factor absent from the other product.
No cardinality or growth hypothesis is needed for this comparison. -/
private theorem base_product_comparison
    (m : Nat) (x : Nat → Real)
    (hxle : ∀ n, n ≤ m → 1 ≤ x n)
    (A B : Finset (Fin (m + 1))) (i : Fin (m + 1))
    (hiA : i ∈ A) (hiB : i ∉ B)
    (htail : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) :
    (∏ j ∈ B, x j.val) * x i.val ≤
      (∏ k ∈ Finset.range i.val, x k) * (∏ j ∈ A, x j.val) := by
  classical
  have hxl (j : Fin (m + 1)) : 1 ≤ x j.val :=
    hxle j.val (Nat.le_of_lt_succ j.isLt)
  have hpoint (j : Fin (m + 1)) :
      (if j ∈ B then x j.val else 1) * (if j = i then x j.val else 1) ≤
        (if j < i then x j.val else 1) * (if j ∈ A then x j.val else 1) := by
    rcases lt_trichotomy j i with hji | hji | hij
    · have hne : j ≠ i := ne_of_lt hji
      simp only [if_pos hji, if_neg hne, mul_one]
      split_ifs <;> nlinarith only [hxl j, sq_nonneg (x j.val - 1)]
    · subst j
      simp [hiA, hiB]
    · have hnlt : ¬ j < i := not_lt_of_ge hij.le
      have hne : j ≠ i := ne_of_gt hij
      simp only [if_neg hnlt, if_neg hne, mul_one, one_mul]
      have hm : j ∈ B ↔ j ∈ A := (htail j hij).symm
      simpa only [hm] using
        (le_refl (if j ∈ A then x j.val else (1 : Real)))
  have hprod :
      (∏ j : Fin (m + 1),
        (if j ∈ B then x j.val else 1) * (if j = i then x j.val else 1)) ≤
      ∏ j : Fin (m + 1),
        (if j < i then x j.val else 1) * (if j ∈ A then x j.val else 1) := by
    apply Finset.prod_le_prod
    · intro j hj
      have hxj : 0 ≤ x j.val := le_trans zero_le_one (hxl j)
      split_ifs <;> positivity
    · intro j hj
      exact hpoint j
  have hprod' :
      (∏ j ∈ B, x j.val) * x i.val ≤
        (∏ j : Fin (m + 1), if j < i then x j.val else 1) *
          (∏ j ∈ A, x j.val) := by
    simpa only [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq,
      Finset.prod_ite_eq', Finset.mem_univ, if_true] using hprod
  have hlow :
      (∏ j : Fin (m + 1), if j < i then x j.val else 1) =
        ∏ k ∈ Finset.range i.val, x k := by
    rw [← Finset.prod_filter]
    refine Finset.prod_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_range.mpr ((Finset.mem_filter.mp hj).2)
    · intro j hj k hk hjk
      exact Fin.ext hjk
    · intro k hk
      have hk' : k < i.val := Finset.mem_range.mp hk
      refine ⟨⟨k, lt_trans hk' i.isLt⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩
    · intro j hj
      rfl
  simpa only [hlow] using hprod'

theorem solution
    (m : Nat) (x : Nat → Real) (w0 v0 theta C : Real)
    (hx0 : x 0 = 1)
    (hxle : ∀ n, n ≤ m → 1 ≤ x n)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hgrowth : ∀ n, 1 ≤ n → n ≤ m →
      (C * (max 1 (max v0 (1 / theta) / min w0 1)) ^ (m + 1)) *
        (∏ j ∈ Finset.range n, x j) < x n) :
    let w : Fin (m + 1) → Real := fun i => Fin.cases w0 (fun j => x (j.val + 1)) i
    let v : Fin (m + 1) → Real := fun i => Fin.cases v0 (fun j => x (j.val + 1) / theta) i
    ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
          C * (∏ j ∈ B, v j) < ∏ j ∈ A, w j := by
  classical
  dsimp only
  intro A B hcard i hne hiA hiB htail
  let w : Fin (m + 1) → Real :=
    fun j => Fin.cases w0 (fun k => x (k.val + 1)) j
  let v : Fin (m + 1) → Real :=
    fun j => Fin.cases v0 (fun k => x (k.val + 1) / theta) j
  change C * (∏ j ∈ B, v j) < ∏ j ∈ A, w j
  have hxl (j : Fin (m + 1)) : 1 ≤ x j.val :=
    hxle j.val (Nat.le_of_lt_succ j.isLt)
  have hxn (j : Fin (m + 1)) : 0 ≤ x j.val :=
    le_trans zero_le_one (hxl j)
  have hxp (j : Fin (m + 1)) : 0 < x j.val :=
    lt_of_lt_of_le zero_lt_one (hxl j)
  have hwpos (j : Fin (m + 1)) : 0 < w j := by
    refine Fin.cases ?_ (fun k => ?_) j
    · change 0 < w0
      exact hw0
    · change 0 < x (k.val + 1)
      exact hxp k.succ
  have hvpos (j : Fin (m + 1)) : 0 < v j := by
    refine Fin.cases ?_ (fun k => ?_) j
    · change 0 < v0
      exact hv0
    · change 0 < x (k.val + 1) / theta
      exact div_pos (hxp k.succ) htheta
  have hWpos : 0 < ∏ j ∈ A, w j :=
    Finset.prod_pos (fun j hj => hwpos j)
  have hVpos : 0 < ∏ j ∈ B, v j :=
    Finset.prod_pos (fun j hj => hvpos j)
  by_cases hC : C ≤ 0
  · exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hC hVpos.le) hWpos
  have hCpos : 0 < C := lt_of_not_ge hC
  let a : Real := min w0 1
  let b : Real := max v0 (1 / theta)
  let K : Real := max 1 (b / a)
  have ha : 0 < a := lt_min hw0 zero_lt_one
  have ha1 : a ≤ 1 := min_le_right _ _
  have hK : 1 ≤ K := le_max_left _ _
  have hKn : 0 ≤ K := le_trans zero_le_one hK
  have hbK : b ≤ K * a :=
    (div_le_iff₀ ha).mp (show b / a ≤ K from le_max_right _ _)
  have hwlow (j : Fin (m + 1)) : a * x j.val ≤ w j := by
    refine Fin.cases ?_ (fun k => ?_) j
    · change a * x 0 ≤ w0
      rw [hx0, mul_one]
      exact min_le_left _ _
    · change a * x (k.val + 1) ≤ x (k.val + 1)
      have hxk : 0 ≤ x (k.val + 1) := hxn k.succ
      calc
        a * x (k.val + 1) ≤ 1 * x (k.val + 1) :=
          mul_le_mul_of_nonneg_right ha1 hxk
        _ = x (k.val + 1) := one_mul _
  have hvup (j : Fin (m + 1)) : v j ≤ (K * a) * x j.val := by
    refine Fin.cases ?_ (fun k => ?_) j
    · change v0 ≤ (K * a) * x 0
      rw [hx0, mul_one]
      exact (le_max_left v0 (1 / theta)).trans hbK
    · change x (k.val + 1) / theta ≤ (K * a) * x (k.val + 1)
      calc
        x (k.val + 1) / theta = (1 / theta) * x (k.val + 1) := by ring
        _ ≤ b * x (k.val + 1) :=
          mul_le_mul_of_nonneg_right (le_max_right v0 (1 / theta)) (hxn k.succ)
        _ ≤ (K * a) * x (k.val + 1) :=
          mul_le_mul_of_nonneg_right hbK (hxn k.succ)
  have hwprod :
      a ^ A.card * (∏ j ∈ A, x j.val) ≤ ∏ j ∈ A, w j := by
    calc
      _ = ∏ j ∈ A, a * x j.val := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod
        (fun j hj => mul_nonneg ha.le (hxn j)) (fun j hj => hwlow j)
  have hvprod :
      (∏ j ∈ B, v j) ≤ K ^ B.card * a ^ B.card * (∏ j ∈ B, x j.val) := by
    calc
      _ ≤ ∏ j ∈ B, (K * a) * x j.val :=
        Finset.prod_le_prod (fun j hj => (hvpos j).le) (fun j hj => hvup j)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, mul_pow]
  have hbase := base_product_comparison m x hxle A B i hiA hiB htail
  have hPnonneg : 0 ≤ ∏ k ∈ Finset.range i.val, x k := by
    apply Finset.prod_nonneg
    intro k hk
    have hk' : k < i.val := Finset.mem_range.mp hk
    exact le_trans zero_le_one (hxle k (le_trans (Nat.le_of_lt hk') (Nat.le_of_lt_succ i.isLt)))
  have hKpow : K ^ B.card ≤ K ^ (m + 1) :=
    pow_le_pow_right₀ hK (by simpa only [Fintype.card_fin] using B.card_le_univ)
  have hcomp :
      (∏ j ∈ B, v j) * x i.val ≤
        K ^ (m + 1) * (∏ k ∈ Finset.range i.val, x k) * (∏ j ∈ A, w j) := by
    calc
      (∏ j ∈ B, v j) * x i.val ≤
          (K ^ B.card * a ^ B.card * (∏ j ∈ B, x j.val)) * x i.val :=
        mul_le_mul_of_nonneg_right hvprod (hxn i)
      _ = (K ^ B.card * a ^ B.card) * ((∏ j ∈ B, x j.val) * x i.val) := by ring
      _ ≤ (K ^ B.card * a ^ B.card) *
          ((∏ k ∈ Finset.range i.val, x k) * (∏ j ∈ A, x j.val)) :=
        mul_le_mul_of_nonneg_left hbase
          (mul_nonneg (pow_nonneg hKn _) (pow_nonneg ha.le _))
      _ = (K ^ B.card * (∏ k ∈ Finset.range i.val, x k)) *
          (a ^ A.card * (∏ j ∈ A, x j.val)) := by
        rw [hcard]
        ring
      _ ≤ (K ^ B.card * (∏ k ∈ Finset.range i.val, x k)) * (∏ j ∈ A, w j) :=
        mul_le_mul_of_nonneg_left hwprod (mul_nonneg (pow_nonneg hKn _) hPnonneg)
      _ = K ^ B.card *
          ((∏ k ∈ Finset.range i.val, x k) * (∏ j ∈ A, w j)) := by ring
      _ ≤ K ^ (m + 1) *
          ((∏ k ∈ Finset.range i.val, x k) * (∏ j ∈ A, w j)) :=
        mul_le_mul_of_nonneg_right hKpow (mul_nonneg hPnonneg hWpos.le)
      _ = _ := by ring
  have hi0 : i.val ≠ 0 := by
    intro hi
    apply hne
    exact Fin.ext hi
  have higrowth :
      (C * K ^ (m + 1)) * (∏ k ∈ Finset.range i.val, x k) < x i.val :=
    hgrowth i.val (Nat.one_le_iff_ne_zero.mpr hi0) (Nat.le_of_lt_succ i.isLt)
  have hstrict := mul_lt_mul_of_pos_right higrowth hWpos
  have hscaled := mul_le_mul_of_nonneg_left hcomp hCpos.le
  apply (mul_lt_mul_iff_left₀ (hxp i)).mp
  calc
    (C * (∏ j ∈ B, v j)) * x i.val =
        C * ((∏ j ∈ B, v j) * x i.val) := by ring
    _ ≤ C * (K ^ (m + 1) * (∏ k ∈ Finset.range i.val, x k) *
        (∏ j ∈ A, w j)) := hscaled
    _ = ((C * K ^ (m + 1)) * (∏ k ∈ Finset.range i.val, x k)) *
        (∏ j ∈ A, w j) := by ring
    _ < x i.val * (∏ j ∈ A, w j) := hstrict
    _ = (∏ j ∈ A, w j) * x i.val := mul_comm _ _