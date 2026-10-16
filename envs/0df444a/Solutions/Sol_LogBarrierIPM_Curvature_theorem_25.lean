-- Prove2me | solution 1 for LogBarrierIPM.Curvature.theorem_25
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T01:47:43.190595+00:00
-- url     : https://prove2.me/submissions/3070b285-40a2-4103-be74-527da4a86fe5

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TotalCurvature
import Definitions.Def_LogBarrierIPM_Curvature_SlackCentralPath
import Definitions.Def_LogBarrierIPM_Iterations_LW
import Definitions.Def_LogBarrierIPM_Curvature_TropicalAngle
import Definitions.Def_LogBarrierIPM_Curvature_TropicalCentralPathLW

set_option autoImplicit false
open Matrix

namespace LogBarrierIPM.Iterations

/-- Duality identity: `x·s + w·y = c·x + b·y` on primal-dual feasible points. -/
lemma duality_identity {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : PDPoint n m) (h1 : A *ᵥ z.1 + z.2.1 = b) (h2 : z.2.2.1 - Aᵀ *ᵥ z.2.2.2 = c) :
    z.1 ⬝ᵥ z.2.2.1 + z.2.1 ⬝ᵥ z.2.2.2 = c ⬝ᵥ z.1 + b ⬝ᵥ z.2.2.2 := by
  have hs : z.2.2.1 = c + Aᵀ *ᵥ z.2.2.2 := by rw [← h2]; abel
  have hw : z.2.1 = b - A *ᵥ z.1 := by rw [← h1]; abel
  rw [hs, hw, dotProduct_add, sub_dotProduct, dotProduct_comm z.1 c, dotProduct_mulVec,
    vecMul_transpose]
  ring

/-- Indicator sum with three distinct nonzero entries. -/
lemma sum_ind3 (n : ℕ) (f : Fin n → ℝ) (a b c : ℕ) (ha : a < n) (hb : b < n) (hc : c < n)
    (u v w : ℝ) :
    ∑ k : Fin n, ((if k.val = a then u else 0) + (if k.val = b then v else 0) +
        (if k.val = c then w else 0)) * f k =
      u * f ⟨a, ha⟩ + v * f ⟨b, hb⟩ + w * f ⟨c, hc⟩ := by
  have e : ∀ (d : ℕ) (hd : d < n) (k : Fin n), (k.val = d) ↔ (k = ⟨d, hd⟩) := by
    intro d hd k; simp [Fin.ext_iff]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [e a ha, e b hb, e c hc, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma lw_rowsum (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (i : Fin (3 * r - 1)) :
    (lwA r t *ᵥ x) i = ∑ k : Fin (2 * r), lwEntry t (i.val + 1) (k.val + 1) * x k := by
  simp [lwA, mulVec, dotProduct]

lemma lw_row_a (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    (lwA r t *ᵥ x) ⟨3 * j - 1, by omega⟩ =
      x ⟨2 * j, by omega⟩ - t * x ⟨2 * j - 2, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (3 * j - 1 + 1) (k.val + 1) =
      (if k.val = 2 * j then 1 else 0) + (if k.val = 2 * j - 2 then -t else 0) +
        (if k.val = 0 then 0 else 0) := by
    intro k
    have h3 : 3 * j - 1 + 1 = 3 * j := by omega
    have hd : 3 * j / 3 = j := by omega
    have hm : 3 * j % 3 = 0 := by omega
    simp only [lwEntry, h3, hd, hm]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x (2 * j) (2 * j - 2) 0 (by omega) (by omega) (by omega)]
  ring

lemma lw_row_b (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    (lwA r t *ᵥ x) ⟨3 * j, by omega⟩ =
      x ⟨2 * j, by omega⟩ - t * x ⟨2 * j - 1, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (3 * j + 1) (k.val + 1) =
      (if k.val = 2 * j then 1 else 0) + (if k.val = 2 * j - 1 then -t else 0) +
        (if k.val = 0 then 0 else 0) := by
    intro k
    have hd : (3 * j + 1) / 3 = j := by omega
    have hm : (3 * j + 1) % 3 = 1 := by omega
    simp only [lwEntry, hd, hm]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x (2 * j) (2 * j - 1) 0 (by omega) (by omega) (by omega)]
  ring

lemma lw_row_c (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    (lwA r t *ᵥ x) ⟨3 * j + 1, by omega⟩ =
      x ⟨2 * j + 1, by omega⟩ - t ^ ((1 : ℝ) - 1 / 2 ^ j) * x ⟨2 * j - 2, by omega⟩
        - t ^ ((1 : ℝ) - 1 / 2 ^ j) * x ⟨2 * j - 1, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (3 * j + 1 + 1) (k.val + 1) =
      (if k.val = 2 * j + 1 then 1 else 0) +
        (if k.val = 2 * j - 2 then -(t ^ ((1 : ℝ) - 1 / 2 ^ j)) else 0) +
        (if k.val = 2 * j - 1 then -(t ^ ((1 : ℝ) - 1 / 2 ^ j)) else 0) := by
    intro k
    have hd : (3 * j + 1 + 1) / 3 = j := by omega
    have hm : (3 * j + 1 + 1) % 3 = 2 := by omega
    simp only [lwEntry, hd, hm]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x (2 * j + 1) (2 * j - 2) (2 * j - 1) (by omega) (by omega) (by omega)]
  ring

lemma lw_row_0 (r : ℕ) (t : ℝ) (hr : 1 ≤ r) (x : Fin (2 * r) → ℝ) :
    (lwA r t *ᵥ x) ⟨0, by omega⟩ = x ⟨0, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (0 + 1) (k.val + 1) =
      (if k.val = 0 then 1 else 0) + (if k.val = 0 then 0 else 0) +
        (if k.val = 0 then 0 else 0) := by
    intro k
    simp only [lwEntry]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x 0 0 0 (by omega) (by omega) (by omega)]
  ring

lemma lw_row_1 (r : ℕ) (t : ℝ) (hr : 1 ≤ r) (x : Fin (2 * r) → ℝ) :
    (lwA r t *ᵥ x) ⟨1, by omega⟩ = x ⟨1, by omega⟩ := by
  rw [lw_rowsum]
  have hpt : ∀ k : Fin (2 * r), lwEntry t (1 + 1) (k.val + 1) =
      (if k.val = 1 then 1 else 0) + (if k.val = 1 then 0 else 0) +
        (if k.val = 1 then 0 else 0) := by
    intro k
    simp only [lwEntry]
    split_ifs <;> first | omega | simp_all
  simp only [hpt]
  rw [sum_ind3 (2 * r) x 1 1 1 (by omega) (by omega) (by omega)]
  ring

lemma lw_row_a' (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j i p q : ℕ) (hj1 : 1 ≤ j) (hjr : j < r)
    (hi : i = 3 * j - 1) (hp : p = 2 * j) (hq : q = 2 * j - 2)
    (hi' : i < 3 * r - 1) (hp' : p < 2 * r) (hq' : q < 2 * r) :
    (lwA r t *ᵥ x) ⟨i, hi'⟩ = x ⟨p, hp'⟩ - t * x ⟨q, hq'⟩ := by
  subst hi hp hq; exact lw_row_a r t x j hj1 hjr

lemma lw_row_b' (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j i p q : ℕ) (hj1 : 1 ≤ j) (hjr : j < r)
    (hi : i = 3 * j) (hp : p = 2 * j) (hq : q = 2 * j - 1)
    (hi' : i < 3 * r - 1) (hp' : p < 2 * r) (hq' : q < 2 * r) :
    (lwA r t *ᵥ x) ⟨i, hi'⟩ = x ⟨p, hp'⟩ - t * x ⟨q, hq'⟩ := by
  subst hi hp hq; exact lw_row_b r t x j hj1 hjr

lemma lw_row_c' (r : ℕ) (t : ℝ) (x : Fin (2 * r) → ℝ) (j i p q1 q2 : ℕ) (hj1 : 1 ≤ j) (hjr : j < r)
    (hi : i = 3 * j + 1) (hp : p = 2 * j + 1) (hq1 : q1 = 2 * j - 2) (hq2 : q2 = 2 * j - 1)
    (hi' : i < 3 * r - 1) (hp' : p < 2 * r) (hq1' : q1 < 2 * r) (hq2' : q2 < 2 * r) :
    (lwA r t *ᵥ x) ⟨i, hi'⟩ =
      x ⟨p, hp'⟩ - t ^ ((1 : ℝ) - 1 / 2 ^ j) * x ⟨q1, hq1'⟩
        - t ^ ((1 : ℝ) - 1 / 2 ^ j) * x ⟨q2, hq2'⟩ := by
  subst hi hp hq1 hq2; exact lw_row_c r t x j hj1 hjr


lemma xcongr {n : ℕ} (x : Fin n → ℝ) (a b : ℕ) (ha : a < n) (hb : b < n) (h : a = b) :
    x ⟨a, ha⟩ = x ⟨b, hb⟩ := by subst h; rfl

lemma lw_x0 (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) :
    z.1 ⟨0, by omega⟩ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * dualityMeasure z ∧
      z.1 ⟨0, by omega⟩ < t ^ 2 := by
  obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
  have hN : (0 : ℝ) < ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 0 < 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  constructor
  · have hid := duality_identity _ _ _ z h1 h2
    have hmu : ((2 * r + (3 * r - 1) : ℕ) : ℝ) * dualityMeasure z =
        z.1 ⬝ᵥ z.2.2.1 + z.2.1 ⬝ᵥ z.2.2.2 := by
      unfold dualityMeasure
      field_simp
    have hc : lwC r ⬝ᵥ z.1 = z.1 ⟨0, by omega⟩ := by
      simp only [dotProduct, lwC]
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro k _ hk
        have : k.val ≠ 0 := fun h => hk (Fin.ext h)
        simp [this]
      · simp
    have hb : 0 ≤ lwB r t ⬝ᵥ z.2.2.2 := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg _ (hy i).le
      unfold lwB
      split_ifs <;> positivity
    rw [hmu, hid, hc]
    linarith
  · have e := congrFun h1 ⟨0, by omega⟩
    rw [Pi.add_apply, lw_row_0 r t hr] at e
    simp only [lwB] at e
    simp at e
    have := hw ⟨0, by omega⟩
    linarith

lemma lw_step (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) (j : ℕ) (hj : j + 1 < r) :
    z.1 ⟨2 * (j + 1), by omega⟩ < t * z.1 ⟨2 * j, by omega⟩ ∧
    z.1 ⟨2 * (j + 1), by omega⟩ < t * z.1 ⟨2 * j + 1, by omega⟩ ∧
    z.1 ⟨2 * (j + 1) + 1, by omega⟩ <
      t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * (z.1 ⟨2 * j, by omega⟩ + z.1 ⟨2 * j + 1, by omega⟩) := by
  obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
  have hb0 : ∀ i : Fin (3 * r - 1), 2 ≤ i.val → lwB r t i = 0 := by
    intro i hi; simp only [lwB]; rw [if_neg (by omega), if_neg (by omega)]
  have ea := congrFun h1 ⟨3 * j + 2, by omega⟩
  have ra := lw_row_a' r t z.1 (j + 1) (3 * j + 2) (2 * (j + 1)) (2 * j) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [Pi.add_apply, ra] at ea
  have eb := congrFun h1 ⟨3 * j + 3, by omega⟩
  have rb := lw_row_b' r t z.1 (j + 1) (3 * j + 3) (2 * (j + 1)) (2 * j + 1) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [Pi.add_apply, rb] at eb
  have ec := congrFun h1 ⟨3 * j + 4, by omega⟩
  have rc := lw_row_c' r t z.1 (j + 1) (3 * j + 4) (2 * (j + 1) + 1) (2 * j) (2 * j + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  rw [Pi.add_apply, rc] at ec
  have wa := hw ⟨3 * j + 2, by omega⟩
  have wb := hw ⟨3 * j + 3, by omega⟩
  have wc := hw ⟨3 * j + 4, by omega⟩
  rw [hb0 ⟨3 * j + 2, by omega⟩ (by simp)] at ea
  rw [hb0 ⟨3 * j + 3, by omega⟩ (by simp)] at eb
  rw [hb0 ⟨3 * j + 4, by omega⟩ (by simp)] at ec
  refine ⟨by linarith, by linarith, by linarith⟩

/-- elementary upper bounds along the chain -/
theorem lw_upper (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) (lam : ℝ)
    (hμ : dualityMeasure z ≤ t ^ lam) :
    ∀ j : ℕ, ∀ hj : j < r,
      z.1 ⟨2 * j, by omega⟩ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * 2 ^ j * t ^ (xPair lam j).1 ∧
      z.1 ⟨2 * j + 1, by omega⟩ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * 2 ^ j * t ^ (xPair lam j).2 := by
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  intro j
  induction j with
  | zero =>
    intro hj
    obtain ⟨h0a, h0b⟩ := lw_x0 r hr t ht1 z hfeas
    obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
    simp only [xPair, pow_zero, mul_one, Nat.mul_zero, Nat.zero_add]
    refine ⟨?_, ?_⟩
    · rcases le_total lam 2 with hl | hl
      · rw [min_eq_left hl]
        calc z.1 ⟨0, by omega⟩ ≤ _ := h0a
          _ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * t ^ lam :=
            mul_le_mul_of_nonneg_left hμ (by linarith)
      · rw [min_eq_right hl]
        calc z.1 ⟨0, by omega⟩ ≤ t ^ 2 := h0b.le
          _ = t ^ (2 : ℝ) := by norm_num
          _ ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) * t ^ (2 : ℝ) :=
            le_mul_of_one_le_left (by positivity) hN1
    · have e := congrFun h1 ⟨1, by omega⟩
      rw [Pi.add_apply, lw_row_1 r t hr] at e
      simp only [lwB] at e
      simp at e
      have := hw ⟨1, by omega⟩
      rw [Real.rpow_one]
      calc z.1 ⟨1, by omega⟩ ≤ t := by linarith
        _ ≤ _ := le_mul_of_one_le_left ht0.le hN1
  | succ j ih =>
    intro hj
    obtain ⟨ihA, ihB⟩ := ih (by omega)
    obtain ⟨sa, sb, sc⟩ := lw_step r hr t z hfeas j hj
    set X := z.1 ⟨2 * j, by omega⟩ with hX
    set Y := z.1 ⟨2 * j + 1, by omega⟩ with hY
    set P := z.1 ⟨2 * (j + 1), by omega⟩ with hP
    set Q := z.1 ⟨2 * (j + 1) + 1, by omega⟩ with hQ
    set C : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) * 2 ^ j with hC
    have hC0 : 0 ≤ C := by positivity
    set α := (xPair lam j).1 with hα
    set β := (xPair lam j).2 with hβ
    have hxp : xPair lam (j + 1) = (1 + min α β, (1 - 1 / 2 ^ (j + 1)) + max α β) := by
      rw [xPair]
    have hpow : ((2 * r + (3 * r - 1) : ℕ) : ℝ) * 2 ^ (j + 1) = 2 * C := by
      rw [hC]; ring
    rw [hxp, hpow]
    simp only
    have hmono : ∀ a b : ℝ, a ≤ b → t ^ a ≤ t ^ b :=
      fun a b h => Real.rpow_le_rpow_of_exponent_le ht1.le h
    refine ⟨?_, ?_⟩
    · rw [Real.rpow_add ht0, Real.rpow_one]
      rcases le_total α β with h | h
      · rw [min_eq_left h]
        have : P ≤ t * (C * t ^ α) := by nlinarith
        have h2 : 0 ≤ C * (t * t ^ α) := by positivity
        nlinarith
      · rw [min_eq_right h]
        have : P ≤ t * (C * t ^ β) := by nlinarith
        have h2 : 0 ≤ C * (t * t ^ β) := by positivity
        nlinarith
    · rw [Real.rpow_add ht0]
      have hτ : 0 < t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) := by positivity
      have hXb : X ≤ C * t ^ max α β := ihA.trans (mul_le_mul_of_nonneg_left (hmono _ _ (le_max_left _ _)) hC0)
      have hYb : Y ≤ C * t ^ max α β := ihB.trans (mul_le_mul_of_nonneg_left (hmono _ _ (le_max_right _ _)) hC0)
      have : Q ≤ t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * (2 * (C * t ^ max α β)) := by
        calc Q ≤ _ := sc.le
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hτ.le
      calc Q ≤ _ := this
        _ = _ := by ring


/-- extension by zero of a `Fin n` vector to `ℕ` -/
noncomputable def fext {n : ℕ} (f : Fin n → ℝ) (a : ℕ) : ℝ := if h : a < n then f ⟨a, h⟩ else 0

lemma sum_ind (n : ℕ) (f : Fin n → ℝ) (a : ℕ) (u : ℝ) :
    ∑ k : Fin n, (if k.val = a then u else 0) * f k = u * fext f a := by
  unfold fext
  by_cases h : a < n
  · have e : ∀ k : Fin n, (k.val = a) ↔ (k = ⟨a, h⟩) := fun k => by simp [Fin.ext_iff]
    simp only [e, dif_pos h, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have e : ∀ k : Fin n, ¬ (k.val = a) := fun k hk => h (hk ▸ k.isLt)
    simp [e, h]

lemma lw_colsum (r : ℕ) (t : ℝ) (y : Fin (3 * r - 1) → ℝ) (k : Fin (2 * r)) :
    ((lwA r t)ᵀ *ᵥ y) k = ∑ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (k.val + 1) * y i := by
  simp [lwA, mulVec, dotProduct, Matrix.transpose_apply]

lemma lw_col_a (r : ℕ) (t : ℝ) (y : Fin (3 * r - 1) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    ((lwA r t)ᵀ *ᵥ y) ⟨2 * j, by omega⟩ =
      fext y (3 * j - 1) + fext y (3 * j) - t * fext y (3 * j + 2)
        - t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * fext y (3 * j + 4) := by
  rw [lw_colsum]
  have hpt : ∀ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (2 * j + 1) =
      (if i.val = 3 * j - 1 then 1 else 0) + (if i.val = 3 * j then 1 else 0) +
      (if i.val = 3 * j + 2 then -t else 0) +
      (if i.val = 3 * j + 4 then -(t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1))) else 0) := by
    intro i
    simp only [lwEntry]
    split_ifs <;> try omega
    all_goals first | (simp; done) | (rw [show ((i : ℕ) + 1) / 3 = j + 1 by omega]; simp; done)
  simp only [hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  ring


lemma lw_col_a0 (r : ℕ) (t : ℝ) (hr : 1 ≤ r) (y : Fin (3 * r - 1) → ℝ) :
    ((lwA r t)ᵀ *ᵥ y) ⟨0, by omega⟩ =
      fext y 0 - t * fext y 2 - t ^ ((1 : ℝ) - 1 / 2 ^ 1) * fext y 4 := by
  rw [lw_colsum]
  have hpt : ∀ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (0 + 1) =
      (if i.val = 0 then 1 else 0) + (if i.val = 2 then -t else 0) +
      (if i.val = 4 then -(t ^ ((1 : ℝ) - 1 / 2 ^ 1)) else 0) := by
    intro i
    simp only [lwEntry]
    split_ifs <;> try omega
    all_goals first | (simp; done) | (rw [show ((i : ℕ) + 1) / 3 = 1 by omega]; simp; done)
  simp only [Fin.val_mk, hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  ring

lemma lw_col_b0 (r : ℕ) (t : ℝ) (hr : 1 ≤ r) (y : Fin (3 * r - 1) → ℝ) :
    ((lwA r t)ᵀ *ᵥ y) ⟨1, by omega⟩ =
      fext y 1 - t * fext y 3 - t ^ ((1 : ℝ) - 1 / 2 ^ 1) * fext y 4 := by
  rw [lw_colsum]
  have hpt : ∀ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (1 + 1) =
      (if i.val = 1 then 1 else 0) + (if i.val = 3 then -t else 0) +
      (if i.val = 4 then -(t ^ ((1 : ℝ) - 1 / 2 ^ 1)) else 0) := by
    intro i
    simp only [lwEntry]
    split_ifs <;> try omega
    all_goals first | (simp; done) | (rw [show ((i : ℕ) + 1) / 3 = 1 by omega]; simp; done)
  simp only [Fin.val_mk, hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  ring

lemma lw_col_b (r : ℕ) (t : ℝ) (y : Fin (3 * r - 1) → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    ((lwA r t)ᵀ *ᵥ y) ⟨2 * j + 1, by omega⟩ =
      fext y (3 * j + 1) - t * fext y (3 * j + 3)
        - t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * fext y (3 * j + 4) := by
  rw [lw_colsum]
  have hpt : ∀ i : Fin (3 * r - 1), lwEntry t (i.val + 1) (2 * j + 1 + 1) =
      (if i.val = 3 * j + 1 then 1 else 0) + (if i.val = 3 * j + 3 then -t else 0) +
      (if i.val = 3 * j + 4 then -(t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1))) else 0) := by
    intro i
    simp only [lwEntry]
    split_ifs <;> try omega
    all_goals first | (simp; done) | (rw [show ((i : ℕ) + 1) / 3 = j + 1 by omega]; simp; done)
  simp only [hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  ring


lemma fext_nonneg {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (a : ℕ) : 0 ≤ fext f a := by
  unfold fext; split_ifs with h
  · exact hf _
  · exact le_rfl

lemma fext_pos {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 < f i) (a : ℕ) (ha : a < n) : 0 < fext f a := by
  unfold fext; rw [dif_pos ha]; exact hf _

/-- `F_a(j)`: inflow at the `a`-column of pair `j`. -/
noncomputable def Fa {r : ℕ} (y : Fin (3 * r - 1) → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 + fext y 0 else fext y (3 * j - 1) + fext y (3 * j)

/-- `F_b(j)`: inflow at the `b`-column of pair `j`. -/
noncomputable def Fb {r : ℕ} (y : Fin (3 * r - 1) → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then fext y 1 else fext y (3 * j + 1)

lemma lw_s_a (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (z : PDPoint (2 * r) (3 * r - 1))
    (h2 : z.2.2.1 - (lwA r t)ᵀ *ᵥ z.2.2.2 = lwC r) (j : ℕ) (hj : j < r) :
    z.2.2.1 ⟨2 * j, by omega⟩ = Fa z.2.2.2 j - t * fext z.2.2.2 (3 * j + 2)
      - t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * fext z.2.2.2 (3 * j + 4) := by
  have hk := congrFun h2 ⟨2 * j, by omega⟩
  rw [Pi.sub_apply] at hk
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have := lw_col_a0 r t hr z.2.2.2
    simp only [Nat.mul_zero] at hk ⊢
    rw [this] at hk
    simp only [lwC] at hk
    simp only [Fa, if_true]
    simp at hk ⊢
    linarith
  · rw [lw_col_a r t z.2.2.2 j hpos hj] at hk
    simp only [lwC] at hk
    rw [if_neg (by omega)] at hk
    simp only [Fa, if_neg (show j ≠ 0 by omega)]
    linarith

lemma lw_s_b (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (z : PDPoint (2 * r) (3 * r - 1))
    (h2 : z.2.2.1 - (lwA r t)ᵀ *ᵥ z.2.2.2 = lwC r) (j : ℕ) (hj : j < r) :
    z.2.2.1 ⟨2 * j + 1, by omega⟩ = Fb z.2.2.2 j - t * fext z.2.2.2 (3 * j + 3)
      - t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) * fext z.2.2.2 (3 * j + 4) := by
  have hk := congrFun h2 ⟨2 * j + 1, by omega⟩
  rw [Pi.sub_apply] at hk
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have := lw_col_b0 r t hr z.2.2.2
    simp only [Nat.mul_zero, Nat.zero_add] at hk ⊢
    rw [this] at hk
    simp only [lwC] at hk
    simp only [Fb, if_true]
    simp at hk ⊢
    linarith
  · rw [lw_col_b r t z.2.2.2 j hpos hj] at hk
    simp only [lwC] at hk
    rw [if_neg (by omega)] at hk
    simp only [Fb, if_neg (show j ≠ 0 by omega)]
    linarith


lemma lw_dual_base (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) :
    t ^ 2 * fext z.2.2.2 0 + t * fext z.2.2.2 1 ≤
      ((2 * r + (3 * r - 1) : ℕ) : ℝ) * dualityMeasure z := by
  obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
  have hN : (0 : ℝ) < ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 0 < 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  have hid := duality_identity _ _ _ z h1 h2
  have hmu : ((2 * r + (3 * r - 1) : ℕ) : ℝ) * dualityMeasure z =
      z.1 ⬝ᵥ z.2.2.1 + z.2.1 ⬝ᵥ z.2.2.2 := by
    unfold dualityMeasure
    field_simp
  have hc : lwC r ⬝ᵥ z.1 = z.1 ⟨0, by omega⟩ := by
    simp only [dotProduct, lwC]
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · simp
    · intro k _ hk
      have : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [this]
    · simp
  have hb : lwB r t ⬝ᵥ z.2.2.2 = t ^ 2 * fext z.2.2.2 0 + t * fext z.2.2.2 1 := by
    simp only [dotProduct]
    have hpt : ∀ i : Fin (3 * r - 1), lwB r t i = (if i.val = 0 then t ^ 2 else 0) +
        (if i.val = 1 then t else 0) := by
      intro i; unfold lwB; split_ifs <;> first | omega | simp
    simp only [hpt, add_mul, Finset.sum_add_distrib, sum_ind]
  rw [hmu, hid, hc, hb]
  have := hx ⟨0, by omega⟩
  linarith

lemma flow_step (t : ℝ) (ht1 : 1 < t) (lam A B c D Fa Fb ya yb yc : ℝ) (hD : 0 ≤ D)
    (hFa : Fa ≤ D * t ^ (lam - A)) (hFb : Fb ≤ D * t ^ (lam - B))
    (hya : 0 ≤ ya) (hyb : 0 ≤ yb) (hyc : 0 ≤ yc)
    (h1 : t * ya ≤ Fa) (h2 : t * yb ≤ Fb)
    (h3 : t ^ ((1 : ℝ) - c) * yc ≤ Fa) (h4 : t ^ ((1 : ℝ) - c) * yc ≤ Fb) :
    ya + yb ≤ 2 * D * t ^ (lam - (1 + min A B)) ∧
    yc ≤ 2 * D * t ^ (lam - ((1 - c) + max A B)) := by
  have ht0 : 0 < t := by linarith
  have hmono : ∀ a b : ℝ, a ≤ b → t ^ a ≤ t ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le ht1.le h
  constructor
  · have e : t ^ (lam - min A B) = t ^ (lam - (1 + min A B)) * t := by
      rw [show lam - min A B = (lam - (1 + min A B)) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
    have hA : t ^ (lam - A) ≤ t ^ (lam - min A B) := hmono _ _ (by linarith [min_le_left A B])
    have hB : t ^ (lam - B) ≤ t ^ (lam - min A B) := hmono _ _ (by linarith [min_le_right A B])
    have key : t * (ya + yb) ≤ t * (2 * D * t ^ (lam - (1 + min A B))) := by
      calc t * (ya + yb) = t * ya + t * yb := by ring
        _ ≤ Fa + Fb := add_le_add h1 h2
        _ ≤ D * t ^ (lam - min A B) + D * t ^ (lam - min A B) :=
            add_le_add (hFa.trans (mul_le_mul_of_nonneg_left hA hD))
              (hFb.trans (mul_le_mul_of_nonneg_left hB hD))
        _ = t * (2 * D * t ^ (lam - (1 + min A B))) := by rw [e]; ring
    exact le_of_mul_le_mul_left key ht0
  · set τ : ℝ := t ^ ((1 : ℝ) - c) with hτ
    have hτ0 : 0 < τ := by positivity
    have e : t ^ (lam - max A B) = t ^ (lam - ((1 - c) + max A B)) * τ := by
      rw [hτ, ← Real.rpow_add ht0]; congr 1; ring
    have hbound : τ * yc ≤ D * t ^ (lam - max A B) := by
      rcases le_total A B with h | h
      · rw [max_eq_right h]; exact h4.trans hFb
      · rw [max_eq_left h]; exact h3.trans hFa
    have hnn : 0 ≤ D * t ^ (lam - ((1 - c) + max A B)) := by positivity
    have : τ * yc ≤ τ * (D * t ^ (lam - ((1 - c) + max A B))) := by
      calc τ * yc ≤ D * t ^ (lam - max A B) := hbound
        _ = τ * (D * t ^ (lam - ((1 - c) + max A B))) := by rw [e]; ring
    have := le_of_mul_le_mul_left this hτ0
    nlinarith


theorem lw_dual_bound (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) (lam : ℝ)
    (hμ : dualityMeasure z = t ^ lam) :
    ∀ j : ℕ, j < r →
      Fa z.2.2.2 j ≤ (((2 * r + (3 * r - 1) : ℕ) : ℝ) + 1) * 2 ^ j * t ^ (lam - (xPair lam j).1) ∧
      Fb z.2.2.2 j ≤ (((2 * r + (3 * r - 1) : ℕ) : ℝ) + 1) * 2 ^ j * t ^ (lam - (xPair lam j).2) := by
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  have hbase := lw_dual_base r hr t ht1 z hfeas
  obtain ⟨h1, h2, hx, hw, hs, hy⟩ := hfeas
  have hy0 : 0 ≤ fext z.2.2.2 0 := fext_nonneg _ (fun i => (hy i).le) 0
  have hy1 : 0 ≤ fext z.2.2.2 1 := fext_nonneg _ (fun i => (hy i).le) 1
  intro j
  induction j with
  | zero =>
    intro hj
    rw [hμ] at hbase
    set N : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) with hNdef
    have e2 : t ^ lam = t ^ (lam - 2) * t ^ 2 := by
      rw [show lam = (lam - 2) + (2 : ℕ) by push_cast; ring, Real.rpow_add ht0, Real.rpow_natCast]
      simp
    have e1 : t ^ lam = t ^ (lam - 1) * t := by
      rw [show lam = (lam - 1) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
      simp
    have hT2 : fext z.2.2.2 0 ≤ N * t ^ (lam - 2) := by
      have : t ^ 2 * fext z.2.2.2 0 ≤ t ^ 2 * (N * t ^ (lam - 2)) := by
        calc t ^ 2 * fext z.2.2.2 0 ≤ t ^ 2 * fext z.2.2.2 0 + t * fext z.2.2.2 1 := by
              have : 0 ≤ t * fext z.2.2.2 1 := by positivity
              linarith
          _ ≤ N * t ^ lam := hbase
          _ = t ^ 2 * (N * t ^ (lam - 2)) := by rw [e2]; ring
      exact le_of_mul_le_mul_left this (by positivity)
    have hT1 : fext z.2.2.2 1 ≤ N * t ^ (lam - 1) := by
      have : t * fext z.2.2.2 1 ≤ t * (N * t ^ (lam - 1)) := by
        calc t * fext z.2.2.2 1 ≤ t ^ 2 * fext z.2.2.2 0 + t * fext z.2.2.2 1 := by
              have : 0 ≤ t ^ 2 * fext z.2.2.2 0 := by positivity
              linarith
          _ ≤ N * t ^ lam := hbase
          _ = t * (N * t ^ (lam - 1)) := by rw [e1]; ring
      exact le_of_mul_le_mul_left this ht0
    simp only [xPair, pow_zero, mul_one, Fa, Fb, if_true]
    refine ⟨?_, ?_⟩
    · rcases le_total lam 2 with hl | hl
      · rw [min_eq_left hl, sub_self, Real.rpow_zero]
        have : t ^ (lam - 2) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
        nlinarith
      · rw [min_eq_right hl]
        have : 1 ≤ t ^ (lam - 2) := Real.one_le_rpow ht1.le (by linarith)
        nlinarith
    · have : 0 ≤ t ^ (lam - 1) := by positivity
      nlinarith
  | succ j ih =>
    intro hj
    obtain ⟨ihA, ihB⟩ := ih (by omega)
    set N : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) with hNdef
    have sa := lw_s_a r hr t z h2 j (by omega)
    have sb := lw_s_b r hr t z h2 j (by omega)
    have pa := hs ⟨2 * j, by omega⟩
    have pb := hs ⟨2 * j + 1, by omega⟩
    set τ : ℝ := t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) with hτ
    have hτ0 : 0 < τ := by positivity
    set ya := fext z.2.2.2 (3 * j + 2) with hya
    set yb := fext z.2.2.2 (3 * j + 3) with hyb
    set yc := fext z.2.2.2 (3 * j + 4) with hyc
    have ya0 : 0 ≤ ya := fext_nonneg _ (fun i => (hy i).le) _
    have yb0 : 0 ≤ yb := fext_nonneg _ (fun i => (hy i).le) _
    have yc0 : 0 ≤ yc := fext_nonneg _ (fun i => (hy i).le) _
    rw [sa] at pa
    rw [sb] at pb
    have hty : 0 ≤ τ * yc := by positivity
    have hta : 0 ≤ t * ya := by positivity
    have htb : 0 ≤ t * yb := by positivity
    have key := flow_step t ht1 lam (xPair lam j).1 (xPair lam j).2 (1 / 2 ^ (j + 1))
      ((N + 1) * 2 ^ j) (Fa z.2.2.2 j) (Fb z.2.2.2 j) ya yb yc (by positivity) ihA ihB ya0 yb0 yc0
      (by linarith) (by linarith) (by linarith) (by linarith)
    have hxp : xPair lam (j + 1) = (1 + min (xPair lam j).1 (xPair lam j).2,
        (1 - 1 / 2 ^ (j + 1)) + max (xPair lam j).1 (xPair lam j).2) := by
      rw [xPair]
    have eFa : Fa z.2.2.2 (j + 1) = ya + yb := by
      simp only [Fa]
      rw [if_neg (by omega), hya, hyb]
      congr 2 <;> omega
    have eFb : Fb z.2.2.2 (j + 1) = yc := by
      simp only [Fb]
      rw [if_neg (by omega), hyc]
      congr 1
    rw [hxp, eFa, eFb]
    simp only
    have e2 : (N + 1) * 2 ^ (j + 1) = 2 * ((N + 1) * 2 ^ j) := by ring
    rw [e2]
    exact ⟨key.1, key.2⟩


lemma log_sandwich (t : ℝ) (ht1 : 1 < t) (x A ρ U D θ : ℝ) (hx : 0 < x) (hθ : θ < 1)
    (hD : 0 < D) (hup : x ≤ U * t ^ A) (hlow : (1 - θ) * t ^ A ≤ x * D)
    (hU : U ≤ t ^ ρ) (hDθ : D / (1 - θ) ≤ t ^ ρ) (hU0 : 0 ≤ U) :
    |Real.logb t x - A| ≤ ρ := by
  have ht0 : 0 < t := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  rw [abs_le]
  constructor
  · -- A - ρ ≤ logb x
    rw [show -ρ ≤ Real.logb t x - A ↔ A - ρ ≤ Real.logb t x by constructor <;> intro h <;> linarith]
    rw [Real.le_logb_iff_rpow_le ht1 hx, Real.rpow_sub ht0]
    have hA : 0 < t ^ A := by positivity
    have hρ : 0 < t ^ ρ := by positivity
    rw [div_le_iff₀ hρ]
    have h2 : t ^ A ≤ x * (D / (1 - θ)) := by
      rw [mul_div_assoc', le_div_iff₀ h1θ]; linarith
    calc t ^ A ≤ x * (D / (1 - θ)) := h2
      _ ≤ x * t ^ ρ := mul_le_mul_of_nonneg_left hDθ hx.le
  · rw [sub_le_iff_le_add, add_comm, Real.logb_le_iff_le_rpow ht1 hx, Real.rpow_add ht0]
    calc x ≤ U * t ^ A := hup
      _ ≤ t ^ ρ * t ^ A := mul_le_mul_of_nonneg_right hU (by positivity)
      _ = t ^ A * t ^ ρ := mul_comm _ _

lemma lower_coord (t : ℝ) (ht1 : 1 < t) (x s Fcap D θ lam A : ℝ) (hx : 0 < x)
    (hxs : (1 - θ) * t ^ lam ≤ x * s) (hs : s ≤ Fcap) (hF : Fcap ≤ D * t ^ (lam - A)) :
    (1 - θ) * t ^ A ≤ x * D := by
  have ht0 : 0 < t := by linarith
  have e : t ^ lam = t ^ A * t ^ (lam - A) := by
    rw [← Real.rpow_add ht0]; congr 1; ring
  have hp : 0 < t ^ (lam - A) := by positivity
  have h1 : (1 - θ) * t ^ A * t ^ (lam - A) ≤ x * D * t ^ (lam - A) := by
    calc (1 - θ) * t ^ A * t ^ (lam - A) = (1 - θ) * t ^ lam := by rw [e]; ring
      _ ≤ x * s := hxs
      _ ≤ x * (D * t ^ (lam - A)) := mul_le_mul_of_nonneg_left (hs.trans hF) hx.le
      _ = x * D * t ^ (lam - A) := by ring
  exact le_of_mul_le_mul_right h1 hp

lemma two_pow_le_factorial (n : ℕ) : 2 ^ n ≤ (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.factorial_succ (n + 1)]
    have : 2 ≤ n + 1 + 1 := by omega
    calc 2 ^ n * 2 ≤ (n + 1).factorial * (n + 1 + 1) := Nat.mul_le_mul ih this
      _ = (n + 1 + 1) * (n + 1).factorial := by ring

lemma const_sq_le (r j : ℕ) (hr : 1 ≤ r) (hj : j < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (5 * (r : ℝ) * 2 ^ j / (1 - θ)) ^ 2 ≤
      max (Nat.factorial (10 * r - 2) : ℝ) ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3) := by
  refine le_trans ?_ (le_max_right _ _)
  have h1θ : 0 < 1 - θ := by linarith
  have h1θ1 : 1 - θ ≤ 1 := by linarith
  set F : ℕ := Nat.factorial (10 * r - 1) with hF
  have hF1 : 1 ≤ F := Nat.factorial_pos _
  have h5 : 5 * r ≤ F := le_trans (by omega) (Nat.self_le_factorial (10 * r - 1))
  have h2 : 2 ^ j ≤ F := by
    calc 2 ^ j ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (r - 1 + 1).factorial := two_pow_le_factorial _
      _ ≤ F := Nat.factorial_le (by omega)
  have h3 : 5 * r * 2 ^ j ≤ F * F := Nat.mul_le_mul h5 h2
  have h3' : (5 * (r : ℝ) * 2 ^ j) ≤ (F : ℝ) * F := by exact_mod_cast h3
  have hF1' : (1 : ℝ) ≤ F := by exact_mod_cast hF1
  have h5' : (0 : ℝ) ≤ 5 * (r : ℝ) * 2 ^ j := by positivity
  rw [div_pow]
  have h4 : (5 * (r : ℝ) * 2 ^ j) ^ 2 ≤ (F : ℝ) ^ 24 := by
    calc (5 * (r : ℝ) * 2 ^ j) ^ 2 ≤ ((F : ℝ) * F) ^ 2 := pow_le_pow_left₀ h5' h3' 2
      _ = (F : ℝ) ^ 4 := by ring
      _ ≤ (F : ℝ) ^ 24 := pow_le_pow_right₀ hF1' (by norm_num)
  have h6 : (1 - θ) ^ 3 ≤ (1 - θ) ^ 2 := pow_le_pow_of_le_one h1θ.le h1θ1 (by norm_num)
  have h7 : 0 < (1 - θ) ^ 3 := by positivity
  rw [div_le_div_iff₀ (by positivity) h7]
  calc (5 * (r : ℝ) * 2 ^ j) ^ 2 * (1 - θ) ^ 3 ≤ (F : ℝ) ^ 24 * (1 - θ) ^ 3 :=
        mul_le_mul_of_nonneg_right h4 h7.le
    _ ≤ (F : ℝ) ^ 24 * (1 - θ) ^ 2 := mul_le_mul_of_nonneg_left h6 (by positivity)


theorem nbhd_log_close (r : ℕ) (hr : 1 ≤ r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (t : ℝ)
    (ht : (max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) ^ (2 ^ (r - 1)) < t)
    (z : PDPoint (2 * r) (3 * r - 1)) (hz : z ∈ lwWideNeighborhood r θ t)
    (h0 : 1 ≤ dualityMeasure z) (h2 : dualityMeasure z ≤ t ^ 2) (j : ℕ) (hj : j < r) :
    |Real.logb t (z.1 ⟨2 * j, by omega⟩) - (xPair (Real.logb t (dualityMeasure z)) j).1| ≤
        Real.logb t (max (Nat.factorial (10 * r - 2) : ℝ)
          ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) / 2 ∧
    |Real.logb t (z.1 ⟨2 * j + 1, by omega⟩) - (xPair (Real.logb t (dualityMeasure z)) j).2| ≤
        Real.logb t (max (Nat.factorial (10 * r - 2) : ℝ)
          ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) / 2 := by
  set M : ℝ := max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3) with hM
  have hM1 : (1 : ℝ) ≤ M :=
    le_max_of_le_left (by exact_mod_cast Nat.factorial_pos _)
  have hMpos : 0 < M := by linarith
  have ht1 : 1 < t := lt_of_le_of_lt (one_le_pow₀ hM1) ht
  have ht0 : 0 < t := by linarith
  have hz' : z ∈ wideNeighborhood (lwA r t) (lwB r t) (lwC r) θ := hz
  obtain ⟨hfeas, hxs, hwy⟩ := hz'
  have hμpos : 0 < dualityMeasure z := by linarith
  set lam : ℝ := Real.logb t (dualityMeasure z) with hlam
  have hμ : dualityMeasure z = t ^ lam := (Real.rpow_logb ht0 ht1.ne' hμpos).symm
  have hup := lw_upper r hr t ht1 z hfeas lam (le_of_eq hμ) j hj
  have hdual := lw_dual_bound r hr t ht1 z hfeas lam hμ j hj
  have hsa := lw_s_a r hr t z hfeas.2.1 j hj
  have hsb := lw_s_b r hr t z hfeas.2.1 j hj
  obtain ⟨hfe1, hfe2, hx, hw, hs, hy⟩ := hfeas
  set N : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) with hNdef
  have hN5 : N + 1 = 5 * (r : ℝ) := by
    have : 2 * r + (3 * r - 1) + 1 = 5 * r := by omega
    rw [hNdef]
    exact_mod_cast this
  have hN0 : 0 ≤ N := by positivity
  set ρ : ℝ := Real.logb t M / 2 with hρ
  have hρ2 : (t ^ ρ) ^ 2 = M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
      show ρ * ((2 : ℕ) : ℝ) = Real.logb t M by rw [hρ]; push_cast; ring,
      Real.rpow_logb ht0 ht1.ne' hMpos]
  set D : ℝ := (N + 1) * 2 ^ j with hD
  set U : ℝ := N * 2 ^ j with hU
  have hD0 : 0 < D := by rw [hD]; positivity
  have hUD : U ≤ D := by rw [hU, hD]; nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) j]
  have hC : D / (1 - θ) ≤ t ^ ρ := by
    have hsq := const_sq_le r j hr hj θ hθ0 hθ1
    have hDC : D / (1 - θ) = 5 * (r : ℝ) * 2 ^ j / (1 - θ) := by rw [hD, hN5]
    rw [hDC]
    have htρ : 0 < t ^ ρ := by positivity
    by_contra hcon
    push_neg at hcon
    have : (t ^ ρ) ^ 2 < (5 * (r : ℝ) * 2 ^ j / (1 - θ)) ^ 2 := by
      apply pow_lt_pow_left₀ hcon htρ.le (by norm_num)
    rw [hρ2] at this
    linarith
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hUρ : U ≤ t ^ ρ := by
    refine hUD.trans (le_trans ?_ hC)
    rw [le_div_iff₀ (by linarith : 0 < 1 - θ)]
    nlinarith
  have main : ∀ (x s Fc A : ℝ), 0 < x → (1 - θ) * dualityMeasure z ≤ x * s → s ≤ Fc →
      Fc ≤ D * t ^ (lam - A) → x ≤ U * t ^ A → |Real.logb t x - A| ≤ ρ := by
    intro x s Fc A hx hxs' hs' hF hup'
    exact log_sandwich t ht1 x A ρ U D θ hx hθ1 hD0 hup'
      (lower_coord t ht1 x s Fc D θ lam A hx (by rw [← hμ]; exact hxs') hs' hF) hUρ hC hU0
  have ya0 := fext_nonneg z.2.2.2 (fun i => (hy i).le) (3 * j + 2)
  have yb0 := fext_nonneg z.2.2.2 (fun i => (hy i).le) (3 * j + 3)
  have yc0 := fext_nonneg z.2.2.2 (fun i => (hy i).le) (3 * j + 4)
  have hτ0 : 0 < t ^ ((1 : ℝ) - 1 / 2 ^ (j + 1)) := by positivity
  constructor
  · refine main _ (z.2.2.1 ⟨2 * j, by omega⟩) (Fa z.2.2.2 j) _ (hx _) (hxs _) ?_ ?_ hup.1
    · rw [hsa]
      have := mul_nonneg ht0.le ya0
      have := mul_nonneg hτ0.le yc0
      linarith
    · exact hdual.1
  · refine main _ (z.2.2.1 ⟨2 * j + 1, by omega⟩) (Fb z.2.2.2 j) _ (hx _) (hxs _) ?_ ?_ hup.2
    · rw [hsb]
      have := mul_nonneg ht0.le yb0
      have := mul_nonneg hτ0.le yc0
      linarith
    · exact hdual.2





lemma xPair_delta_succ (lam : ℝ) (j : ℕ) :
    (xPair lam (j + 1)).1 - (xPair lam (j + 1)).2 =
      1 / 2 ^ (j + 1) - |(xPair lam j).1 - (xPair lam j).2| := by
  have h : (xPair lam (j + 1)) = (1 + min (xPair lam j).1 (xPair lam j).2,
      (1 - 1 / 2 ^ (j + 1)) + max (xPair lam j).1 (xPair lam j).2) := by
    rw [xPair]
  rw [h]
  simp only
  rcases le_total (xPair lam j).1 (xPair lam j).2 with hle | hle
  · rw [min_eq_left hle, max_eq_right hle, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right hle, max_eq_left hle, abs_of_nonneg (by linarith)]; ring

lemma xPair_cell (n : ℕ) : ∀ (k : ℕ), k < 2 ^ n → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
    (xPair (2 * ((k : ℝ) + u) / 2 ^ n) n).1 - (xPair (2 * ((k : ℝ) + u) / 2 ^ n) n).2
      = (-1) ^ (k + 1) * (1 - 2 * u) / 2 ^ n := by
  induction n with
  | zero =>
    intro k hk u hu0 hu1
    have : k = 0 := by simpa using hk
    subst this
    simp only [xPair, pow_zero, Nat.cast_zero, zero_add, div_one]
    rw [min_eq_left (by linarith)]
    ring
  | succ n ih =>
    intro k hk u hu0 hu1
    obtain ⟨k0, e, he, hk0⟩ : ∃ k0 e : ℕ, e < 2 ∧ k = 2 * k0 + e := ⟨k / 2, k % 2, by omega, by omega⟩
    have hk0' : k0 < 2 ^ n := by rw [pow_succ] at hk; omega
    have hlam : 2 * ((k : ℝ) + u) / 2 ^ (n + 1) = 2 * ((k0 : ℝ) + (e + u) / 2) / 2 ^ n := by
      rw [hk0]; push_cast; rw [pow_succ]; field_simp; ring
    rw [xPair_delta_succ, hlam]
    have := ih k0 hk0' ((e + u) / 2) (by positivity) (by interval_cases e <;> simp <;> linarith)
    rw [this]
    interval_cases e
    · simp only [hk0]
      have : (-1 : ℝ) ^ (2 * k0 + 0 + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [this, pow_succ]
      have hpos : (0 : ℝ) < 2 ^ n := by positivity
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hpos]
      simp only [abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonneg (by linarith)]
      field_simp
      ring
    · simp only [hk0]
      have : (-1 : ℝ) ^ (2 * k0 + 1 + 1) = 1 := by rw [show 2 * k0 + 1 + 1 = 2 * (k0 + 1) by ring, pow_mul]; norm_num
      rw [this, pow_succ]
      have hpos : (0 : ℝ) < 2 ^ n := by positivity
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hpos]
      simp only [abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonpos (by linarith)]
      field_simp
      ring

theorem xPair_zigzag (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ 2 ^ (r - 1)) :
    (xPair (2 * (k : ℝ) / 2 ^ (r - 1)) (r - 1)).1 - (xPair (2 * (k : ℝ) / 2 ^ (r - 1)) (r - 1)).2
      = (-1) ^ (k + 1) / 2 ^ (r - 1) := by
  rcases Nat.lt_or_ge k (2 ^ (r - 1)) with h | h
  · have := xPair_cell (r - 1) k h 0 le_rfl zero_le_one
    simp only [add_zero, mul_zero, sub_zero, mul_one] at this
    rw [this]
  · have hk' : k = 2 ^ (r - 1) := le_antisymm hk h
    have hpos : 0 < 2 ^ (r - 1) := by positivity
    have := xPair_cell (r - 1) (k - 1) (by omega) 1 zero_le_one le_rfl
    have hc : ((k - 1 : ℕ) : ℝ) + 1 = k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at this
    rw [this]
    have : (-1 : ℝ) ^ (k - 1 + 1) = (-1) ^ k := by rw [Nat.sub_add_cancel (by omega)]
    rw [this, pow_succ]
    ring


lemma xPair_succ' (lam : ℝ) (j : ℕ) (hj : 0 < j) :
    xPair lam j = (1 + min (xPair lam (j - 1)).1 (xPair lam (j - 1)).2,
      (1 - 1 / 2 ^ j) + max (xPair lam (j - 1)).1 (xPair lam (j - 1)).2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp [xPair]

lemma tropW_0 (lam : ℝ) : LogBarrierIPM.Curvature.tropW lam 1 = 2 := by
  unfold LogBarrierIPM.Curvature.tropW; simp

lemma tropW_1 (lam : ℝ) : LogBarrierIPM.Curvature.tropW lam 2 = 1 := by
  unfold LogBarrierIPM.Curvature.tropW; simp

lemma tropW_a (lam : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    LogBarrierIPM.Curvature.tropW lam (3 * j) = 1 + (xPair lam (j - 1)).1 := by
  unfold LogBarrierIPM.Curvature.tropW
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have : 3 * j / 3 - 1 = j - 1 := by omega
  rw [this]

lemma tropW_b (lam : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    LogBarrierIPM.Curvature.tropW lam (3 * j + 1) = 1 + (xPair lam (j - 1)).2 := by
  unfold LogBarrierIPM.Curvature.tropW
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have : (3 * j + 1) / 3 - 1 = j - 1 := by omega
  rw [this]

lemma tropW_c (lam : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    LogBarrierIPM.Curvature.tropW lam (3 * j + 2) = (xPair lam j).2 := by
  unfold LogBarrierIPM.Curvature.tropW
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have : (3 * j + 2) / 3 = j := by omega
  rw [this]





/-! ## w-block estimates -/

lemma fext_eq {n : ℕ} (f : Fin n → ℝ) (a : ℕ) (ha : a < n) : fext f a = f ⟨a, ha⟩ := by
  unfold fext; rw [dif_pos ha]

lemma low_step (t : ℝ) (ht1 : 1 < t) (lam e A D w y : ℝ) (hD : 0 < D) (hw : 0 < w)
    (hwy : (1 / 2 : ℝ) * t ^ lam ≤ w * y) (hy : t ^ e * y ≤ D * t ^ (lam - A)) :
    t ^ (e + A) ≤ 2 * D * w := by
  have ht0 : 0 < t := by linarith
  have he : 0 < t ^ e := by positivity
  have h1 : (1 / 2 : ℝ) * t ^ lam * t ^ e ≤ w * y * t ^ e := mul_le_mul_of_nonneg_right hwy he.le
  have h3 : w * (t ^ e * y) ≤ w * (D * t ^ (lam - A)) := mul_le_mul_of_nonneg_left hy hw.le
  have hsplit : t ^ lam * t ^ e = t ^ (e + A) * t ^ (lam - A) := by
    rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]; congr 1; ring
  have hp : 0 < t ^ (lam - A) := by positivity
  have h4 : t ^ (e + A) * t ^ (lam - A) ≤ (2 * D * w) * t ^ (lam - A) := by
    have h5 : (1 / 2 : ℝ) * (t ^ lam * t ^ e) ≤ w * (D * t ^ (lam - A)) := by
      calc (1 / 2 : ℝ) * (t ^ lam * t ^ e) = (1 / 2 : ℝ) * t ^ lam * t ^ e := by ring
        _ ≤ w * y * t ^ e := h1
        _ = w * (t ^ e * y) := by ring
        _ ≤ _ := h3
    rw [hsplit] at h5
    nlinarith [h5]
  exact le_of_mul_le_mul_right h4 hp

lemma bounds_of_UL (t : ℝ) (ht1 : 1 < t) (w A U L C : ℝ) (hw : 0 < w)
    (hU : w ≤ U * t ^ A) (hL : t ^ A ≤ L * w) (hUC : U ≤ C) (hLC : L ≤ C) (hC : 0 < C)
    (hU0 : 0 ≤ U) :
    t ^ A / C ≤ w ∧ w ≤ C * t ^ A := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < t ^ A := by positivity
  constructor
  · rw [div_le_iff₀ hC]
    nlinarith [mul_le_mul_of_nonneg_right hLC hw.le]
  · calc w ≤ U * t ^ A := hU
      _ ≤ C * t ^ A := mul_le_mul_of_nonneg_right hUC hp.le

theorem lw_w_bounds (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht1 : 1 < t) (z : PDPoint (2 * r) (3 * r - 1))
    (hfeas : z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r)) (lam : ℝ)
    (hμ : dualityMeasure z = t ^ lam)
    (hwy : ∀ i, (1 / 2 : ℝ) * t ^ lam ≤ z.2.1 i * z.2.2.2 i) (i : Fin (3 * r - 1)) :
    t ^ (LogBarrierIPM.Curvature.tropW lam ((i : ℕ) + 1)) /
        (2 * (((2 * r + (3 * r - 1) : ℕ) : ℝ) + 1) * 2 ^ r) ≤ z.2.1 i ∧
      z.2.1 i ≤ (2 * (((2 * r + (3 * r - 1) : ℕ) : ℝ) + 1) * 2 ^ r) *
        t ^ (LogBarrierIPM.Curvature.tropW lam ((i : ℕ) + 1)) := by
  have ht0 : 0 < t := by linarith
  have hup := lw_upper r hr t ht1 z hfeas lam (le_of_eq hμ)
  have hdual := lw_dual_bound r hr t ht1 z hfeas lam hμ
  have hbase := lw_dual_base r hr t ht1 z hfeas
  have hfe1 := hfeas.1
  obtain ⟨_, h2, hx, hw, hs, hy⟩ := hfeas
  set N : ℝ := ((2 * r + (3 * r - 1) : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ 2 * r + (3 * r - 1) := by omega
    rw [hNdef]; exact_mod_cast this
  have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hpw : ∀ k, k ≤ r → (2 : ℝ) ^ k ≤ 2 ^ r := fun k hk =>
    pow_le_pow_right₀ (by norm_num) hk
  set C : ℝ := 2 * (N + 1) * 2 ^ r with hCdef
  have hCpos : 0 < C := by positivity
  have hrowi := congrFun hfe1 i
  simp only [Pi.add_apply] at hrowi
  have hwi := hw i
  have yfe : ∀ a : ℕ, 0 ≤ fext z.2.2.2 a := fun a => fext_nonneg _ (fun i => (hy i).le) a
  have hyi : z.2.2.2 i = fext z.2.2.2 (i : ℕ) := (fext_eq _ _ i.2).symm
  have hwyi := hwy i
  rw [hyi] at hwyi
  have fin : ∀ (A A' e D U : ℝ), e + A' = A → 0 < D → 0 ≤ U → U ≤ C → 2 * D ≤ C →
      z.2.1 i ≤ U * t ^ A → t ^ e * fext z.2.2.2 (i : ℕ) ≤ D * t ^ (lam - A') →
      t ^ A / C ≤ z.2.1 i ∧ z.2.1 i ≤ C * t ^ A := by
    intro A A' e D U hA hD hU0 hUC h2D hU hy'
    have := low_step t ht1 lam e A' D (z.2.1 i) (fext z.2.2.2 (i : ℕ)) hD hwi hwyi hy'
    rw [hA] at this
    exact bounds_of_UL t ht1 _ A U (2 * D) C hwi hU this hUC h2D hCpos hU0
  have hC2N : 2 * N ≤ C := by
    rw [hCdef]
    calc 2 * N ≤ 2 * (N + 1) * 1 := by linarith
      _ ≤ 2 * (N + 1) * 2 ^ r := mul_le_mul_of_nonneg_left h2r (by positivity)
  have hC1 : 1 ≤ C := by linarith
  rcases Nat.lt_or_ge (i : ℕ) 2 with hi2 | hi2
  · -- i = 0 or i = 1
    have hyb0 := yfe 0
    have hyb1 := yfe 1
    rw [hμ] at hbase
    rcases Nat.lt_or_ge (i : ℕ) 1 with hi1 | hi1
    · have hi0 : (i : ℕ) = 0 := by omega
      have hrow : (lwA r t *ᵥ z.1) i = z.1 ⟨0, by omega⟩ := by
        have : i = ⟨0, by omega⟩ := Fin.ext hi0
        exact (congrArg (fun k => (lwA r t *ᵥ z.1) k) this).trans (lw_row_0 r t hr z.1)
      have hB : lwB r t i = t ^ 2 := by simp [lwB, hi0]
      rw [hrow, hB] at hrowi
      have hx0 := hx ⟨0, by omega⟩
      have hix : (i : ℕ) + 1 = 1 := by omega
      rw [hix, tropW_0]
      have hyy : fext z.2.2.2 (i : ℕ) = fext z.2.2.2 0 := by rw [hi0]
      refine fin 2 0 2 N 1 (by norm_num) (by linarith) (by norm_num) hC1 hC2N ?_ ?_
      · rw [Real.rpow_two]; linarith
      · rw [hyy, Real.rpow_two, sub_zero]
        linarith [mul_nonneg ht0.le hyb1]
    · have hi0 : (i : ℕ) = 1 := by omega
      have hrow : (lwA r t *ᵥ z.1) i = z.1 ⟨1, by omega⟩ := by
        have : i = ⟨1, by omega⟩ := Fin.ext hi0
        exact (congrArg (fun k => (lwA r t *ᵥ z.1) k) this).trans (lw_row_1 r t hr z.1)
      have hB : lwB r t i = t := by simp [lwB, hi0]
      rw [hrow, hB] at hrowi
      have hx0 := hx ⟨1, by omega⟩
      have hix : (i : ℕ) + 1 = 2 := by omega
      rw [hix, tropW_1]
      have hyy : fext z.2.2.2 (i : ℕ) = fext z.2.2.2 1 := by rw [hi0]
      refine fin 1 0 1 N 1 (by norm_num) (by linarith) (by norm_num) hC1 hC2N ?_ ?_
      · rw [Real.rpow_one]; linarith
      · rw [hyy, Real.rpow_one, sub_zero]
        linarith [mul_nonneg (sq_nonneg t) hyb0]
  · obtain ⟨j, hj1, hjr, hcase⟩ : ∃ j, 1 ≤ j ∧ j < r ∧
        ((i : ℕ) = 3 * j - 1 ∨ (i : ℕ) = 3 * j ∨ (i : ℕ) = 3 * j + 1) :=
      ⟨((i : ℕ) + 1) / 3, by omega, by omega, by omega⟩
    have hB : lwB r t i = 0 := by
      simp only [lwB]; rw [if_neg (by omega), if_neg (by omega)]
    have hj1' : j - 1 + 1 = j := by omega
    have hDle : 2 * ((N + 1) * 2 ^ (j - 1)) ≤ C := by
      calc 2 * ((N + 1) * 2 ^ (j - 1)) = (2 * (N + 1)) * 2 ^ (j - 1) := by ring
        _ ≤ (2 * (N + 1)) * 2 ^ r := mul_le_mul_of_nonneg_left (hpw _ (by omega)) (by positivity)
    rcases hcase with hc | hc | hc
    · -- row a
      have hix : (i : ℕ) + 1 = 3 * j := by omega
      rw [hix, tropW_a lam j hj1]
      have hrow : (lwA r t *ᵥ z.1) i = z.1 ⟨2 * j, by omega⟩ - t * z.1 ⟨2 * j - 2, by omega⟩ :=
        lw_row_a' r t z.1 j (i : ℕ) (2 * j) (2 * j - 2) hj1 hjr hc rfl rfl i.2 (by omega) (by omega)
      rw [hrow, hB] at hrowi
      have hxp := hx ⟨2 * j, by omega⟩
      have hxq := (hup (j - 1) (by omega)).1
      rw [xcongr z.1 (2 * (j - 1)) (2 * j - 2) (by omega) (by omega) (by omega)] at hxq
      have hsa := lw_s_a r hr t z h2 (j - 1) (by omega)
      have hsj := hs ⟨2 * (j - 1), by omega⟩
      rw [hsa] at hsj
      have hyc0 := yfe (3 * (j - 1) + 4)
      have hpowpos : 0 < t ^ ((1 : ℝ) - 1 / 2 ^ (j - 1 + 1)) := by positivity
      have hFa := (hdual (j - 1) (by omega)).1
      have hyidx : fext z.2.2.2 (i : ℕ) = fext z.2.2.2 (3 * (j - 1) + 2) := by congr 1; omega
      have hexp : t ^ (1 + (xPair lam (j - 1)).1) = t * t ^ (xPair lam (j - 1)).1 := by
        rw [Real.rpow_add ht0, Real.rpow_one]
      refine fin (1 + (xPair lam (j - 1)).1) (xPair lam (j - 1)).1 1 ((N + 1) * 2 ^ (j - 1))
        (N * 2 ^ (j - 1)) (by ring) (by positivity) (by positivity) ?_ hDle ?_ ?_
      · rw [hCdef]
        exact mul_le_mul (by linarith) (hpw _ (by omega)) (by positivity) (by positivity)
      · rw [hexp]
        linarith [mul_le_mul_of_nonneg_left hxq ht0.le]
      · rw [hyidx, Real.rpow_one]
        linarith [mul_nonneg hpowpos.le hyc0]
    · -- row b
      have hix : (i : ℕ) + 1 = 3 * j + 1 := by omega
      rw [hix, tropW_b lam j hj1]
      have hrow : (lwA r t *ᵥ z.1) i = z.1 ⟨2 * j, by omega⟩ - t * z.1 ⟨2 * j - 1, by omega⟩ :=
        lw_row_b' r t z.1 j (i : ℕ) (2 * j) (2 * j - 1) hj1 hjr hc rfl rfl i.2 (by omega) (by omega)
      rw [hrow, hB] at hrowi
      have hxp := hx ⟨2 * j, by omega⟩
      have hxq := (hup (j - 1) (by omega)).2
      rw [xcongr z.1 (2 * (j - 1) + 1) (2 * j - 1) (by omega) (by omega) (by omega)] at hxq
      have hsb := lw_s_b r hr t z h2 (j - 1) (by omega)
      have hsj := hs ⟨2 * (j - 1) + 1, by omega⟩
      rw [hsb] at hsj
      have hyc0 := yfe (3 * (j - 1) + 4)
      have hpowpos : 0 < t ^ ((1 : ℝ) - 1 / 2 ^ (j - 1 + 1)) := by positivity
      have hFb := (hdual (j - 1) (by omega)).2
      have hyidx : fext z.2.2.2 (i : ℕ) = fext z.2.2.2 (3 * (j - 1) + 3) := by congr 1; omega
      have hexp : t ^ (1 + (xPair lam (j - 1)).2) = t * t ^ (xPair lam (j - 1)).2 := by
        rw [Real.rpow_add ht0, Real.rpow_one]
      refine fin (1 + (xPair lam (j - 1)).2) (xPair lam (j - 1)).2 1 ((N + 1) * 2 ^ (j - 1))
        (N * 2 ^ (j - 1)) (by ring) (by positivity) (by positivity) ?_ hDle ?_ ?_
      · rw [hCdef]
        exact mul_le_mul (by linarith) (hpw _ (by omega)) (by positivity) (by positivity)
      · rw [hexp]
        linarith [mul_le_mul_of_nonneg_left hxq ht0.le]
      · rw [hyidx, Real.rpow_one]
        linarith [mul_nonneg hpowpos.le hyc0]
    · -- row c
      have hix : (i : ℕ) + 1 = 3 * j + 2 := by omega
      rw [hix, tropW_c lam j hj1, xPair_succ' lam j (by omega)]
      dsimp only
      have hrow : (lwA r t *ᵥ z.1) i = z.1 ⟨2 * j + 1, by omega⟩
          - t ^ ((1 : ℝ) - 1 / 2 ^ j) * z.1 ⟨2 * j - 2, by omega⟩
          - t ^ ((1 : ℝ) - 1 / 2 ^ j) * z.1 ⟨2 * j - 1, by omega⟩ :=
        lw_row_c' r t z.1 j (i : ℕ) (2 * j + 1) (2 * j - 2) (2 * j - 1) hj1 hjr hc rfl rfl rfl i.2
          (by omega) (by omega) (by omega)
      rw [hrow, hB] at hrowi
      have hxp := hx ⟨2 * j + 1, by omega⟩
      have hxq1 := (hup (j - 1) (by omega)).1
      have hxq2 := (hup (j - 1) (by omega)).2
      rw [xcongr z.1 (2 * (j - 1)) (2 * j - 2) (by omega) (by omega) (by omega)] at hxq1
      rw [xcongr z.1 (2 * (j - 1) + 1) (2 * j - 1) (by omega) (by omega) (by omega)] at hxq2
      have hsa := lw_s_a r hr t z h2 (j - 1) (by omega)
      have hsb := lw_s_b r hr t z h2 (j - 1) (by omega)
      have hsja := hs ⟨2 * (j - 1), by omega⟩
      have hsjb := hs ⟨2 * (j - 1) + 1, by omega⟩
      rw [hsa] at hsja
      rw [hsb] at hsjb
      rw [hj1'] at hsja hsjb
      have hya0 := yfe (3 * (j - 1) + 2)
      have hyb0 := yfe (3 * (j - 1) + 3)
      have hFa := (hdual (j - 1) (by omega)).1
      have hFb := (hdual (j - 1) (by omega)).2
      have hyidx : fext z.2.2.2 (i : ℕ) = fext z.2.2.2 (3 * (j - 1) + 4) := by congr 1; omega
      set a : ℝ := (xPair lam (j - 1)).1 with ha
      set b : ℝ := (xPair lam (j - 1)).2 with hb
      set τ : ℝ := t ^ ((1 : ℝ) - 1 / 2 ^ j) with hτ
      have hτ0 : 0 < τ := by positivity
      have hmono : ∀ p q : ℝ, p ≤ q → t ^ p ≤ t ^ q :=
        fun p q h => Real.rpow_le_rpow_of_exponent_le ht1.le h
      have hta : t ^ a ≤ t ^ (max a b) := hmono _ _ (le_max_left _ _)
      have htb : t ^ b ≤ t ^ (max a b) := hmono _ _ (le_max_right _ _)
      have hexp : t ^ ((1 - 1 / 2 ^ j : ℝ) + max a b) = τ * t ^ (max a b) := by
        rw [hτ, Real.rpow_add ht0]
      refine fin ((1 - 1 / 2 ^ j : ℝ) + max a b) (max a b) ((1 : ℝ) - 1 / 2 ^ j)
        ((N + 1) * 2 ^ (j - 1)) (N * 2 ^ j) rfl (by positivity) (by positivity) ?_ hDle ?_ ?_
      · rw [hCdef]
        exact mul_le_mul (by linarith) (hpw _ hjr.le) (by positivity) (by positivity)
      · rw [hexp]
        have h2j : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
          rw [← pow_succ']; congr 1; omega
        have hNp : 0 ≤ N * 2 ^ (j - 1) := by positivity
        have e1 : τ * z.1 ⟨2 * j - 2, by omega⟩ ≤ τ * (N * 2 ^ (j - 1) * t ^ (max a b)) :=
          mul_le_mul_of_nonneg_left (hxq1.trans (mul_le_mul_of_nonneg_left hta hNp)) hτ0.le
        have e2 : τ * z.1 ⟨2 * j - 1, by omega⟩ ≤ τ * (N * 2 ^ (j - 1) * t ^ (max a b)) :=
          mul_le_mul_of_nonneg_left (hxq2.trans (mul_le_mul_of_nonneg_left htb hNp)) hτ0.le
        rw [h2j]
        linarith
      · have hyc0 := yfe (3 * (j - 1) + 4)
        have hlt1 : τ * fext z.2.2.2 (3 * (j - 1) + 4) ≤ Fa z.2.2.2 (j - 1) := by
          linarith [mul_nonneg ht0.le hya0]
        have hlt2 : τ * fext z.2.2.2 (3 * (j - 1) + 4) ≤ Fb z.2.2.2 (j - 1) := by
          linarith [mul_nonneg ht0.le hyb0]
        rw [hyidx]
        rcases le_total a b with hab | hab
        · rw [max_eq_right hab]; exact hlt2.trans hFb
        · rw [max_eq_left hab]; exact hlt1.trans hFa

end LogBarrierIPM.Iterations


namespace LogBarrierIPM.Curvature
open LogBarrierIPM.Iterations

lemma tropX_eq (lam : ℝ) (k : ℕ) :
    tropX lam (k + 1) = if k % 2 = 0 then (xPair lam (k / 2)).1 else (xPair lam (k / 2)).2 := by
  unfold tropX
  by_cases hk : k % 2 = 0
  · have h1 : (k + 1) % 2 = 1 := by omega
    have h3 : (k + 1 - 1) / 2 = k / 2 := by omega
    rw [if_pos h1, if_pos hk, h3]
  · have h1 : ¬ ((k + 1) % 2 = 1) := by omega
    have h3 : (k + 1 - 2) / 2 = k / 2 := by omega
    rw [if_neg h1, if_neg hk, h3]


end LogBarrierIPM.Curvature


namespace LogBarrierIPM.Curvature
open Filter Topology LogBarrierIPM.Iterations

lemma logb_small (M ε t : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) (ht1 : 1 < t)
    (ht : Real.exp (Real.log M / ε) ≤ t) : Real.logb t M ≤ ε := by
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have ht0 : 0 < t := by linarith
  have h1 : Real.log M / ε ≤ Real.log t := (Real.le_log_iff_exp_le ht0).2 ht
  rw [div_le_iff₀ hε] at h1
  unfold Real.logb
  rw [div_le_iff₀ hlogt]
  linarith

lemma logb_of_bounds (t : ℝ) (ht1 : 1 < t) (w A C : ℝ) (hC : 1 ≤ C) (hw : 0 < w)
    (hl : t ^ A / C ≤ w) (hu : w ≤ C * t ^ A) : |Real.logb t w - A| ≤ Real.logb t C := by
  have ht0 : 0 < t := by linarith
  have hC0 : 0 < C := by linarith
  have hp : 0 < t ^ A := by positivity
  have e1 : Real.logb t (C * t ^ A) = Real.logb t C + A := by
    rw [Real.logb_mul hC0.ne' hp.ne', Real.logb_rpow ht0 ht1.ne']
  have e2 : Real.logb t (t ^ A / C) = A - Real.logb t C := by
    rw [Real.logb_div hp.ne' hC0.ne', Real.logb_rpow ht0 ht1.ne']
  have h1 : Real.logb t w ≤ Real.logb t (C * t ^ A) := Real.logb_le_logb_of_le ht1 hw hu
  have h2 : Real.logb t (t ^ A / C) ≤ Real.logb t w :=
    Real.logb_le_logb_of_le ht1 (by positivity) hl
  rw [abs_le]; constructor <;> linarith

lemma central_facts (r : ℕ) (t lam : ℝ) (z : SlackPoint (2 * r) (3 * r - 1))
    (hr : 1 ≤ r)
    (hz : IsSlackCentralPathPoint (lwA r t) (lwB r t) (lwC r) (t ^ lam) z) :
    z ∈ strictlyFeasible (lwA r t) (lwB r t) (lwC r) ∧ dualityMeasure z = t ^ lam ∧
      (∀ j, z.1 j * z.2.2.1 j = t ^ lam) ∧ (∀ i, z.2.1 i * z.2.2.2 i = t ^ lam) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hz
  have h4' : ∀ i, z.2.1 i * z.2.2.2 i = t ^ lam := fun i => by rw [mul_comm]; exact h4 i
  have h2' : z.2.2.1 - (lwA r t)ᵀ *ᵥ z.2.2.2 = lwC r := by
    ext j
    have := congrFun h2 j
    simp only [Pi.sub_apply, Pi.neg_apply] at this ⊢
    linarith
  refine ⟨⟨h1, h2', h5, h6, h8, h7⟩, ?_, h3, h4'⟩
  have e1 : z.1 ⬝ᵥ z.2.2.1 = ((2 * r : ℕ) : ℝ) * t ^ lam := by
    simp [dotProduct, h3]
  have e2 : z.2.1 ⬝ᵥ z.2.2.2 = ((3 * r - 1 : ℕ) : ℝ) * t ^ lam := by
    simp [dotProduct, h4']
  have hN : (0 : ℝ) < ((2 * r + (3 * r - 1) : ℕ) : ℝ) := by
    have : 0 < 2 * r + (3 * r - 1) := by omega
    exact_mod_cast this
  unfold dualityMeasure
  rw [e1, e2, div_eq_iff hN.ne']
  push_cast [Nat.cast_add]
  ring

theorem lw_central_path_log_limit (r : ℕ) (hr : 1 ≤ r) (lam : ℝ) (h0 : 0 ≤ lam) (h2 : lam ≤ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ z : SlackPoint (2 * r) (3 * r - 1),
      IsSlackCentralPathPoint (LogBarrierIPM.Iterations.lwA r t) (LogBarrierIPM.Iterations.lwB r t)
        (LogBarrierIPM.Iterations.lwC r) (t ^ lam) z →
      ∀ q, 0 < primalDualPoint z q ∧
        |Real.logb t (primalDualPoint z q) - tropCentralPathLW r lam q| ≤ ε := by
  set M : ℝ := max (Nat.factorial (10 * r - 2) : ℝ)
    ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - (1 / 2 : ℝ)) ^ 3) with hM
  set C : ℝ := 2 * (((2 * r + (3 * r - 1) : ℕ) : ℝ) + 1) * 2 ^ r with hC
  have hM1 : (1 : ℝ) ≤ M := le_max_of_le_left (by exact_mod_cast Nat.factorial_pos _)
  have hC1 : (1 : ℝ) ≤ C := by
    have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have hN0 : (0 : ℝ) ≤ ((2 * r + (3 * r - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hC]
    nlinarith
  have hev : ∀ᶠ t in atTop, 1 < t ∧ M ^ (2 ^ (r - 1)) < t ∧
      Real.exp (Real.log M / (2 * ε)) ≤ t ∧ Real.exp (Real.log C / ε) ≤ t :=
    (eventually_gt_atTop (1 : ℝ)).and ((eventually_gt_atTop _).and
      ((eventually_ge_atTop _).and (eventually_ge_atTop _)))
  filter_upwards [hev] with t ht z hz q
  obtain ⟨ht1, htM, htε1, htε2⟩ := ht
  have ht0 : 0 < t := by linarith
  obtain ⟨hfeas, hμ, hxs, hwy⟩ := central_facts r t lam z hr hz
  have hz' := hz
  obtain ⟨_, _, _, _, hxpos, hwpos, hypos, hspos⟩ := hz'
  have hlogM : Real.logb t M ≤ 2 * ε := logb_small M (2 * ε) t hM1 (by linarith) ht1 htε1
  have hlogC : Real.logb t C ≤ ε := logb_small C ε t hC1 hε ht1 htε2
  have hlogM2 : Real.logb t (max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - (1 / 2 : ℝ)) ^ 3)) / 2 ≤ ε := by
    show Real.logb t M / 2 ≤ ε
    linarith
  have hmem : z ∈ lwWideNeighborhood r (1 / 2) t := by
    refine ⟨hfeas, fun j => ?_, fun i => ?_⟩
    · rw [hμ, hxs j]; nlinarith [Real.rpow_pos_of_pos ht0 lam]
    · rw [hμ, hwy i]; nlinarith [Real.rpow_pos_of_pos ht0 lam]
  have hμ1 : 1 ≤ dualityMeasure z := by rw [hμ]; exact Real.one_le_rpow ht1.le h0
  have hμ2 : dualityMeasure z ≤ t ^ 2 := by
    rw [hμ, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht1.le (by simpa using h2)
  have hlogμ : Real.logb t (dualityMeasure z) = lam := by
    rw [hμ, Real.logb_rpow ht0 ht1.ne']
  -- x block
  have keyx : ∀ k : Fin (2 * r), |Real.logb t (z.1 k) - tropX lam (k.val + 1)| ≤ ε := by
    intro k
    have hj : k.val / 2 < r := by have := k.2; omega
    obtain ⟨hb1, hb2⟩ := nbhd_log_close r hr (1 / 2) (by norm_num) (by norm_num) t htM z hmem hμ1 hμ2
      (k.val / 2) hj
    rw [hlogμ] at hb1 hb2
    rw [tropX_eq]
    by_cases hk : k.val % 2 = 0
    · rw [if_pos hk]
      have e : z.1 k = z.1 ⟨2 * (k.val / 2), by have := k.2; omega⟩ :=
        congrArg z.1 (Fin.ext (by simp; omega))
      rw [e]
      exact hb1.trans hlogM2
    · rw [if_neg hk]
      have e : z.1 k = z.1 ⟨2 * (k.val / 2) + 1, by have := k.2; omega⟩ :=
        congrArg z.1 (Fin.ext (by simp; omega))
      rw [e]
      exact hb2.trans hlogM2
  -- w block
  have keyw : ∀ i : Fin (3 * r - 1), |Real.logb t (z.2.1 i) - tropW lam (i.val + 1)| ≤ ε := by
    intro i
    have hb := lw_w_bounds r hr t ht1 z hfeas lam hμ
      (fun i => by rw [hwy i]; nlinarith [Real.rpow_pos_of_pos ht0 lam]) i
    exact (logb_of_bounds t ht1 _ _ C hC1 (hwpos i) hb.1 hb.2).trans hlogC
  -- s and y blocks
  have keys : ∀ k : Fin (2 * r), |Real.logb t (z.2.2.1 k) - tropS lam (k.val + 1)| ≤ ε := by
    intro k
    have : z.2.2.1 k = t ^ lam / z.1 k := by
      rw [eq_div_iff (hxpos k).ne', mul_comm]; exact hxs k
    rw [this, Real.logb_div (Real.rpow_pos_of_pos ht0 lam).ne' (hxpos k).ne',
      Real.logb_rpow ht0 ht1.ne']
    have := keyx k
    unfold tropS
    rw [abs_sub_comm] at this
    calc |lam - Real.logb t (z.1 k) - (lam - tropX lam (k.val + 1))|
        = |tropX lam (k.val + 1) - Real.logb t (z.1 k)| := by congr 1; ring
      _ ≤ ε := this
  have keyy : ∀ i : Fin (3 * r - 1), |Real.logb t (z.2.2.2 i) - tropY lam (i.val + 1)| ≤ ε := by
    intro i
    have : z.2.2.2 i = t ^ lam / z.2.1 i := by
      rw [eq_div_iff (hwpos i).ne']; rw [mul_comm]; exact hwy i
    rw [this, Real.logb_div (Real.rpow_pos_of_pos ht0 lam).ne' (hwpos i).ne',
      Real.logb_rpow ht0 ht1.ne']
    have := keyw i
    unfold tropY
    rw [abs_sub_comm] at this
    calc |lam - Real.logb t (z.2.1 i) - (lam - tropW lam (i.val + 1))|
        = |tropW lam (i.val + 1) - Real.logb t (z.2.1 i)| := by congr 1; ring
      _ ≤ ε := this
  -- assemble
  refine Fin.addCases (fun q1 => ?_) (fun q2 => ?_) q
  · refine Fin.addCases (fun k => ?_) (fun i => ?_) q1
    · simp only [primalDualPoint, tropCentralPathLW, Fin.append_left]
      exact ⟨hxpos k, keyx k⟩
    · simp only [primalDualPoint, tropCentralPathLW, Fin.append_left, Fin.append_right]
      exact ⟨hwpos i, keyw i⟩
  · refine Fin.addCases (fun k => ?_) (fun i => ?_) q2
    · simp only [primalDualPoint, tropCentralPathLW, Fin.append_left, Fin.append_right]
      exact ⟨hspos k, keys k⟩
    · simp only [primalDualPoint, tropCentralPathLW, Fin.append_right]
      exact ⟨hypos i, keyy i⟩

end LogBarrierIPM.Curvature


namespace LogBarrierIPM.Curvature
open LogBarrierIPM.Iterations

/-- The primal block `(x, w)` of the tropical central path. -/
noncomputable def tropP (r : ℕ) (lam : ℝ) : Fin (2 * r + (3 * r - 1)) → ℝ :=
  Fin.append (fun k : Fin (2 * r) => tropX lam (k.val + 1))
    (fun i : Fin (3 * r - 1) => tropW lam (i.val + 1))

lemma xpa (lam : ℝ) (j : ℕ) :
    (xPair lam (j + 1)).1 = 1 + min (xPair lam j).1 (xPair lam j).2 := by
  rw [xPair]

lemma xpb (lam : ℝ) (j : ℕ) :
    (xPair lam (j + 1)).2 = (1 - 1 / 2 ^ (j + 1)) + max (xPair lam j).1 (xPair lam j).2 := by
  rw [xPair]

lemma xp0 (lam : ℝ) : xPair lam 0 = (min lam 2, 1) := by
  rw [xPair]

lemma half_le (j : ℕ) : (1 : ℝ) / 2 ^ (j + 1) ≤ 1 / 2 := by
  have : (2 : ℝ) ≤ 2 ^ (j + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact one_div_le_one_div_of_le (by norm_num) this

lemma xp_nonneg (lam : ℝ) (h0 : 0 ≤ lam) :
    ∀ j, 0 ≤ (xPair lam j).1 ∧ 0 ≤ (xPair lam j).2 := by
  intro j
  induction j with
  | zero => rw [xp0]; exact ⟨le_min h0 (by norm_num), by norm_num⟩
  | succ j ih =>
    rw [xpa, xpb]
    have h1 := half_le j
    refine ⟨?_, ?_⟩
    · have := le_min ih.1 ih.2
      linarith
    · have : 0 ≤ max (xPair lam j).1 (xPair lam j).2 := le_max_of_le_left ih.1
      linarith

noncomputable def mxf (lam : ℝ) (j : ℕ) : ℝ := max (xPair lam j).1 (xPair lam j).2

lemma mx_ge (lam : ℝ) (j n : ℕ) : mxf lam j + (n : ℝ) / 2 ≤ mxf lam (j + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := half_le (j + n)
    have h2 : mxf lam (j + n) + 1 / 2 ≤ mxf lam (j + n + 1) := by
      have hb := le_max_right (xPair lam (j + n + 1)).1 (xPair lam (j + n + 1)).2
      have hb2 := xpb lam (j + n)
      unfold mxf
      linarith
    have : j + (n + 1) = j + n + 1 := by omega
    rw [this]
    push_cast
    linarith

lemma xp_sum (lam : ℝ) (j : ℕ) :
    (xPair lam j).1 + (xPair lam j).2 = min lam 2 + 2 * j + 1 / 2 ^ j := by
  induction j with
  | zero => rw [xp0]; simp
  | succ j ih =>
    rw [xpa, xpb]
    have e : min (xPair lam j).1 (xPair lam j).2 + max (xPair lam j).1 (xPair lam j).2 =
        (xPair lam j).1 + (xPair lam j).2 := min_add_max _ _
    have h2 : (1 : ℝ) / 2 ^ (j + 1) = 1 / 2 ^ j / 2 := by
      rw [pow_succ]; field_simp
    push_cast
    nlinarith [e, ih, h2]

lemma tropW_nonneg (lam : ℝ) (h0 : 0 ≤ lam) (m : ℕ) : 0 ≤ tropW lam m := by
  unfold tropW
  have H := fun j => xp_nonneg lam h0 j
  split_ifs <;> first
    | linarith [(H (m / 3 - 1)).1, (H (m / 3 - 1)).2, (H (m / 3)).1, (H (m / 3)).2]
    | norm_num

lemma tropX_nonneg (lam : ℝ) (h0 : 0 ≤ lam) (k : ℕ) : 0 ≤ tropX lam (k + 1) := by
  rw [tropX_eq]
  split_ifs
  · exact (xp_nonneg lam h0 _).1
  · exact (xp_nonneg lam h0 _).2

theorem peak_aux (r : ℕ) (hr : 3 ≤ r) (lam : ℝ) (h0 : 0 ≤ lam)
    (hne : (xPair lam (r - 2)).1 ≠ (xPair lam (r - 2)).2) (q : Fin (2 * r + (3 * r - 1))) :
    tropP r lam q ≤ 1 + mxf lam (r - 2) ∧
    (tropP r lam q = 1 + mxf lam (r - 2) →
      (q = Fin.natAdd (2 * r) ⟨3 * r - 4, by omega⟩ ∧ (xPair lam (r - 2)).1 = mxf lam (r - 2)) ∨
      (q = Fin.natAdd (2 * r) ⟨3 * r - 3, by omega⟩ ∧ (xPair lam (r - 2)).2 = mxf lam (r - 2))) := by
  have hn1 : 1 ≤ r - 2 := by omega
  have hrn : r = (r - 2) + 2 := by omega
  generalize hn : r - 2 = n at hne hn1 hrn ⊢
  have hle : ∀ j, j ≤ n → mxf lam j ≤ mxf lam n := by
    intro j hj
    have := mx_ge lam j (n - j)
    rw [show j + (n - j) = n by omega] at this
    have : (0 : ℝ) ≤ ((n - j : ℕ) : ℝ) / 2 := by positivity
    linarith
  have hlt : ∀ j, j < n → mxf lam j < mxf lam n := by
    intro j hj
    have := mx_ge lam j (n - j)
    rw [show j + (n - j) = n by omega] at this
    have : (1 : ℝ) ≤ ((n - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - j)
    linarith
  have hab : ∀ j, j ≤ n → (xPair lam j).1 ≤ mxf lam n ∧ (xPair lam j).2 ≤ mxf lam n :=
    fun j hj => ⟨(le_max_left _ _).trans (hle j hj), (le_max_right _ _).trans (hle j hj)⟩
  have hab' : ∀ j, j < n → (xPair lam j).1 < mxf lam n ∧ (xPair lam j).2 < mxf lam n :=
    fun j hj => ⟨lt_of_le_of_lt (le_max_left _ _) (hlt j hj),
      lt_of_le_of_lt (le_max_right _ _) (hlt j hj)⟩
  have hmx0 : 1 ≤ mxf lam 0 := by
    unfold mxf; rw [xp0]; exact le_max_right _ _
  have hmx1 : 3 / 2 ≤ mxf lam n := by
    have h1 := mx_ge lam 0 1
    have h2 := hle 1 hn1
    simp only [Nat.zero_add, Nat.cast_one] at h1
    linarith
  have hn1a : (xPair lam (n + 1)).1 < 1 + mxf lam n := by
    rw [xpa]
    have : min (xPair lam n).1 (xPair lam n).2 < max (xPair lam n).1 (xPair lam n).2 :=
      min_lt_max.2 hne
    unfold mxf; linarith
  have hn1b : (xPair lam (n + 1)).2 < 1 + mxf lam n := by
    rw [xpb]
    have : (0 : ℝ) < 1 / 2 ^ (n + 1) := by positivity
    unfold mxf; linarith
  have hX : ∀ j, j ≤ n + 1 →
      (xPair lam j).1 < 1 + mxf lam n ∧ (xPair lam j).2 < 1 + mxf lam n := by
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · have := hab j (by omega)
      constructor <;> linarith [this.1, this.2]
    · have : j = n + 1 := by omega
      subst this; exact ⟨hn1a, hn1b⟩
  refine Fin.addCases (fun k => ?_) (fun i => ?_) q
  · have hk : k.val / 2 ≤ n + 1 := by have := k.2; omega
    have hv : tropX lam (k.val + 1) < 1 + mxf lam n := by
      rw [tropX_eq]; split_ifs
      · exact (hX _ hk).1
      · exact (hX _ hk).2
    simp only [tropP, Fin.append_left]
    exact ⟨hv.le, fun h => absurd h hv.ne⟩
  · simp only [tropP, Fin.append_right]
    rcases Nat.lt_or_ge (i : ℕ) 2 with hi2 | hi2
    · rcases Nat.lt_or_ge (i : ℕ) 1 with hi1 | hi1
      · have hix : (i : ℕ) + 1 = 1 := by omega
        rw [hix, tropW_0]
        have : (2 : ℝ) < 1 + mxf lam n := by linarith
        exact ⟨this.le, fun h => absurd h this.ne⟩
      · have hix : (i : ℕ) + 1 = 2 := by omega
        rw [hix, tropW_1]
        have : (1 : ℝ) < 1 + mxf lam n := by linarith
        exact ⟨this.le, fun h => absurd h this.ne⟩
    · obtain ⟨j, hj1, hjr, hcase⟩ : ∃ j, 1 ≤ j ∧ j < r ∧
          ((i : ℕ) = 3 * j - 1 ∨ (i : ℕ) = 3 * j ∨ (i : ℕ) = 3 * j + 1) :=
        ⟨((i : ℕ) + 1) / 3, by omega, by omega, by omega⟩
      rcases hcase with hc | hc | hc
      · have hix : (i : ℕ) + 1 = 3 * j := by omega
        rw [hix, tropW_a lam j hj1]
        rcases Nat.lt_or_ge (j - 1) n with h | h
        · have := (hab' (j - 1) h).1
          have h' : 1 + (xPair lam (j - 1)).1 < 1 + mxf lam n := by linarith
          exact ⟨h'.le, fun h2 => absurd h2 h'.ne⟩
        · have hj' : j - 1 = n := by omega
          rw [hj']
          refine ⟨by unfold mxf; linarith [le_max_left (xPair lam n).1 (xPair lam n).2],
            fun h2 => Or.inl ⟨?_, by linarith⟩⟩
          exact congrArg (Fin.natAdd (2 * r)) (Fin.ext (by simp; omega))
      · have hix : (i : ℕ) + 1 = 3 * j + 1 := by omega
        rw [hix, tropW_b lam j hj1]
        rcases Nat.lt_or_ge (j - 1) n with h | h
        · have := (hab' (j - 1) h).2
          have h' : 1 + (xPair lam (j - 1)).2 < 1 + mxf lam n := by linarith
          exact ⟨h'.le, fun h2 => absurd h2 h'.ne⟩
        · have hj' : j - 1 = n := by omega
          rw [hj']
          refine ⟨by unfold mxf; linarith [le_max_right (xPair lam n).1 (xPair lam n).2],
            fun h2 => Or.inr ⟨?_, by linarith⟩⟩
          exact congrArg (Fin.natAdd (2 * r)) (Fin.ext (by simp; omega))
      · have hix : (i : ℕ) + 1 = 3 * j + 2 := by omega
        rw [hix, tropW_c lam j hj1]
        have := (hX j (by omega)).2
        exact ⟨this.le, fun h2 => absurd h2 this.ne⟩

lemma grid_facts (r : ℕ) (hr : 3 ≤ r) (kk : ℕ) (hkk : kk ≤ 2 ^ (r - 2)) (lam : ℝ)
    (hlam : lam = 2 * (kk : ℝ) / 2 ^ (r - 2)) :
    0 ≤ lam ∧ lam ≤ 2 ∧ (xPair lam (r - 2)).1 ≠ (xPair lam (r - 2)).2 ∧
    mxf lam (r - 2) = lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2) ∧
    (kk % 2 = 1 → (xPair lam (r - 2)).1 = mxf lam (r - 2)) ∧
    (kk % 2 = 0 → (xPair lam (r - 2)).2 = mxf lam (r - 2)) := by
  have hpos : (0 : ℝ) < 2 ^ (r - 2) := by positivity
  have hl0 : 0 ≤ lam := by rw [hlam]; positivity
  have hl2 : lam ≤ 2 := by
    rw [hlam, div_le_iff₀ hpos]
    have : (kk : ℝ) ≤ 2 ^ (r - 2) := by exact_mod_cast hkk
    linarith
  have hz := xPair_zigzag (r - 1) kk (by omega) (by rw [show r - 1 - 1 = r - 2 by omega]; exact hkk)
  rw [show r - 1 - 1 = r - 2 by omega, ← hlam] at hz
  have hs := xp_sum lam (r - 2)
  rw [min_eq_left hl2] at hs
  set a := (xPair lam (r - 2)).1 with ha
  set b := (xPair lam (r - 2)).2 with hb
  set p : ℝ := 1 / 2 ^ (r - 2) with hp
  have hp0 : 0 < p := by positivity
  rcases Nat.mod_two_eq_zero_or_one kk with hk | hk
  · have hodd : Odd (kk + 1) := by
      rcases Nat.even_or_odd kk with he | ho
      · exact he.add_one
      · exfalso; have := Nat.odd_iff.1 ho; omega
    rw [hodd.neg_one_pow] at hz
    have hd : a - b = -p := by rw [hz, hp]; ring
    have hbm : b = mxf lam (r - 2) := by
      unfold mxf; rw [← ha, ← hb]; exact (max_eq_right (by linarith)).symm
    refine ⟨hl0, hl2, by intro h; linarith, ?_, fun h => by omega, fun _ => hbm⟩
    rw [← hbm]; linarith
  · have heven : Even (kk + 1) := by
      rcases Nat.even_or_odd kk with he | ho
      · exfalso; have := Nat.even_iff.1 he; omega
      · exact ho.add_one
    rw [heven.neg_one_pow] at hz
    have hd : a - b = p := by rw [hz]
    have ham : a = mxf lam (r - 2) := by
      unfold mxf; rw [← ha, ← hb]; exact (max_eq_left (by linarith)).symm
    refine ⟨hl0, hl2, by intro h; linarith, ?_, fun _ => ham, fun h => by omega⟩
    rw [← ham]; linarith

def peakIdx (r kk : ℕ) (hr : 3 ≤ r) : Fin (2 * r + (3 * r - 1)) :=
  Fin.natAdd (2 * r) ⟨if kk % 2 = 1 then 3 * r - 4 else 3 * r - 3, by split_ifs <;> omega⟩

theorem peak_grid (r : ℕ) (hr : 3 ≤ r) (kk : ℕ) (hkk : kk ≤ 2 ^ (r - 2)) (lam : ℝ)
    (hlam : lam = 2 * (kk : ℝ) / 2 ^ (r - 2)) (q : Fin (2 * r + (3 * r - 1))) :
    tropP r lam q ≤ 1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) ∧
    (tropP r lam q = 1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) → q = peakIdx r kk hr) := by
  obtain ⟨h0, h2, hne, hmx, hodd, heven⟩ := grid_facts r hr kk hkk lam hlam
  have key := peak_aux r hr lam h0 hne q
  have h1 := key.1
  rw [hmx] at h1
  refine ⟨h1, fun h => ?_⟩
  have h' : tropP r lam q = 1 + mxf lam (r - 2) := by rw [hmx]; exact h
  rcases key.2 h' with ⟨hq, ha⟩ | ⟨hq, hb⟩
  · have hk1 : kk % 2 = 1 := by
      by_contra hk
      have hk0 : kk % 2 = 0 := by omega
      exact hne (ha.trans (heven hk0).symm)
    exact hq.trans (by unfold peakIdx; congr 1; apply Fin.ext; simp [hk1])
  · have hk0 : kk % 2 = 0 := by
      by_contra hk
      have hk1 : kk % 2 = 1 := by omega
      exact hne ((hodd hk1).trans hb.symm)
    exact hq.trans (by unfold peakIdx; congr 1; apply Fin.ext; simp [hk0])

theorem peak_attained (r : ℕ) (hr : 3 ≤ r) (kk : ℕ) (hkk : kk ≤ 2 ^ (r - 2)) (lam : ℝ)
    (hlam : lam = 2 * (kk : ℝ) / 2 ^ (r - 2)) :
    tropP r lam (peakIdx r kk hr) = 1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) := by
  obtain ⟨h0, h2, hne, hmx, hodd, heven⟩ := grid_facts r hr kk hkk lam hlam
  have e : tropP r lam (peakIdx r kk hr) =
      tropW lam ((if kk % 2 = 1 then 3 * r - 4 else 3 * r - 3) + 1) := by
    unfold tropP peakIdx; rw [Fin.append_right]
  rw [e]
  by_cases hk : kk % 2 = 1
  · rw [if_pos hk]
    have e1 : 3 * r - 4 + 1 = 3 * (r - 1) := by omega
    rw [e1, tropW_a lam (r - 1) (by omega), show r - 1 - 1 = r - 2 by omega, hodd hk, hmx]
  · rw [if_neg hk]
    have hk0 : kk % 2 = 0 := by omega
    have e1 : 3 * r - 3 + 1 = 3 * (r - 1) + 1 := by omega
    rw [e1, tropW_b lam (r - 1) (by omega), show r - 1 - 1 = r - 2 by omega, heven hk0, hmx]

theorem peak_grid_pd (r : ℕ) (hr : 3 ≤ r) (kk : ℕ) (hkk : kk ≤ 2 ^ (r - 2)) (lam : ℝ)
    (hlam : lam = 2 * (kk : ℝ) / 2 ^ (r - 2))
    (q : Fin ((2 * r + (3 * r - 1)) + (2 * r + (3 * r - 1)))) :
    tropCentralPathLW r lam q ≤ 1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) ∧
    (tropCentralPathLW r lam q = 1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) →
      q = Fin.castAdd _ (peakIdx r kk hr)) := by
  obtain ⟨h0, h2, hne, hmx, hodd, heven⟩ := grid_facts r hr kk hkk lam hlam
  have hp : (0 : ℝ) < 1 / 2 ^ (r - 2) := by positivity
  have hn : (1 : ℝ) ≤ ((r - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 2)
  have hT : lam < 1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) := by linarith
  refine Fin.addCases (fun q1 => ?_) (fun q2 => ?_) q
  · have e : tropCentralPathLW r lam (Fin.castAdd _ q1) = tropP r lam q1 := by
      simp [tropCentralPathLW, tropP]
    rw [e]
    have := peak_grid r hr kk hkk lam hlam q1
    exact ⟨this.1, fun h => congrArg _ (this.2 h)⟩
  · refine Fin.addCases (fun k => ?_) (fun i => ?_) q2
    · have e : tropCentralPathLW r lam (Fin.natAdd _ (Fin.castAdd _ k)) = lam - tropX lam (k.val + 1) := by
        simp only [tropCentralPathLW, Fin.append_left, Fin.append_right, tropS]
      rw [e]
      have := tropX_nonneg lam h0 k.val
      have hlt : lam - tropX lam (k.val + 1) < 1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) := by
        linarith
      exact ⟨hlt.le, fun h => absurd h hlt.ne⟩
    · have e : tropCentralPathLW r lam (Fin.natAdd _ (Fin.natAdd _ i)) = lam - tropW lam (i.val + 1) := by
        simp only [tropCentralPathLW, Fin.append_left, Fin.append_right, tropY]
      rw [e]
      have := tropW_nonneg lam h0 (i.val + 1)
      have hlt : lam - tropW lam (i.val + 1) < 1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) := by
        linarith
      exact ⟨hlt.le, fun h => absurd h hlt.ne⟩

lemma tmax_coe {d : ℕ} (Q : Fin d → ℝ) (i : Fin d) (T : ℝ) (h : ∀ q, Q q ≤ T) (e : Q i = T) :
    tmax (fun q => (Q q : WithBot ℝ)) = (T : WithBot ℝ) := by
  unfold tmax
  apply le_antisymm
  · exact Finset.sup_le fun q _ => WithBot.coe_le_coe.2 (h q)
  · have := Finset.le_sup (f := fun q => (Q q : WithBot ℝ)) (Finset.mem_univ i)
    rw [e] at this; exact this

lemma l23_of_peaks {d : ℕ} (Q1 Q2 Q3 : Fin d → ℝ) (i1 i2 i3 : Fin d) (T1 T2 T3 : ℝ)
    (h1 : ∀ q, Q1 q ≤ T1) (e1 : Q1 i1 = T1)
    (h2 : ∀ q, Q2 q ≤ T2) (e2 : Q2 i2 = T2) (u2 : ∀ q, Q2 q = T2 → q = i2)
    (h3 : ∀ q, Q3 q ≤ T3) (e3 : Q3 i3 = T3) (u3 : ∀ q, Q3 q = T3 → q = i3)
    (t12 : T1 < T2) (t23 : T2 < T3) (hi : i2 ≠ i3) :
    Lemma23Condition (fun q => (Q1 q : WithBot ℝ)) (fun q => (Q2 q : WithBot ℝ))
      (fun q => (Q3 q : WithBot ℝ)) := by
  have m1 := tmax_coe Q1 i1 T1 h1 e1
  have m2 := tmax_coe Q2 i2 T2 h2 e2
  have m3 := tmax_coe Q3 i3 T3 h3 e3
  refine ⟨by rw [m1, m2]; exact WithBot.coe_lt_coe.2 t12,
    by rw [m2, m3]; exact WithBot.coe_lt_coe.2 t23, ?_⟩
  rw [Set.disjoint_left]
  intro q hq2 hq3
  have hq2' : Q2 q = T2 := by
    have : (Q2 q : WithBot ℝ) = tmax (fun q => (Q2 q : WithBot ℝ)) := hq2
    rw [m2] at this; exact WithBot.coe_eq_coe.1 this
  have hq3' : Q3 q = T3 := by
    have : (Q3 q : WithBot ℝ) = tmax (fun q => (Q3 q : WithBot ℝ)) := hq3
    rw [m3] at this; exact WithBot.coe_eq_coe.1 this
  exact hi ((u2 q hq2').symm.trans (u3 q hq3'))

lemma peakIdx_ne (r : ℕ) (hr : 3 ≤ r) (k : ℕ) : peakIdx r (k + 1) hr ≠ peakIdx r (k + 2) hr := by
  intro h
  have := congrArg Fin.val h
  unfold peakIdx at this
  simp only [Fin.val_natAdd] at this
  by_cases hk : (k + 1) % 2 = 1
  · have hk' : ¬ ((k + 2) % 2 = 1) := by omega
    rw [if_pos hk, if_neg hk'] at this
    omega
  · have hk' : (k + 2) % 2 = 1 := by omega
    rw [if_neg hk, if_pos hk'] at this
    omega

theorem cond_primal (r : ℕ) (hr : 3 ≤ r) (k : ℕ) (hk : k + 2 ≤ 2 ^ (r - 2)) (l0 l1 l2 : ℝ)
    (e0 : l0 = 2 * (k : ℝ) / 2 ^ (r - 2)) (e1 : l1 = 2 * ((k + 1 : ℕ) : ℝ) / 2 ^ (r - 2))
    (e2 : l2 = 2 * ((k + 2 : ℕ) : ℝ) / 2 ^ (r - 2)) :
    Lemma23Condition (fun q => (tropP r l0 q : WithBot ℝ)) (fun q => (tropP r l1 q : WithBot ℝ))
      (fun q => (tropP r l2 q : WithBot ℝ)) := by
  have hpos : (0 : ℝ) < 2 ^ (r - 2) := by positivity
  have l01 : l0 < l1 := by
    rw [e0, e1]; push_cast
    exact div_lt_div_of_pos_right (by linarith) hpos
  have l12 : l1 < l2 := by
    rw [e1, e2]; push_cast
    exact div_lt_div_of_pos_right (by linarith) hpos
  refine l23_of_peaks _ _ _ (peakIdx r k hr) (peakIdx r (k + 1) hr) (peakIdx r (k + 2) hr) _ _ _
    (fun q => (peak_grid r hr k (by omega) l0 e0 q).1) (peak_attained r hr k (by omega) l0 e0)
    (fun q => (peak_grid r hr (k + 1) (by omega) l1 e1 q).1) (peak_attained r hr (k + 1) (by omega) l1 e1)
    (fun q => (peak_grid r hr (k + 1) (by omega) l1 e1 q).2)
    (fun q => (peak_grid r hr (k + 2) (by omega) l2 e2 q).1) (peak_attained r hr (k + 2) (by omega) l2 e2)
    (fun q => (peak_grid r hr (k + 2) (by omega) l2 e2 q).2) ?_ ?_ (peakIdx_ne r hr k)
  · linarith
  · linarith

theorem cond_pd (r : ℕ) (hr : 3 ≤ r) (k : ℕ) (hk : k + 2 ≤ 2 ^ (r - 2)) (l0 l1 l2 : ℝ)
    (e0 : l0 = 2 * (k : ℝ) / 2 ^ (r - 2)) (e1 : l1 = 2 * ((k + 1 : ℕ) : ℝ) / 2 ^ (r - 2))
    (e2 : l2 = 2 * ((k + 2 : ℕ) : ℝ) / 2 ^ (r - 2)) :
    Lemma23Condition (fun q => (tropCentralPathLW r l0 q : WithBot ℝ))
      (fun q => (tropCentralPathLW r l1 q : WithBot ℝ))
      (fun q => (tropCentralPathLW r l2 q : WithBot ℝ)) := by
  have hpos : (0 : ℝ) < 2 ^ (r - 2) := by positivity
  have l01 : l0 < l1 := by
    rw [e0, e1]; push_cast
    exact div_lt_div_of_pos_right (by linarith) hpos
  have l12 : l1 < l2 := by
    rw [e1, e2]; push_cast
    exact div_lt_div_of_pos_right (by linarith) hpos
  have att : ∀ (kk : ℕ) (hkk : kk ≤ 2 ^ (r - 2)) (lam : ℝ) (hlam : lam = 2 * (kk : ℝ) / 2 ^ (r - 2)),
      tropCentralPathLW r lam (Fin.castAdd _ (peakIdx r kk hr)) =
        1 + (lam / 2 + ((r - 2 : ℕ) : ℝ) + 1 / 2 ^ (r - 2)) := by
    intro kk hkk lam hlam
    have e : tropCentralPathLW r lam (Fin.castAdd _ (peakIdx r kk hr)) = tropP r lam (peakIdx r kk hr) := by
      simp [tropCentralPathLW, tropP]
    rw [e]; exact peak_attained r hr kk hkk lam hlam
  refine l23_of_peaks _ _ _ (Fin.castAdd _ (peakIdx r k hr)) (Fin.castAdd _ (peakIdx r (k + 1) hr))
    (Fin.castAdd _ (peakIdx r (k + 2) hr)) _ _ _
    (fun q => (peak_grid_pd r hr k (by omega) l0 e0 q).1) (att k (by omega) l0 e0)
    (fun q => (peak_grid_pd r hr (k + 1) (by omega) l1 e1 q).1) (att (k + 1) (by omega) l1 e1)
    (fun q => (peak_grid_pd r hr (k + 1) (by omega) l1 e1 q).2)
    (fun q => (peak_grid_pd r hr (k + 2) (by omega) l2 e2 q).1) (att (k + 2) (by omega) l2 e2)
    (fun q => (peak_grid_pd r hr (k + 2) (by omega) l2 e2 q).2) ?_ ?_
    (fun h => peakIdx_ne r hr k (Fin.castAdd_injective _ _ h))
  · linarith
  · linarith

end LogBarrierIPM.Curvature

open Filter Topology

namespace LogBarrierIPM.Curvature

lemma k2_bnd (t : ℝ) (ht1 : 1 < t) (x X η : ℝ) (hx : 0 < x) (h : |Real.logb t x - X| ≤ η) :
    t ^ (X - η) ≤ x ∧ x ≤ t ^ (X + η) := by
  rw [abs_le] at h
  constructor
  · rw [← Real.le_logb_iff_rpow_le ht1 hx]; linarith [h.1]
  · rw [← Real.logb_le_iff_le_rpow ht1 hx]; linarith [h.2]

lemma k2_pair_bound (t : ℝ) (ht1 : 1 < t) (x y X Y E η : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxb : |Real.logb t x - X| ≤ η) (hyb : |Real.logb t y - Y| ≤ η) (hXE : X ≤ E) (hYE : Y ≤ E) :
    |y - x| ≤ t ^ (E + η) := by
  have h1 := (k2_bnd t ht1 x X η hx hxb).2
  have h2 := (k2_bnd t ht1 y Y η hy hyb).2
  have m1 : t ^ (X + η) ≤ t ^ (E + η) :=
    Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
  have m2 : t ^ (Y + η) ≤ t ^ (E + η) :=
    Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
  rw [abs_le]; constructor <;> linarith

/-- If `y ≥ t^(M-η)` and `x ≤ t^(M-h+η)` with `η = h/8`, then `y - x ≥ t^(M-η)/2`. -/
lemma k2_half (t : ℝ) (ht1 : 1 < t) (h K M x y : ℝ) (hh : 0 < h) (hK2 : 2 ≤ K)
    (hK : K < t ^ (h / 2)) (hy : t ^ (M - h / 8) ≤ y) (hx : x ≤ t ^ (M - h + h / 8)) :
    t ^ (M - h / 8) / 2 ≤ y - x := by
  have ht0 : 0 < t := by linarith
  have hT : 0 < t ^ (h / 2) := by positivity
  have hsplit : t ^ (M - h + h / 8) = t ^ (M - h / 8) * t ^ (h / 8 + h / 8 - h) := by
    rw [← Real.rpow_add ht0]; congr 1; ring
  have hsmall : t ^ (h / 8 + h / 8 - h) ≤ (t ^ (h / 2))⁻¹ := by
    rw [← Real.rpow_neg ht0.le]
    exact Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
  have hinv : (t ^ (h / 2))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hT (by norm_num)]
    linarith
  have hX : 0 < t ^ (M - h / 8) := by positivity
  have : x ≤ t ^ (M - h / 8) * (1 / 2) := by
    calc x ≤ t ^ (M - h + h / 8) := hx
      _ = t ^ (M - h / 8) * t ^ (h / 8 + h / 8 - h) := hsplit
      _ ≤ t ^ (M - h / 8) * (1 / 2) :=
          mul_le_mul_of_nonneg_left (hsmall.trans hinv) hX.le
  linarith

lemma angle_core {d : ℕ} (t : ℝ) (ht1 : 1 < t) (U V W : Fin d → ℝ) (MV MW h : ℝ) (hh : 0 < h)
    (hU : ∀ q, U q ≤ MV - h)
    (hV : ∀ q, V q ≤ MV)
    (hcase : ∀ q, V q ≤ MV - h ∨ (V q = MV ∧ W q ≤ MW - h))
    (hMW : MV ≤ MW - h) (hW : ∀ q, W q ≤ MW)
    (iV iW : Fin d) (hiV : V iV = MV) (hiW : W iW = MW)
    (K s : ℝ) (hs : 0 < s) (hK2 : 2 ≤ K) (hKd : 4 * d / s ≤ K) (hK : K < t ^ (h / 2))
    (u v w : EuclideanSpace ℝ (Fin d))
    (hu : ∀ q, 0 < u q ∧ |Real.logb t (u q) - U q| ≤ h / 8)
    (hv : ∀ q, 0 < v q ∧ |Real.logb t (v q) - V q| ≤ h / 8)
    (hw : ∀ q, 0 < w q ∧ |Real.logb t (w q) - W q| ≤ h / 8) :
    v - u ≠ 0 ∧ w - v ≠ 0 ∧
      inner ℝ (v - u) (w - v) / (‖v - u‖ * ‖w - v‖) < s := by
  have ht0 : 0 < t := by linarith
  set η : ℝ := h / 8 with hη
  have hηpos : 0 < η := by positivity
  -- coordinate products
  have hprod : ∀ q, |(v - u) q * (w - v) q| ≤ t ^ (MV + MW - h + 2 * η) := by
    intro q
    rw [abs_mul]
    have hvu : (v - u) q = v q - u q := rfl
    have hwv : (w - v) q = w q - v q := rfl
    rw [hvu, hwv]
    have hmono : ∀ p p' : ℝ, p ≤ p' → t ^ p ≤ t ^ p' :=
      fun p p' hp => Real.rpow_le_rpow_of_exponent_le ht1.le hp
    rcases hcase q with hc | ⟨hc1, hc2⟩
    · have ha := k2_pair_bound t ht1 (u q) (v q) (U q) (V q) (MV - h) η (hu q).1 (hv q).1
        (hu q).2 (hv q).2 (hU q) hc
      have hb := k2_pair_bound t ht1 (v q) (w q) (V q) (W q) MW η (hv q).1 (hw q).1
        (hv q).2 (hw q).2 (by linarith [hV q]) (hW q)
      calc |v q - u q| * |w q - v q| ≤ t ^ (MV - h + η) * t ^ (MW + η) :=
            mul_le_mul ha hb (abs_nonneg _) (by positivity)
        _ = t ^ (MV + MW - h + 2 * η) := by
            rw [← Real.rpow_add ht0]; congr 1; ring
    · have ha := k2_pair_bound t ht1 (u q) (v q) (U q) (V q) MV η (hu q).1 (hv q).1
        (hu q).2 (hv q).2 (by linarith [hU q]) (hV q)
      have hb := k2_pair_bound t ht1 (v q) (w q) (V q) (W q) (MW - h) η (hv q).1 (hw q).1
        (hv q).2 (hw q).2 (by linarith) hc2
      calc |v q - u q| * |w q - v q| ≤ t ^ (MV + η) * t ^ (MW - h + η) :=
            mul_le_mul ha hb (abs_nonneg _) (by positivity)
        _ = t ^ (MV + MW - h + 2 * η) := by
            rw [← Real.rpow_add ht0]; congr 1; ring
  -- upper bound on the inner product
  have hinner : inner ℝ (v - u) (w - v) ≤ (d : ℝ) * t ^ (MV + MW - h + 2 * η) := by
    have e : inner ℝ (v - u) (w - v) = ∑ q, (v - u) q * (w - v) q := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [e]
    calc ∑ q, (v - u) q * (w - v) q ≤ ∑ q : Fin d, t ^ (MV + MW - h + 2 * η) :=
          Finset.sum_le_sum fun q _ => (le_abs_self _).trans (hprod q)
      _ = (d : ℝ) * t ^ (MV + MW - h + 2 * η) := by simp
  -- lower bounds on the two norms
  have hiVu := k2_bnd t ht1 (u iV) (U iV) η (hu iV).1 (hu iV).2
  have hiVv := k2_bnd t ht1 (v iV) (V iV) η (hv iV).1 (hv iV).2
  have hiWv := k2_bnd t ht1 (v iW) (V iW) η (hv iW).1 (hv iW).2
  have hiWw := k2_bnd t ht1 (w iW) (W iW) η (hw iW).1 (hw iW).2
  have hmono : ∀ p p' : ℝ, p ≤ p' → t ^ p ≤ t ^ p' :=
    fun p p' hp => Real.rpow_le_rpow_of_exponent_le ht1.le hp
  rw [hiV] at hiVv
  rw [hiW] at hiWw
  have hA := k2_half t ht1 h K MV (u iV) (v iV) hh hK2 hK hiVv.1
    (hiVu.2.trans (hmono _ _ (by linarith [hU iV])))
  have hB := k2_half t ht1 h K MW (v iW) (w iW) hh hK2 hK hiWw.1
    (hiWv.2.trans (hmono _ _ (by linarith [hV iW])))
  set X : ℝ := t ^ (MV - η) with hX
  set Y : ℝ := t ^ (MW - η) with hY
  have hXpos : 0 < X := by positivity
  have hYpos : 0 < Y := by positivity
  have na : X / 2 ≤ ‖v - u‖ := by
    refine hA.trans ?_
    calc v iV - u iV ≤ ‖(v - u) iV‖ := by
          have : (v - u) iV = v iV - u iV := rfl
          rw [this]; exact le_trans (le_abs_self _) (by simp)
      _ ≤ ‖v - u‖ := PiLp.norm_apply_le _ _
  have nb : Y / 2 ≤ ‖w - v‖ := by
    refine hB.trans ?_
    calc w iW - v iW ≤ ‖(w - v) iW‖ := by
          have : (w - v) iW = w iW - v iW := rfl
          rw [this]; exact le_trans (le_abs_self _) (by simp)
      _ ≤ ‖w - v‖ := PiLp.norm_apply_le _ _
  have hna : 0 < ‖v - u‖ := lt_of_lt_of_le (by positivity) na
  have hnb : 0 < ‖w - v‖ := lt_of_lt_of_le (by positivity) nb
  refine ⟨fun h0 => by rw [h0] at hna; simp at hna, fun h0 => by rw [h0] at hnb; simp at hnb, ?_⟩
  rw [div_lt_iff₀ (mul_pos hna hnb)]
  have hT : 0 < t ^ (h / 2) := by positivity
  have hP : t ^ (MV + MW - h + 2 * η) = (X * Y) * (t ^ (h / 2))⁻¹ := by
    rw [hX, hY, ← Real.rpow_add ht0, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]
    congr 1; rw [hη]; ring
  have hd4 : 4 * (d : ℝ) < s * t ^ (h / 2) := by
    have : 4 * (d : ℝ) / s < t ^ (h / 2) := lt_of_le_of_lt hKd hK
    rw [div_lt_iff₀ hs] at this
    linarith
  have hdXY : (d : ℝ) * t ^ (MV + MW - h + 2 * η) < s * (X / 2 * (Y / 2)) := by
    rw [hP]
    have hinv : (t ^ (h / 2))⁻¹ * (4 * d) < s := by
      rw [inv_mul_lt_iff₀ hT]; linarith
    have hXY : 0 < X * Y := mul_pos hXpos hYpos
    have : (d : ℝ) * (X * Y * (t ^ (h / 2))⁻¹) = (X * Y) * ((t ^ (h / 2))⁻¹ * d) := by ring
    rw [this]
    have h4 : (X * Y) * ((t ^ (h / 2))⁻¹ * (4 * d)) < (X * Y) * s := mul_lt_mul_of_pos_left hinv hXY
    nlinarith
  have hmul : X / 2 * (Y / 2) ≤ ‖v - u‖ * ‖w - v‖ :=
    mul_le_mul na nb (by positivity) hna.le
  calc inner ℝ (v - u) (w - v) ≤ (d : ℝ) * t ^ (MV + MW - h + 2 * η) := hinner
    _ < s * (X / 2 * (Y / 2)) := hdXY
    _ ≤ s * (‖v - u‖ * ‖w - v‖) := mul_le_mul_of_nonneg_left hmul hs.le


theorem turningAngle_gt_of_logb_close {d : ℕ} (U V W : Fin d → ℝ)
    (hcond : Lemma23Condition (fun q => (U q : WithBot ℝ)) (fun q => (V q : WithBot ℝ))
      (fun q => (W q : WithBot ℝ)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t in atTop, ∀ u v w : EuclideanSpace ℝ (Fin d),
      (∀ q, 0 < u q ∧ |Real.logb t (u q) - U q| ≤ η) →
      (∀ q, 0 < v q ∧ |Real.logb t (v q) - V q| ≤ η) →
      (∀ q, 0 < w q ∧ |Real.logb t (w q) - W q| ≤ η) →
      Real.pi / 2 - δ < turningAngle u v w := by
  obtain ⟨hUV, hVW, hdisj⟩ := hcond
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
    by_contra hne
    have : (Finset.univ : Finset (Fin d)) = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    unfold tmax at hUV
    rw [this] at hUV
    simp at hUV
  obtain ⟨iU, -, hiU⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun q => (U q : WithBot ℝ))
  obtain ⟨iV, -, hiV⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun q => (V q : WithBot ℝ))
  obtain ⟨iW, -, hiW⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun q => (W q : WithBot ℝ))
  have tU : tmax (fun q => (U q : WithBot ℝ)) = (U iU : WithBot ℝ) := hiU
  have tV : tmax (fun q => (V q : WithBot ℝ)) = (V iV : WithBot ℝ) := hiV
  have tW : tmax (fun q => (W q : WithBot ℝ)) = (W iW : WithBot ℝ) := hiW
  rw [tU, tV] at hUV
  rw [tV, tW] at hVW
  have hUV' : U iU < V iV := WithBot.coe_lt_coe.1 hUV
  have hVW' : V iV < W iW := WithBot.coe_lt_coe.1 hVW
  have leU : ∀ q, U q ≤ U iU := fun q => by
    have := Finset.le_sup (f := fun q => (U q : WithBot ℝ)) (Finset.mem_univ q)
    rw [show Finset.univ.sup (fun q => (U q : WithBot ℝ)) = (U iU : WithBot ℝ) from hiU] at this
    exact WithBot.coe_le_coe.1 this
  have leV : ∀ q, V q ≤ V iV := fun q => by
    have := Finset.le_sup (f := fun q => (V q : WithBot ℝ)) (Finset.mem_univ q)
    rw [show Finset.univ.sup (fun q => (V q : WithBot ℝ)) = (V iV : WithBot ℝ) from hiV] at this
    exact WithBot.coe_le_coe.1 this
  have leW : ∀ q, W q ≤ W iW := fun q => by
    have := Finset.le_sup (f := fun q => (W q : WithBot ℝ)) (Finset.mem_univ q)
    rw [show Finset.univ.sup (fun q => (W q : WithBot ℝ)) = (W iW : WithBot ℝ) from hiW] at this
    exact WithBot.coe_le_coe.1 this
  have hWlt : ∀ q, V q = V iV → W q < W iW := by
    intro q hq
    have hmem : q ∈ targmax (fun q => (V q : WithBot ℝ)) := by
      show (V q : WithBot ℝ) = tmax (fun q => (V q : WithBot ℝ))
      rw [tV, hq]
    have hnot := Set.disjoint_left.1 hdisj hmem
    have hne' : W q ≠ W iW := by
      intro h
      apply hnot
      show (W q : WithBot ℝ) = tmax (fun q => (W q : WithBot ℝ))
      rw [tW, h]
    exact lt_of_le_of_ne (leW q) hne'
  set MV := V iV with hMV
  set MW := W iW with hMW
  -- the positive gap function
  let g : Fin d → ℝ := fun q => if V q < MV then MV - V q else MW - W q
  have hg : ∀ q, 0 < g q := by
    intro q
    simp only [g]
    split_ifs with hlt
    · linarith
    · have : V q = MV := le_antisymm (leV q) (not_lt.1 hlt)
      have := hWlt q this
      linarith
  set h0 : ℝ := Finset.univ.inf' hne g with hh0
  have hh0pos : 0 < h0 := by
    rw [hh0, Finset.lt_inf'_iff]; exact fun q _ => hg q
  have hh0le : ∀ q, h0 ≤ g q := fun q => Finset.inf'_le g (Finset.mem_univ q)
  set h : ℝ := min h0 (min (MV - U iU) (MW - MV)) with hhdef
  have hhpos : 0 < h := lt_min hh0pos (lt_min (by linarith) (by linarith))
  have hh1 : h ≤ h0 := min_le_left _ _
  have hh2 : h ≤ MV - U iU := (min_le_right _ _).trans (min_le_left _ _)
  have hh3 : h ≤ MW - MV := (min_le_right _ _).trans (min_le_right _ _)
  have hU : ∀ q, U q ≤ MV - h := fun q => by linarith [leU q]
  have hcase : ∀ q, V q ≤ MV - h ∨ (V q = MV ∧ W q ≤ MW - h) := by
    intro q
    by_cases hlt : V q < MV
    · left
      have := hh0le q
      simp only [g, if_pos hlt] at this
      linarith
    · right
      have hq : V q = MV := le_antisymm (leV q) (not_lt.1 hlt)
      refine ⟨hq, ?_⟩
      have := hh0le q
      simp only [g, if_neg hlt] at this
      linarith
  -- the angle threshold
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hpi := Real.pi_gt_three
  have hspos : 0 < Real.sin δ' :=
    Real.sin_pos_of_pos_of_lt_pi hδ'pos (by linarith)
  set s : ℝ := Real.sin δ' with hs
  set K : ℝ := max 2 (4 * d / s) with hK
  refine ⟨h / 8, by positivity, ?_⟩
  have hev : ∀ᶠ t in atTop, 1 < t ∧ K < t ^ (h / 2) :=
    (eventually_gt_atTop (1 : ℝ)).and
      ((tendsto_rpow_atTop (by positivity : 0 < h / 2)).eventually_gt_atTop K)
  filter_upwards [hev] with t ht u v w hu hv hw
  obtain ⟨ht1, htK⟩ := ht
  obtain ⟨n1, n2, hlt⟩ := angle_core t ht1 U V W MV MW h hhpos hU leV hcase (by linarith) leW
    iV iW rfl rfl K s hspos (le_max_left _ _) (le_max_right _ _) htK u v w hu hv hw
  have huv : ¬ (u = v ∨ v = w) := by
    rintro (h1 | h1)
    · exact n1 (by rw [h1, sub_self])
    · exact n2 (by rw [h1, sub_self])
  unfold turningAngle
  rw [if_neg huv]
  by_contra hcon
  have hle : InnerProductGeometry.angle (v - u) (w - v) ≤ Real.pi / 2 - δ' := by linarith [not_lt.1 hcon]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg (v - u) (w - v))
    (by linarith) hle
  rw [Real.cos_pi_div_two_sub, InnerProductGeometry.cos_angle] at hcos
  linarith

end LogBarrierIPM.Curvature


namespace LogBarrierIPM.Curvature

/-! ## Reduction (our own code, no placeholders) -/

theorem T25.le_totalCurvature {d : ℕ} (σ : ℝ → EuclideanSpace ℝ (Fin d)) (I : Set ℝ) (p : ℕ)
    (μ : ℕ → ℝ) (h : IsInscribedSubdivision I p μ) :
    ((inscribedPolygonCurvature σ p μ : ℝ) : EReal) ≤ totalCurvature σ I := by
  unfold totalCurvature
  exact le_iSup₂_of_le p μ (le_iSup_of_le h le_rfl)

theorem T25.totalCurvature_nonneg {d : ℕ} (σ : ℝ → EuclideanSpace ℝ (Fin d)) :
    (0 : EReal) ≤ totalCurvature σ (Set.Ioi 0) := by
  have h : IsInscribedSubdivision (Set.Ioi (0 : ℝ)) 0 (fun _ => 1) :=
    ⟨fun _ _ => by norm_num, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  have := T25.le_totalCurvature σ _ 0 _ h
  simpa [inscribedPolygonCurvature] using this

theorem T25.bound_of_angles {d : ℕ} (σ : ℝ → EuclideanSpace ℝ (Fin d)) (m : ℕ) (hm : 2 ≤ m)
    (μ : ℕ → ℝ) (hsub : IsInscribedSubdivision (Set.Ioi 0) m μ) (ε : ℝ) (hε : 0 < ε)
    (hang : ∀ k, k < m - 1 →
      Real.pi / 2 - ε / m < turningAngle (σ (μ k)) (σ (μ (k + 1))) (σ (μ (k + 2)))) :
    ((((m : ℝ) - 1) * Real.pi / 2 - ε : ℝ) : EReal) < totalCurvature σ (Set.Ioi 0) := by
  refine lt_of_lt_of_le ?_ (T25.le_totalCurvature σ _ m μ hsub)
  rw [EReal.coe_lt_coe_iff]
  unfold inscribedPolygonCurvature
  have hne : (Finset.range (m - 1)).Nonempty := Finset.nonempty_range_iff.2 (by omega)
  have hlt := Finset.sum_lt_sum_of_nonempty hne (fun k hk => hang k (Finset.mem_range.1 hk))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hm' : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hm'] at hlt
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h1 : ((m : ℝ) - 1) * (ε / m) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hmpos]; nlinarith
  have h2 : ((m : ℝ) - 1) * (Real.pi / 2 - ε / m) =
      ((m : ℝ) - 1) * Real.pi / 2 - ((m : ℝ) - 1) * (ε / m) := by ring
  linarith

theorem T25.primalPoint_apply {n m : ℕ} (z : SlackPoint n m) (q : Fin (n + m)) :
    primalPoint z q = primalDualPoint z (Fin.castAdd (n + m) q) := by
  simp [primalPoint, primalDualPoint]

theorem T25.trop_castAdd (r : ℕ) (lam : ℝ) (q : Fin (2 * r + (3 * r - 1))) :
    tropCentralPathLW r lam (Fin.castAdd (2 * r + (3 * r - 1)) q) = tropP r lam q := by
  simp [tropCentralPathLW, tropP]

end LogBarrierIPM.Curvature

open LogBarrierIPM.Curvature in
theorem solution (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ < t →
      ∀ C : ℝ → SlackPoint (2 * r) (3 * r - 1),
        (∀ μ : ℝ, 0 < μ → IsSlackCentralPathPoint (LogBarrierIPM.Iterations.lwA r t) (LogBarrierIPM.Iterations.lwB r t) (LogBarrierIPM.Iterations.lwC r) μ (C μ)) →
        ((((2 : ℝ) ^ ((r : ℤ) - 2) - 1) * Real.pi / 2 - ε : ℝ) : EReal) <
            totalCurvature (fun μ => primalPoint (C μ)) (Set.Ioi 0) ∧
          ((((2 : ℝ) ^ ((r : ℤ) - 2) - 1) * Real.pi / 2 - ε : ℝ) : EReal) <
            totalCurvature (fun μ => primalDualPoint (C μ)) (Set.Ioi 0) := by
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · -- r ≤ 2: the bound is negative
    refine ⟨0, fun t _ C _ => ?_⟩
    have hz : (2 : ℝ) ^ ((r : ℤ) - 2) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hb : ((2 : ℝ) ^ ((r : ℤ) - 2) - 1) * Real.pi / 2 - ε < 0 := by
      nlinarith [Real.pi_pos]
    have hb' : ((((2 : ℝ) ^ ((r : ℤ) - 2) - 1) * Real.pi / 2 - ε : ℝ) : EReal) < 0 := by
      exact_mod_cast hb
    exact ⟨lt_of_lt_of_le hb' (T25.totalCurvature_nonneg _),
      lt_of_lt_of_le hb' (T25.totalCurvature_nonneg _)⟩
  · -- r ≥ 3
    set m : ℕ := 2 ^ (r - 2) with hm
    have hm2 : 2 ≤ m := by
      have : 2 ^ 1 ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa [hm] using this
    have hmR : (m : ℝ) = 2 ^ (r - 2) := by simp [hm]
    have hzpow : (2 : ℝ) ^ ((r : ℤ) - 2) = (m : ℝ) := by
      rw [show (r : ℤ) - 2 = ((r - 2 : ℕ) : ℤ) by omega, zpow_natCast, hmR]
    have h2r : (2 : ℝ) ^ (r - 1) = 2 * m := by
      rw [hmR, show r - 1 = (r - 2) + 1 by omega, pow_succ]; ring
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    set L : ℕ → ℝ := fun j => 4 * (j : ℝ) / 2 ^ (r - 1) with hLdef
    have hLval : ∀ j, L j = 2 * (j : ℝ) / m := by
      intro j; simp only [hLdef, h2r]; field_simp; ring
    have hL0 : ∀ j, 0 ≤ L j := fun j => by rw [hLval]; positivity
    have hL2 : ∀ j, j ≤ m → L j ≤ 2 := by
      intro j hj; rw [hLval, div_le_iff₀ hmpos]
      have : (j : ℝ) ≤ m := by exact_mod_cast hj
      linarith
    have hLlt : ∀ j, L j < L (j + 1) := by
      intro j; rw [hLval, hLval]; push_cast
      apply div_lt_div_of_pos_right _ hmpos; linarith
    -- tropical vectors
    set Tpd : ℝ → Fin ((2 * r + (3 * r - 1)) + (2 * r + (3 * r - 1))) → ℝ :=
      fun lam => tropCentralPathLW r lam with hTpd
    have hmeq : (m : ℝ) = 2 ^ (r - 2) := hmR
    have hLe : ∀ j : ℕ, L j = 2 * ((j : ℕ) : ℝ) / 2 ^ (r - 2) := by
      intro j; rw [hLval, hmeq]
    have hkm : ∀ k : Fin (m - 1), (k : ℕ) + 2 ≤ 2 ^ (r - 2) := by
      intro k; have h1 := k.2; have h2 : m = 2 ^ (r - 2) := hm; omega
    have hcpd : ∀ k : Fin (m - 1), Lemma23Condition (fun q => (Tpd (L k) q : WithBot ℝ))
        (fun q => (Tpd (L (k + 1)) q : WithBot ℝ)) (fun q => (Tpd (L (k + 2)) q : WithBot ℝ)) := by
      intro k
      exact cond_pd r hr3 k (hkm k) _ _ _ (hLe _) (hLe _) (hLe _)
    have hcp : ∀ k : Fin (m - 1), Lemma23Condition (fun q => (tropP r (L k) q : WithBot ℝ))
        (fun q => (tropP r (L (k + 1)) q : WithBot ℝ)) (fun q => (tropP r (L (k + 2)) q : WithBot ℝ)) := by
      intro k
      exact cond_primal r hr3 k (hkm k) _ _ _ (hLe _) (hLe _) (hLe _)
    have hδ : 0 < ε / m := div_pos hε hmpos
    choose ηpd hηpd hpdev using fun k : Fin (m - 1) =>
      turningAngle_gt_of_logb_close _ _ _ (hcpd k) (ε / m) hδ
    choose ηp hηp hpev using fun k : Fin (m - 1) =>
      turningAngle_gt_of_logb_close _ _ _ (hcp k) (ε / m) hδ
    have hK1 : ∀ (k : Fin (m - 1)) (i : ℕ), i ≤ 2 → ∀ᶠ t in atTop,
        ∀ z : SlackPoint (2 * r) (3 * r - 1),
          IsSlackCentralPathPoint (LogBarrierIPM.Iterations.lwA r t) (LogBarrierIPM.Iterations.lwB r t)
            (LogBarrierIPM.Iterations.lwC r) (t ^ L (k + i)) z →
          ∀ q, 0 < primalDualPoint z q ∧
            |Real.logb t (primalDualPoint z q) - tropCentralPathLW r (L (k + i)) q|
              ≤ min (ηpd k) (ηp k) := by
      intro k i hi
      exact lw_central_path_log_limit r hr (L (k + i)) (hL0 _) (hL2 _ (by have := k.2; omega)) _
        (lt_min (hηpd k) (hηp k))
    have hev := (eventually_gt_atTop (1 : ℝ)).and (eventually_all.2 fun k : Fin (m - 1) =>
      (hpdev k).and ((hpev k).and ((hK1 k 0 (by norm_num)).and ((hK1 k 1 (by norm_num)).and
        (hK1 k 2 (by norm_num))))))
    obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hev
    refine ⟨t₀, fun t ht C hC => ?_⟩
    obtain ⟨ht1, hk⟩ := ht₀ t ht.le
    let μ : ℕ → ℝ := fun j => t ^ L j
    have hsub : IsInscribedSubdivision (Set.Ioi 0) m μ :=
      ⟨fun k _ => Real.rpow_pos_of_pos (by linarith) _,
        fun k _ => Real.rpow_lt_rpow_of_exponent_lt ht1 (hLlt k)⟩
    have hb : ((2 : ℝ) ^ ((r : ℤ) - 2) - 1) * Real.pi / 2 - ε = ((m : ℝ) - 1) * Real.pi / 2 - ε := by
      rw [hzpow]
    rw [hb]
    -- the log estimates at the three vertices of each interior angle
    have hlog : ∀ (k : Fin (m - 1)) (i : ℕ), i ≤ 2 → ∀ q, 0 < primalDualPoint (C (μ (k + i))) q ∧
        |Real.logb t (primalDualPoint (C (μ (k + i))) q) - tropCentralPathLW r (L (k + i)) q|
          ≤ min (ηpd k) (ηp k) := by
      intro k i hi q
      obtain ⟨_, _, h0, h1, h2⟩ := hk k
      have hpos : 0 < μ (k + i) := Real.rpow_pos_of_pos (by linarith) _
      interval_cases i
      · exact h0 _ (hC _ hpos) q
      · exact h1 _ (hC _ hpos) q
      · exact h2 _ (hC _ hpos) q
    constructor
    · refine T25.bound_of_angles _ m hm2 μ hsub ε hε fun k hkm => ?_
      have hpe := (hk ⟨k, hkm⟩).2.1
      have hP : ∀ i : ℕ, i ≤ 2 → ∀ q, 0 < primalPoint (C (μ (k + i))) q ∧
          |Real.logb t (primalPoint (C (μ (k + i))) q) - tropP r (L (k + i)) q| ≤ ηp ⟨k, hkm⟩ := by
        intro i hi q
        have h := hlog ⟨k, hkm⟩ i hi (Fin.castAdd _ q)
        rw [T25.primalPoint_apply]
        rw [T25.trop_castAdd] at h
        exact ⟨h.1, h.2.trans (min_le_right _ _)⟩
      exact hpe _ _ _ (hP 0 (by norm_num)) (hP 1 (by norm_num)) (hP 2 (by norm_num))
    · refine T25.bound_of_angles _ m hm2 μ hsub ε hε fun k hkm => ?_
      have hpe := (hk ⟨k, hkm⟩).1
      have hP : ∀ i : ℕ, i ≤ 2 → ∀ q, 0 < primalDualPoint (C (μ (k + i))) q ∧
          |Real.logb t (primalDualPoint (C (μ (k + i))) q) - Tpd (L (k + i)) q| ≤ ηpd ⟨k, hkm⟩ := by
        intro i hi q
        have h := hlog ⟨k, hkm⟩ i hi q
        exact ⟨h.1, h.2.trans (min_le_left _ _)⟩
      exact hpe _ _ _ (hP 0 (by norm_num)) (hP 1 (by norm_num)) (hP 2 (by norm_num))
