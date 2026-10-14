-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-14T09:45:37.881973+00:00
-- url     : https://prove2.me/submissions/82b79d61-35e9-4af0-bed9-347e0d285cba

import Mathlib
import Definitions.Def_BooneHigman_PMonoid

open OAI.FiniteAlgebraicEnvelopes
open OAI.FiniteAlgebraicEnvelopes.PElem


/-- Lemma 6.4: a nonzero idempotent `q ∈ k[P]` (`k = F2`) that decomposes into two orthogonal
copies of itself, with the splitting elements `s'_0, s'_1, t'_0, t'_1 ∈ qk[P]q`. -/
noncomputable abbrev kP := MonoidAlgebra (ZMod 2) PElem

noncomputable def ofP (p : PElem) : kP := MonoidAlgebra.of (ZMod 2) PElem p

theorem ofP_mul (p p' : PElem) : ofP (p * p') = ofP p * ofP p' :=
  map_mul (MonoidAlgebra.of (ZMod 2) PElem) p p'

theorem ofP_one : ofP (1 : PElem) = (1 : kP) := map_one (MonoidAlgebra.of (ZMod 2) PElem)

theorem ofP_e_mul_e (a b : ℚ) : ofP (e a) * ofP (e b) = ofP (e (max a b)) := by
  rw [← ofP_mul, e_mul_e]

/-- `q = e_0 - e_1`. -/
noncomputable def q : kP := ofP (e 0) - ofP (e 1)

/-- `q_0 = w_0 q w_0⁻¹ = e_0 - e_{1/2}` and `q_1 = w_1 q w_1⁻¹ = e_{1/2} - e_1`. -/
noncomputable def q0 : kP := ofP (e 0) - ofP (e (1 / 2))
noncomputable def q1 : kP := ofP (e (1 / 2)) - ofP (e 1)

theorem q_sq : q * q = q := by
  unfold q
  rw [sub_mul, mul_sub, mul_sub, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e]
  norm_num

theorem q0_sq : q0 * q0 = q0 := by
  unfold q0
  rw [sub_mul, mul_sub, mul_sub, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e]
  norm_num

theorem q1_sq : q1 * q1 = q1 := by
  unfold q1
  rw [sub_mul, mul_sub, mul_sub, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e]
  norm_num

theorem q0_add_q1 : q0 + q1 = q := by
  unfold q0 q1 q; abel

theorem q0_mul_q1 : q0 * q1 = 0 := by
  unfold q0 q1
  rw [sub_mul, mul_sub, mul_sub, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e]
  norm_num

theorem q1_mul_q0 : q1 * q0 = 0 := by
  unfold q0 q1
  rw [sub_mul, mul_sub, mul_sub, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e, ofP_e_mul_e]
  norm_num

/-- `w_0 q w_0⁻¹ = q_0`. -/
theorem w0_q_w0inv : ofP u * q * ofP (fullInv (-1) 0) = q0 := by
  unfold q q0
  rw [mul_sub, sub_mul]
  congr 1
  · show ofP u * ofP (e 0) * ofP (fullInv (-1) 0) = ofP (e 0)
    rw [← ofP_mul, ← ofP_mul]
    show ofP (u * e 0 * fullInv (-1) 0) = ofP (e 0)
    rw [u_mul_e_mul_fullInv]
    try norm_num
  · show ofP u * ofP (e 1) * ofP (fullInv (-1) 0) = ofP (e (1 / 2))
    rw [← ofP_mul, ← ofP_mul]
    show ofP (u * e 1 * fullInv (-1) 0) = ofP (e (1 / 2))
    rw [u_mul_e_mul_fullInv]
    try norm_num

/-- `w_1 q w_1⁻¹ = q_1`. -/
theorem w1_q_w1inv : ofP v * q * ofP (fullInv (-1) (1 / 2)) = q1 := by
  unfold q q1
  rw [mul_sub, sub_mul]
  congr 1
  · show ofP v * ofP (e 0) * ofP (fullInv (-1) (1 / 2)) = ofP (e (1 / 2))
    rw [← ofP_mul, ← ofP_mul]
    show ofP (v * e 0 * fullInv (-1) (1 / 2)) = ofP (e (1 / 2))
    rw [v_mul_e_mul_fullInv]
    try norm_num
  · show ofP v * ofP (e 1) * ofP (fullInv (-1) (1 / 2)) = ofP (e 1)
    rw [← ofP_mul, ← ofP_mul]
    show ofP (v * e 1 * fullInv (-1) (1 / 2)) = ofP (e 1)
    rw [v_mul_e_mul_fullInv]
    try norm_num

theorem ofP_w0_mul_w0inv : ofP u * ofP (fullInv (-1) 0) = 1 := by
  rw [← ofP_mul]; unfold u; rw [mul_fullInv, ofP_one]

theorem ofP_w0inv_mul_w0 : ofP (fullInv (-1) 0) * ofP u = 1 := by
  rw [← ofP_mul]; unfold u; rw [fullInv_mul, ofP_one]

theorem ofP_w1_mul_w1inv : ofP v * ofP (fullInv (-1) (1 / 2)) = 1 := by
  rw [← ofP_mul]; unfold v; rw [mul_fullInv, ofP_one]

theorem ofP_w1inv_mul_w1 : ofP (fullInv (-1) (1 / 2)) * ofP v = 1 := by
  rw [← ofP_mul]; unfold v; rw [fullInv_mul, ofP_one]

/-- `s'_0 = w_0 q`, `t'_0 = q w_0⁻¹`, `s'_1 = w_1 q`, `t'_1 = q w_1⁻¹`. -/
noncomputable def s'0 : kP := ofP u * q
noncomputable def t'0 : kP := q * ofP (fullInv (-1) 0)
noncomputable def s'1 : kP := ofP v * q
noncomputable def t'1 : kP := q * ofP (fullInv (-1) (1 / 2))

/-- `s'_0 = q_0 w_0`, derived from `w_0 q w_0⁻¹ = q_0` by right-multiplying by `w_0`. -/
theorem s'0_eq' : s'0 = q0 * ofP u := by
  have := w0_q_w0inv
  have h : ofP u * q * ofP (fullInv (-1) 0) * ofP u = q0 * ofP u := by rw [this]
  rwa [_root_.mul_assoc, ofP_w0inv_mul_w0, _root_.mul_one] at h

theorem t'0_eq' : t'0 = ofP (fullInv (-1) 0) * q0 := by
  have := w0_q_w0inv
  have h : ofP (fullInv (-1) 0) * (ofP u * q * ofP (fullInv (-1) 0)) =
      ofP (fullInv (-1) 0) * q0 := by rw [this]
  rwa [← _root_.mul_assoc, ← _root_.mul_assoc, ofP_w0inv_mul_w0, _root_.one_mul] at h

theorem s'1_eq' : s'1 = q1 * ofP v := by
  have := w1_q_w1inv
  have h : ofP v * q * ofP (fullInv (-1) (1 / 2)) * ofP v = q1 * ofP v := by rw [this]
  rwa [_root_.mul_assoc, ofP_w1inv_mul_w1, _root_.mul_one] at h

theorem t'1_eq' : t'1 = ofP (fullInv (-1) (1 / 2)) * q1 := by
  have := w1_q_w1inv
  have h : ofP (fullInv (-1) (1 / 2)) * (ofP v * q * ofP (fullInv (-1) (1 / 2))) =
      ofP (fullInv (-1) (1 / 2)) * q1 := by rw [this]
  rwa [← _root_.mul_assoc, ← _root_.mul_assoc, ofP_w1inv_mul_w1, _root_.one_mul] at h

theorem t'0_s'0 : t'0 * s'0 = q := by
  unfold t'0 s'0
  rw [_root_.mul_assoc, ← _root_.mul_assoc (ofP (fullInv (-1) 0)), ofP_w0inv_mul_w0, _root_.one_mul, q_sq]

theorem t'1_s'1 : t'1 * s'1 = q := by
  unfold t'1 s'1
  rw [_root_.mul_assoc, ← _root_.mul_assoc (ofP (fullInv (-1) (1 / 2))), ofP_w1inv_mul_w1, _root_.one_mul, q_sq]

theorem t'0_s'1 : t'0 * s'1 = 0 := by
  rw [t'0_eq', s'1_eq', _root_.mul_assoc, ← _root_.mul_assoc q0, q0_mul_q1]
  simp

theorem t'1_s'0 : t'1 * s'0 = 0 := by
  rw [t'1_eq', s'0_eq', _root_.mul_assoc, ← _root_.mul_assoc q1, q1_mul_q0]
  simp

theorem s'0_t'0_add_s'1_t'1 : s'0 * t'0 + s'1 * t'1 = q := by
  have h0 : s'0 * t'0 = q0 := by
    unfold s'0 t'0
    have step : ofP u * q * (q * ofP (fullInv (-1) 0)) =
        ofP u * (q * q) * ofP (fullInv (-1) 0) := by simp only [_root_.mul_assoc]
    rw [step, q_sq]; exact w0_q_w0inv
  have h1 : s'1 * t'1 = q1 := by
    unfold s'1 t'1
    have step : ofP v * q * (q * ofP (fullInv (-1) (1 / 2))) =
        ofP v * (q * q) * ofP (fullInv (-1) (1 / 2)) := by simp only [_root_.mul_assoc]
    rw [step, q_sq]; exact w1_q_w1inv
  rw [h0, h1, q0_add_q1]

theorem q_mul_q0 : q * q0 = q0 := by
  rw [← q0_add_q1, _root_.add_mul, q0_sq, q1_mul_q0, add_zero]

theorem q0_mul_q : q0 * q = q0 := by
  rw [← q0_add_q1, _root_.mul_add, q0_sq, q0_mul_q1, add_zero]

theorem q_mul_q1 : q * q1 = q1 := by
  rw [← q0_add_q1, _root_.add_mul, q0_mul_q1, q1_sq, zero_add]

theorem q1_mul_q : q1 * q = q1 := by
  rw [← q0_add_q1, _root_.mul_add, q1_mul_q0, q1_sq, zero_add]

theorem q_mul_s'0 : q * s'0 = s'0 := by
  rw [s'0_eq', ← _root_.mul_assoc, q_mul_q0]

theorem s'0_mul_q : s'0 * q = s'0 := by
  unfold s'0; rw [_root_.mul_assoc, q_sq]

theorem q_mul_s'1 : q * s'1 = s'1 := by
  rw [s'1_eq', ← _root_.mul_assoc, q_mul_q1]

theorem s'1_mul_q : s'1 * q = s'1 := by
  unfold s'1; rw [_root_.mul_assoc, q_sq]

theorem q_mul_t'0 : q * t'0 = t'0 := by
  unfold t'0; rw [← _root_.mul_assoc, q_sq]

theorem t'0_mul_q : t'0 * q = t'0 := by
  rw [t'0_eq', _root_.mul_assoc, q0_mul_q]

theorem q_mul_t'1 : q * t'1 = t'1 := by
  unfold t'1; rw [← _root_.mul_assoc, q_sq]

theorem t'1_mul_q : t'1 * q = t'1 := by
  rw [t'1_eq', _root_.mul_assoc, q1_mul_q]

theorem s'0_mem : q * s'0 * q = s'0 := by rw [q_mul_s'0, s'0_mul_q]
theorem s'1_mem : q * s'1 * q = s'1 := by rw [q_mul_s'1, s'1_mul_q]
theorem t'0_mem : q * t'0 * q = t'0 := by rw [q_mul_t'0, t'0_mul_q]
theorem t'1_mem : q * t'1 * q = t'1 := by rw [q_mul_t'1, t'1_mul_q]

theorem ofP_eq_single (p : PElem) : ofP p = MonoidAlgebra.single p 1 := rfl

theorem ofP_coeff (p p' : PElem) [Decidable (p = p')] :
    (ofP p).coeff p' = if p = p' then 1 else 0 := by
  rw [ofP_eq_single, MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem e_ne (a b : ℚ) (h : a ≠ b) : e a ≠ e b := by
  intro heq
  exact h (by simpa [e] using congrArg PElem.r heq)

theorem one_coeff (p : PElem) [Decidable ((1 : PElem) = p)] :
    (1 : kP).coeff p = if (1 : PElem) = p then 1 else 0 := by
  rw [← ofP_one]; exact ofP_coeff 1 p

theorem q_ne_zero : q ≠ 0 := by
  intro h
  unfold q at h
  rw [sub_eq_zero] at h
  have hcoeff : (ofP (e 0)).coeff (e 0) = (ofP (e 1)).coeff (e 0) := by rw [h]
  rw [ofP_coeff, ofP_coeff, if_pos rfl, if_neg (e_ne (1:ℚ) 0 (by norm_num))] at hcoeff
  exact absurd hcoeff (by decide)

theorem q_ne_one : q ≠ 1 := by
  intro h
  unfold q at h
  have hcoeff : (ofP (e 0) - ofP (e 1)).coeff (e 0) = (1 : kP).coeff (e 0) := by rw [h]
  rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, ofP_coeff, ofP_coeff, if_pos rfl,
    if_neg (e_ne (1:ℚ) 0 (by norm_num)), one_coeff, if_neg] at hcoeff
  · simp at hcoeff
  · intro heq
    have hr := congrArg PElem.r heq
    simp [e, PElem.one_def] at hr

/-- **Lemma 6.4**. There is a nonzero idempotent `q ∈ k[P]` and elements
`s'_0, s'_1, t'_0, t'_1 ∈ qk[P]q` such that `t'_i s'_j = δ_ij q` and
`s'_0 t'_0 + s'_1 t'_1 = q`. -/
theorem solution :
    ∃ q : kP, q * q = q ∧ q ≠ 0 ∧ q ≠ 1 ∧
      ∃ s0 s1 t0 t1 : kP, q * s0 * q = s0 ∧ q * s1 * q = s1 ∧
        q * t0 * q = t0 ∧ q * t1 * q = t1 ∧
        t0 * s0 = q ∧ t1 * s1 = q ∧ t0 * s1 = 0 ∧ t1 * s0 = 0 ∧
        s0 * t0 + s1 * t1 = q :=
  ⟨q, q_sq, q_ne_zero, q_ne_one, s'0, s'1, t'0, t'1, s'0_mem, s'1_mem, t'0_mem, t'1_mem,
    t'0_s'0, t'1_s'1, t'0_s'1, t'1_s'0, s'0_t'0_add_s'1_t'1⟩
