-- Prove2me | solution 1 for Grunbaum2003.sturm_tarski_and_signed_remainder_cauchy_index
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:16:03.946849+00:00
-- url     : https://prove2.me/submissions/8e0c3510-879e-4a2e-9ca4-879211f0dd75

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003.FormulaCompiler.Parametric

noncomputable def realSize (p : Polynomial ℝ) : ℕ := by
  classical
  exact if p = 0 then 0 else p.natDegree + 1


theorem realSize_le_iff_degree_lt (p : Polynomial ℝ) (n : ℕ) :
    realSize p ≤ n ↔ p.degree < n := by
  classical
  by_cases hp : p = 0
  · simp [realSize, hp]
  · simp only [realSize, if_neg hp, Polynomial.degree_eq_natDegree hp,
      Nat.cast_lt, Nat.add_one_le_iff]

theorem realSize_eq_degree_succ (p : Polynomial ℝ) : realSize p = p.degree.succ := by
  classical
  by_cases hp : p = 0 <;>
    simp [realSize, hp, Polynomial.withBotSucc_degree_eq_natDegree_add_one]

theorem realSize_eq_zero_iff (p : Polynomial ℝ) : realSize p = 0 ↔ p = 0 := by
  classical
  simp [realSize]

theorem realSize_lt_of_degree_lt (p q : Polynomial ℝ) (h : p.degree < q.degree) :
    realSize p < realSize q := by
  simpa only [realSize_eq_degree_succ] using WithBot.succ_lt_succ h

noncomputable def realRemainderStep (r q : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C q.leadingCoeff * r -
    (Polynomial.C r.leadingCoeff * Polynomial.X ^ (r.natDegree - q.natDegree)) * q

theorem degree_realRemainderStep_lt (r q : Polynomial ℝ)
    (hr : r ≠ 0) (hq : q ≠ 0) (hqr : q.natDegree ≤ r.natDegree) :
    (realRemainderStep r q).degree < r.degree := by
  have hq' := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hr' := Polynomial.leadingCoeff_ne_zero.mpr hr
  have hdeg : (Polynomial.C q.leadingCoeff * r).degree = r.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hq', zero_add]
  rw [realRemainderStep, ← hdeg]
  apply Polynomial.degree_sub_lt_left
  case hd =>
    rw [hdeg, Polynomial.degree_mul, Polynomial.degree_C_mul_X_pow _ hr',
      Polynomial.degree_eq_natDegree hr, Polynomial.degree_eq_natDegree hq,
      ← Nat.cast_add, Nat.sub_add_cancel hqr]
  case hp0 => exact mul_ne_zero (Polynomial.C_ne_zero.mpr hq') hr
  case hlc => simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_X, one_pow, one_mul, mul_comm]

noncomputable def realReductionMonomial (r q : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C r.leadingCoeff * Polynomial.X ^ (realSize r - realSize q)

noncomputable def realPseudoLoop (q : Polynomial ℝ) :
    ℕ → ℕ → Polynomial ℝ → Polynomial ℝ → ℕ × Polynomial ℝ × Polynomial ℝ
  | 0, c, a, r => (c, a, r)
  | n + 1, c, a, r =>
      if realSize r < realSize q then (c, a, r) else
        let m := realReductionMonomial r q
        realPseudoLoop q n (c + 1) (Polynomial.C q.leadingCoeff * a + m)
          (Polynomial.C q.leadingCoeff * r - m * q)

theorem real_reduction_preserves_identity (p q a r m : Polynomial ℝ) (c : ℕ)
    (h : Polynomial.C (q.leadingCoeff ^ c) * p = a * q + r) :
    Polynomial.C (q.leadingCoeff ^ (c + 1)) * p =
      (Polynomial.C q.leadingCoeff * a + m) * q +
        (Polynomial.C q.leadingCoeff * r - m * q) := by
  have h' := congrArg (fun f : Polynomial ℝ => Polynomial.C q.leadingCoeff * f) h
  simp only [pow_succ, map_mul]
  convert h' using 1 <;> ring

theorem realPseudoLoop_identity (p q : Polynomial ℝ) (fuel c : ℕ)
    (a r : Polynomial ℝ)
    (h : Polynomial.C (q.leadingCoeff ^ c) * p = a * q + r) :
    let out := realPseudoLoop q fuel c a r
    Polynomial.C (q.leadingCoeff ^ out.1) * p = out.2.1 * q + out.2.2 := by
  induction fuel generalizing c a r with
  | zero => exact h
  | succ n ih =>
      simp only [realPseudoLoop]
      split_ifs with hs
      · exact h
      · exact ih (c + 1) _ _
          (real_reduction_preserves_identity p q a r (realReductionMonomial r q) c h)

theorem realReduction_size_lt (r q : Polynomial ℝ) (hq : q ≠ 0)
    (hqr : realSize q ≤ realSize r) :
    realSize (Polynomial.C q.leadingCoeff * r - realReductionMonomial r q * q) <
      realSize r := by
  have hr : r ≠ 0 := by
    intro hz
    have hs := (realSize_eq_zero_iff r).mpr hz
    have hq' := (realSize_eq_zero_iff q).not.mpr hq
    omega
  have hdeg : q.natDegree ≤ r.natDegree := by
    simpa only [realSize, if_neg hq, if_neg hr, Nat.add_le_add_iff_right] using hqr
  apply realSize_lt_of_degree_lt
  simpa only [realReductionMonomial, realSize, if_neg hr, if_neg hq,
    Nat.add_sub_add_right, realRemainderStep] using
      degree_realRemainderStep_lt r q hr hq hdeg

theorem realPseudoLoop_remainder_size_lt (q : Polynomial ℝ) (fuel c : ℕ)
    (a r : Polynomial ℝ) (hq : q ≠ 0) (hf : realSize r ≤ fuel) :
    realSize (realPseudoLoop q fuel c a r).2.2 < realSize q := by
  induction fuel generalizing c a r with
  | zero =>
      change realSize r < realSize q
      have hq' := (realSize_eq_zero_iff q).not.mpr hq
      omega
  | succ n ih =>
      simp only [realPseudoLoop]
      split_ifs with hs
      · exact hs
      · apply ih
        have hd := realReduction_size_lt r q hq (Nat.le_of_not_gt hs)
        omega


noncomputable def realPseudoDiv (p q : Polynomial ℝ) (fuel : ℕ) :
    ℕ × Polynomial ℝ × Polynomial ℝ :=
  if realSize q = 0 then (0, 0, p) else realPseudoLoop q fuel 0 0 p

theorem realPseudoDiv_spec (p q : Polynomial ℝ) (fuel : ℕ)
    (hf : realSize p ≤ fuel) :
    let out := realPseudoDiv p q fuel
    Polynomial.C (q.leadingCoeff ^ out.1) * p = out.2.1 * q + out.2.2 ∧
      (q = 0 ∨ out.2.2.degree < q.degree) := by
  by_cases hq : q = 0
  · simp [realPseudoDiv, realSize, hq]
  · have hs := (realSize_eq_zero_iff q).not.mpr hq
    rw [realPseudoDiv, if_neg hs]
    refine ⟨realPseudoLoop_identity p q fuel 0 0 p (by simp), Or.inr ?_⟩
    apply WithBot.succ_strictMono.lt_iff_lt.mp
    simpa only [realSize_eq_degree_succ] using
      realPseudoLoop_remainder_size_lt q fuel 0 0 p hq hf

/-- Once the remainder size is strictly below the divisor size, `realPseudoLoop`
terminates immediately regardless of remaining fuel. -/
theorem realPseudoLoop_of_lt (q : Polynomial ℝ) (fuel c : ℕ) (a r : Polynomial ℝ)
    (h : realSize r < realSize q) :
    realPseudoLoop q fuel c a r = (c, a, r) := by
  cases fuel with
  | zero => rfl
  | succ n => simp only [realPseudoLoop, if_pos h]

/-- For any nonzero divisor `q`, `realPseudoLoop` stabilizes once `fuel ≥ realSize r`. -/
theorem realPseudoLoop_eq_of_size_le (q : Polynomial ℝ) (fuel c : ℕ)
    (a r : Polynomial ℝ) (hq : q ≠ 0) (hf : realSize r ≤ fuel) :
    realPseudoLoop q fuel c a r = realPseudoLoop q (realSize r) c a r := by
  induction fuel using Nat.strongRecOn generalizing c a r with
  | ind fuel ih =>
    cases fuel with
    | zero =>
      have hr0 : realSize r = 0 := Nat.eq_zero_of_le_zero hf
      rw [hr0]
    | succ n =>
      by_cases hs : realSize r < realSize q
      · rw [realPseudoLoop_of_lt q (n + 1) c a r hs,
            realPseudoLoop_of_lt q (realSize r) c a r hs]
      · have hqr : realSize q ≤ realSize r := Nat.le_of_not_gt hs
        have hq_pos : 0 < realSize q :=
          Nat.pos_of_ne_zero ((realSize_eq_zero_iff q).not.mpr hq)
        obtain ⟨m, hm⟩ : ∃ m, realSize r = m + 1 :=
          Nat.exists_eq_succ_of_ne_zero (by omega)
        let a' := Polynomial.C q.leadingCoeff * a + realReductionMonomial r q
        let r' := Polynomial.C q.leadingCoeff * r - realReductionMonomial r q * q
        have hlt : realSize r' < realSize r := realReduction_size_lt r q hq hqr
        have h1 : realPseudoLoop q (n + 1) c a r = realPseudoLoop q n (c + 1) a' r' := by
          simp only [realPseudoLoop, if_neg hs, a', r']
        have h2 : realPseudoLoop q (realSize r) c a r =
            realPseudoLoop q m (c + 1) a' r' := by
          rw [hm]
          simp only [realPseudoLoop, if_neg hs, a', r']
        have hle_n : realSize r' ≤ n := by omega
        have hle_m : realSize r' ≤ m := by omega
        have ihn := ih n (Nat.lt_succ_self n) (c + 1) a' r' hle_n
        have ihm := ih m (by omega) (c + 1) a' r' hle_m
        rw [h1, h2, ihn, ihm]

/-- Canonical fuel-independent pseudo-division over `Polynomial ℝ`. -/
noncomputable def canonicalPseudoDiv (p q : Polynomial ℝ) :
    ℕ × Polynomial ℝ × Polynomial ℝ :=
  realPseudoDiv p q (realSize p)

/-- Any fuel bound at least `realSize p` produces `canonicalPseudoDiv p q`. -/
theorem realPseudoDiv_eq_canonical (p q : Polynomial ℝ) (fuel : ℕ)
    (hf : realSize p ≤ fuel) :
    realPseudoDiv p q fuel = canonicalPseudoDiv p q := by
  by_cases hq : q = 0
  · simp [canonicalPseudoDiv, realPseudoDiv, realSize, hq]
  · have hs := (realSize_eq_zero_iff q).not.mpr hq
    simp only [canonicalPseudoDiv, realPseudoDiv, if_neg hs]
    exact realPseudoLoop_eq_of_size_le q fuel 0 0 p hq hf

theorem canonicalPseudoDiv_spec (p q : Polynomial ℝ) :
    let out := canonicalPseudoDiv p q
    Polynomial.C (q.leadingCoeff ^ out.1) * p = out.2.1 * q + out.2.2 ∧
      (q = 0 ∨ out.2.2.degree < q.degree) :=
  realPseudoDiv_spec p q (realSize p) (le_refl _)

theorem canonicalPseudoDiv_size_lt (p q : Polynomial ℝ) (hq : q ≠ 0) :
    realSize (canonicalPseudoDiv p q).2.2 < realSize q := by
  rcases canonicalPseudoDiv_spec p q with ⟨_, h0 | hdeg⟩
  · exact False.elim (hq h0)
  · exact realSize_lt_of_degree_lt _ _ hdeg

/-- Modified signed remainder `-lc(q)^c * r`, which scales the negative ordinary
remainder by the positive square `(lc(q)^c)^2` when `q ≠ 0`. -/
noncomputable def realNextMod (p q : Polynomial ℝ) : Polynomial ℝ :=
  -(Polynomial.C (q.leadingCoeff ^ (canonicalPseudoDiv p q).1) * (canonicalPseudoDiv p q).2.2)

theorem realNextMod_eq_of_fuel (p q : Polynomial ℝ) (fuel : ℕ)
    (hf : realSize p ≤ fuel) :
    -(Polynomial.C (q.leadingCoeff ^ (realPseudoDiv p q fuel).1) *
      (realPseudoDiv p q fuel).2.2) = realNextMod p q := by
  rw [realPseudoDiv_eq_canonical p q fuel hf]
  rfl

/-- Positive-square scaling factor `(lc(q)^c)^2` for `realNextMod p q`. -/
noncomputable def realNextModScale (p q : Polynomial ℝ) : ℝ :=
  (q.leadingCoeff ^ (canonicalPseudoDiv p q).1) ^ 2

/-- Adjusted quotient `lc(q)^c * a` in the three-term Sturm identity. -/
noncomputable def realNextModQuot (p q : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (q.leadingCoeff ^ (canonicalPseudoDiv p q).1) * (canonicalPseudoDiv p q).2.1

theorem realNextModScale_pos (p q : Polynomial ℝ) (hq : q ≠ 0) :
    0 < realNextModScale p q := by
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  exact sq_pos_of_ne_zero (pow_ne_zero _ hlc)

/-- Three-term signed-remainder identity:
`C((lc(q)^c)^2) * p = (C(lc(q)^c) * a) * q - realNextMod p q`. -/
theorem realNextMod_sturm_identity (p q : Polynomial ℝ) :
    Polynomial.C (realNextModScale p q) * p =
      realNextModQuot p q * q - realNextMod p q := by
  have hid := (canonicalPseudoDiv_spec p q).1
  unfold realNextModScale realNextModQuot realNextMod
  rw [sq, map_mul, mul_assoc, hid]
  ring

theorem realNextMod_eq_zero_iff (p q : Polynomial ℝ) (hq : q ≠ 0) :
    realNextMod p q = 0 ↔ (canonicalPseudoDiv p q).2.2 = 0 := by
  have hlc : q.leadingCoeff ^ (canonicalPseudoDiv p q).1 ≠ 0 :=
    pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hC : Polynomial.C (q.leadingCoeff ^ (canonicalPseudoDiv p q).1) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hlc
  unfold realNextMod
  simp only [neg_eq_zero, mul_eq_zero, hC, false_or]

theorem degree_realNextMod_lt (p q : Polynomial ℝ) (hq : q ≠ 0) :
    (realNextMod p q).degree < q.degree := by
  have hlc : q.leadingCoeff ^ (canonicalPseudoDiv p q).1 ≠ 0 :=
    pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hq)
  unfold realNextMod
  rw [Polynomial.degree_neg, Polynomial.degree_mul, Polynomial.degree_C hlc, zero_add]
  rcases (canonicalPseudoDiv_spec p q).2 with h0 | hdeg
  · exact False.elim (hq h0)
  · exact hdeg

theorem realSize_realNextMod_lt (p q : Polynomial ℝ) (hq : q ≠ 0) :
    realSize (realNextMod p q) < realSize q :=
  realSize_lt_of_degree_lt _ _ (degree_realNextMod_lt p q hq)

/-- At any root `x` of `q`, `realNextMod p q` evaluates to `-scale * p.eval x`. -/
theorem eval_realNextMod_of_eval_eq_zero (p q : Polynomial ℝ) (x : ℝ)
    (hx : q.eval x = 0) :
    (realNextMod p q).eval x = -realNextModScale p q * p.eval x := by
  have h := congrArg (Polynomial.eval x) (realNextMod_sturm_identity p q)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, hx,
    mul_zero, zero_sub] at h
  linarith

/-- At a root `x` of a nonzero `q` where `p.eval x ≠ 0`, `p` and `realNextMod p q`
have strictly opposite signs. -/
theorem eval_mul_realNextMod_neg (p q : Polynomial ℝ) (x : ℝ)
    (hq : q ≠ 0) (hx : q.eval x = 0) (hp : p.eval x ≠ 0) :
    p.eval x * (realNextMod p q).eval x < 0 := by
  rw [eval_realNextMod_of_eval_eq_zero p q x hx]
  have hpos : 0 < realNextModScale p q := realNextModScale_pos p q hq
  have hp2 : 0 < p.eval x ^ 2 := sq_pos_of_ne_zero hp
  have hprod : 0 < realNextModScale p q * p.eval x ^ 2 := mul_pos hpos hp2
  linarith [show p.eval x * (-realNextModScale p q * p.eval x) =
    -(realNextModScale p q * p.eval x ^ 2) by ring]

/-- Common real roots of `p` and `q` are preserved by `(q, realNextMod p q)`. -/
theorem eval_eq_zero_and_realNextMod_iff (p q : Polynomial ℝ) (x : ℝ) (hq : q ≠ 0) :
    (p.eval x = 0 ∧ q.eval x = 0) ↔
      (q.eval x = 0 ∧ (realNextMod p q).eval x = 0) := by
  have hscale : realNextModScale p q ≠ 0 := ne_of_gt (realNextModScale_pos p q hq)
  constructor
  · rintro ⟨hp, hqx⟩
    refine ⟨hqx, ?_⟩
    rw [eval_realNextMod_of_eval_eq_zero p q x hqx, hp, mul_zero]
  · rintro ⟨hqx, hm⟩
    rw [eval_realNextMod_of_eval_eq_zero p q x hqx, neg_mul, neg_eq_zero,
      mul_eq_zero] at hm
    exact ⟨hm.resolve_left hscale, hqx⟩

/-- Common polynomial divisors of `p` and `q` are preserved by `(q, realNextMod p q)`. -/
theorem dvd_and_dvd_realNextMod_iff (d p q : Polynomial ℝ) (hq : q ≠ 0) :
    (d ∣ p ∧ d ∣ q) ↔ (d ∣ q ∧ d ∣ realNextMod p q) := by
  have hscale : realNextModScale p q ≠ 0 := ne_of_gt (realNextModScale_pos p q hq)
  have hid := realNextMod_sturm_identity p q
  constructor
  · rintro ⟨hdp, hdq⟩
    refine ⟨hdq, ?_⟩
    have h1 : d ∣ realNextModQuot p q * q := dvd_mul_of_dvd_right hdq _
    have h2 : d ∣ Polynomial.C (realNextModScale p q) * p := dvd_mul_of_dvd_right hdp _
    have hsub : realNextMod p q =
        realNextModQuot p q * q - Polynomial.C (realNextModScale p q) * p := by
      rw [hid]
      ring
    rw [hsub]
    exact dvd_sub h1 h2
  · rintro ⟨hdq, hdm⟩
    refine ⟨?_, hdq⟩
    have h1 : d ∣ realNextModQuot p q * q := dvd_mul_of_dvd_right hdq _
    have h2 : d ∣ Polynomial.C (realNextModScale p q) * p := by
      rw [hid]
      exact dvd_sub h1 hdm
    rcases h2 with ⟨k, hk⟩
    refine ⟨Polynomial.C (realNextModScale p q)⁻¹ * k, ?_⟩
    have hinv : Polynomial.C (realNextModScale p q)⁻¹ *
        Polynomial.C (realNextModScale p q) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hscale, map_one]
    calc
      p = 1 * p := (one_mul p).symm
      _ = (Polynomial.C (realNextModScale p q)⁻¹ *
            Polynomial.C (realNextModScale p q)) * p := by rw [hinv]
      _ = Polynomial.C (realNextModScale p q)⁻¹ *
            (Polynomial.C (realNextModScale p q) * p) := by ring
      _ = Polynomial.C (realNextModScale p q)⁻¹ * (d * k) := by rw [hk]
      _ = d * (Polynomial.C (realNextModScale p q)⁻¹ * k) := by ring

/-- Bounded signed-remainder sequence `mods_aux` over `Polynomial ℝ`. -/
noncomputable def realModsAux : ℕ → Polynomial ℝ → Polynomial ℝ → List (Polynomial ℝ)
  | 0, _, _ => []
  | n + 1, p, q =>
      if realSize p = 0 then []
      else p :: realModsAux n q (realNextMod p q)

theorem realModsAux_of_size_zero (n : ℕ) (p q : Polynomial ℝ) (hp : realSize p = 0) :
    realModsAux n p q = [] := by
  cases n with
  | zero => rfl
  | succ m => simp only [realModsAux, if_pos hp]

theorem realModsAux_of_eq_zero (n : ℕ) (q : Polynomial ℝ) :
    realModsAux n 0 q = [] :=
  realModsAux_of_size_zero n 0 q ((realSize_eq_zero_iff 0).mpr rfl)

theorem ne_zero_of_mem_realModsAux (n : ℕ) (p q f : Polynomial ℝ)
    (hf : f ∈ realModsAux n p q) : f ≠ 0 := by
  induction n generalizing p q with
  | zero => cases hf
  | succ m ih =>
    unfold realModsAux at hf
    by_cases hp : realSize p = 0
    · simp only [if_pos hp, List.not_mem_nil] at hf
    · simp only [if_neg hp, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact (realSize_eq_zero_iff f).not.mp hp
      · exact ih q (realNextMod p q) hf

/-- Once `realSize q < realSize p` and `realSize p ≤ fuel`, `realModsAux` stabilizes. -/
theorem realModsAux_eq_of_lt (fuel : ℕ) (p q : Polynomial ℝ)
    (hqp : realSize q < realSize p) (hf : realSize p ≤ fuel) :
    realModsAux fuel p q = realModsAux (realSize p) p q := by
  induction hp_size : realSize p using Nat.strongRecOn generalizing fuel p q with
  | ind s ih =>
    have hs_pos : 0 < s := by omega
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    have hp_nz : realSize p ≠ 0 := by omega
    unfold realModsAux
    rw [if_neg hp_nz, if_neg hp_nz]
    congr 1
    by_cases hq0 : realSize q = 0
    · rw [realModsAux_of_size_zero n q _ hq0, realModsAux_of_size_zero m q _ hq0]
    · have hq_ne : q ≠ 0 := (realSize_eq_zero_iff q).not.mp hq0
      have hlt : realSize (realNextMod p q) < realSize q := realSize_realNextMod_lt p q hq_ne
      have hqm : realSize q ≤ m := by omega
      have hqn : realSize q ≤ n := by omega
      have ih1 := ih (realSize q) (by omega) n q (realNextMod p q) hlt hqn rfl
      have ih2 := ih (realSize q) (by omega) m q (realNextMod p q) hlt hqm rfl
      exact ih1.trans ih2.symm

/-- Canonical signed-remainder sequence over `Polynomial ℝ`. -/
noncomputable def realMods (p q : Polynomial ℝ) : List (Polynomial ℝ) :=
  realModsAux (realSize q + 1) p q

/-- Any fuel bound at least `realSize q + 1` produces `realMods p q`. -/
theorem realModsAux_eq_realMods (fuel : ℕ) (p q : Polynomial ℝ)
    (hf : realSize q + 1 ≤ fuel) :
    realModsAux fuel p q = realMods p q := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hqn : realSize q ≤ n := by omega
  unfold realMods realModsAux
  by_cases hp0 : realSize p = 0
  · simp only [if_pos hp0]
  · simp only [if_neg hp0]
    congr 1
    by_cases hq0 : realSize q = 0
    · rw [realModsAux_of_size_zero n q _ hq0,
          realModsAux_of_size_zero (realSize q) q _ hq0]
    · have hq_ne : q ≠ 0 := (realSize_eq_zero_iff q).not.mp hq0
      exact realModsAux_eq_of_lt n q (realNextMod p q)
        (realSize_realNextMod_lt p q hq_ne) hqn

theorem realMods_zero_left (q : Polynomial ℝ) : realMods 0 q = [] :=
  realModsAux_of_eq_zero (realSize q + 1) q

theorem realMods_cons (p q : Polynomial ℝ) (hp : p ≠ 0) :
    realMods p q = p :: realMods q (realNextMod p q) := by
  have hp0 : realSize p ≠ 0 := (realSize_eq_zero_iff p).not.mpr hp
  unfold realMods
  conv_lhs => unfold realModsAux
  rw [if_neg hp0]
  congr 1
  by_cases hq : q = 0
  · subst hq
    rw [realModsAux_of_eq_zero, realModsAux_of_eq_zero]
  · have hlt : realSize (realNextMod p q) + 1 ≤ realSize q :=
      realSize_realNextMod_lt p q hq
    exact realModsAux_eq_realMods (realSize q) q (realNextMod p q) hlt

theorem ne_zero_of_mem_realMods (p q f : Polynomial ℝ)
    (hf : f ∈ realMods p q) : f ≠ 0 :=
  ne_zero_of_mem_realModsAux (realSize q + 1) p q f hf

/-- Sign-change counter on real lists using strict-negative adjacent products
(matching MathComp's `changes`). -/
noncomputable def realChanges : List ℝ → ℕ
  | [] => 0
  | a :: xs =>
      (haveI := Classical.propDecidable; if a * xs.headD 0 < 0 then 1 else 0) +
        realChanges xs

@[simp] theorem realChanges_nil : realChanges [] = 0 := rfl

@[simp] theorem realChanges_singleton (a : ℝ) : realChanges [a] = 0 := by
  classical
  simp [realChanges]

theorem realChanges_cons_cons (a b : ℝ) (xs : List ℝ) :
    realChanges (a :: b :: xs) =
      (haveI := Classical.propDecidable; if a * b < 0 then 1 else 0) +
        realChanges (b :: xs) := rfl

/-- Sign variations of a real list after removing zeros. -/
noncomputable def signVariations (xs : List ℝ) : ℕ := by
  classical
  exact realChanges (xs.filter (fun x ↦ decide (x ≠ 0)))

theorem signVariations_eq_realChanges (xs : List ℝ) (h : ∀ x ∈ xs, x ≠ 0) :
    signVariations xs = realChanges xs := by
  classical
  unfold signVariations
  have hfilt : xs.filter (fun x ↦ decide (x ≠ 0)) = xs :=
    List.filter_eq_self.mpr (fun x hx ↦ decide_eq_true (h x hx))
  rw [hfilt]

@[simp] theorem signVariations_nil : signVariations [] = 0 := by
  classical
  simp [signVariations]

@[simp] theorem signVariations_zero_cons (xs : List ℝ) :
    signVariations (0 :: xs) = signVariations xs := by
  classical
  simp [signVariations]

theorem signVariations_cons_zero_cons (a : ℝ) (xs : List ℝ) :
    signVariations (a :: 0 :: xs) = signVariations (a :: xs) := by
  classical
  by_cases ha : a = 0 <;> simp [signVariations, ha]

/-- When `a` and `c` have strictly opposite signs (`a * c < 0`), the sign
variation count of `a :: b :: c :: xs` is `1 + signVariations (c :: xs)` for
every real `b` (including `b = 0`). -/
theorem signVariations_cons_cons_of_mul_neg (a b c : ℝ) (xs : List ℝ)
    (hac : a * c < 0) :
    signVariations (a :: b :: c :: xs) = 1 + signVariations (c :: xs) := by
  classical
  have ha : a ≠ 0 := fun h ↦ by simp [h] at hac
  have hc : c ≠ 0 := fun h ↦ by simp [h] at hac
  by_cases hb : b = 0
  · subst hb
    simp only [signVariations, List.filter, decide_eq_true ha, decide_eq_true hc,
      ne_self_iff_false, decide_false]
    rw [realChanges_cons_cons, if_pos hac]
  · simp only [signVariations, List.filter, decide_eq_true ha,
      decide_eq_true hb, decide_eq_true hc]
    rw [realChanges_cons_cons, realChanges_cons_cons, ← add_assoc]
    congr 1
    have hprod : (a * b) * (b * c) < 0 := by
      have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      have hneg : b ^ 2 * (a * c) < 0 := mul_neg_of_pos_of_neg hb2 hac
      linarith [show (a * b) * (b * c) = b ^ 2 * (a * c) by ring]
    by_cases hab : a * b < 0
    · have hbc : ¬ b * c < 0 := by
        intro hbc
        have := mul_pos_of_neg_of_neg hab hbc
        linarith
      simp only [if_pos hab, if_neg hbc, add_zero]
    · have hab_pos : 0 < a * b := by
        have hab_ne : a * b ≠ 0 := mul_ne_zero ha hb
        exact lt_of_le_of_ne (not_lt.mp hab) hab_ne.symm
      have hbc : b * c < 0 := by
        by_contra hbc
        have := mul_nonneg (le_of_lt hab_pos) (not_lt.mp hbc)
        linarith
      simp only [if_neg hab, if_pos hbc, zero_add]

/-- Sign factor `(-1)^(s - 1)` for a polynomial of `realSize` `s` at `-∞`. -/
noncomputable def minftySignFactor (s : ℕ) : ℝ := (-1 : ℝ) ^ (s - 1)

/-- Leading-term sign representative at `-∞`: `(-1)^(realSize p - 1) * lc(p)`. -/
noncomputable def minftyCoeff (p : Polynomial ℝ) : ℝ :=
  minftySignFactor (realSize p) * p.leadingCoeff

theorem minftyCoeff_zero : minftyCoeff 0 = 0 := by
  simp [minftyCoeff]

theorem minftyCoeff_eq_of_ne_zero (p : Polynomial ℝ) (hp : p ≠ 0) :
    minftyCoeff p = (-1 : ℝ) ^ p.natDegree * p.leadingCoeff := by
  classical
  simp only [minftyCoeff, minftySignFactor, realSize, if_neg hp, Nat.add_sub_cancel]

theorem minftyCoeff_ne_zero (p : Polynomial ℝ) (hp : p ≠ 0) :
    minftyCoeff p ≠ 0 := by
  rw [minftyCoeff_eq_of_ne_zero p hp]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Polynomial.leadingCoeff_ne_zero.mpr hp)

/-- Sequence of leading coefficients at `+∞`. -/
noncomputable def realSeqPInfty (ps : List (Polynomial ℝ)) : List ℝ :=
  ps.map Polynomial.leadingCoeff

/-- Sequence of signed leading coefficients at `-∞`. -/
noncomputable def realSeqMInfty (ps : List (Polynomial ℝ)) : List ℝ :=
  ps.map minftyCoeff

/-- Cauchy/Sturm variation difference on `(-∞, +∞)`:
`changes(SeqMInfty ps) - changes(SeqPInfty ps)`. -/
noncomputable def realChangesPoly (ps : List (Polynomial ℝ)) : ℤ :=
  (realChanges (realSeqMInfty ps) : ℤ) - (realChanges (realSeqPInfty ps) : ℤ)

theorem realSeqPInfty_ne_zero_of_ne_zero (ps : List (Polynomial ℝ))
    (hps : ∀ p ∈ ps, p ≠ 0) :
    ∀ x ∈ realSeqPInfty ps, x ≠ 0 := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
  exact Polynomial.leadingCoeff_ne_zero.mpr (hps p hp)

theorem realSeqMInfty_ne_zero_of_ne_zero (ps : List (Polynomial ℝ))
    (hps : ∀ p ∈ ps, p ≠ 0) :
    ∀ x ∈ realSeqMInfty ps, x ≠ 0 := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
  exact minftyCoeff_ne_zero p (hps p hp)

theorem realChangesPoly_eq_signVariations (ps : List (Polynomial ℝ))
    (hps : ∀ p ∈ ps, p ≠ 0) :
    realChangesPoly ps =
      (signVariations (realSeqMInfty ps) : ℤ) -
        (signVariations (realSeqPInfty ps) : ℤ) := by
  rw [signVariations_eq_realChanges _ (realSeqMInfty_ne_zero_of_ne_zero ps hps),
      signVariations_eq_realChanges _ (realSeqPInfty_ne_zero_of_ne_zero ps hps)]
  rfl

theorem realChangesPoly_realMods_eq_signVariations (p q : Polynomial ℝ) :
    realChangesPoly (realMods p q) =
      (signVariations (realSeqMInfty (realMods p q)) : ℤ) -
        (signVariations (realSeqPInfty (realMods p q)) : ℤ) :=
  realChangesPoly_eq_signVariations (realMods p q) (ne_zero_of_mem_realMods p q)

/-- Three-valued integer sign of a real number (`-1`, `0`, `1`). -/
noncomputable def realSign (x : ℝ) : ℤ :=
  haveI := Classical.propDecidable
  if 0 < x then 1 else if x < 0 then -1 else 0

@[simp] theorem realSign_zero : realSign 0 = 0 := by
  classical
  simp [realSign]

theorem realSign_pos {x : ℝ} (h : 0 < x) : realSign x = 1 := by
  classical
  simp [realSign, h]

theorem realSign_neg {x : ℝ} (h : x < 0) : realSign x = -1 := by
  classical
  have hnp : ¬ 0 < x := not_lt.mpr (le_of_lt h)
  simp [realSign, hnp, h]

theorem realSign_eq_zero_iff (x : ℝ) : realSign x = 0 ↔ x = 0 := by
  rcases lt_trichotomy 0 x with h | rfl | h
  · simp [realSign_pos h, ne_of_gt h]
  · simp
  · simp [realSign_neg h, ne_of_lt h]

theorem realSign_ne_zero_iff (x : ℝ) : realSign x ≠ 0 ↔ x ≠ 0 :=
  (realSign_eq_zero_iff x).not

theorem realSign_neg_val (x : ℝ) : realSign (-x) = -realSign x := by
  rcases lt_trichotomy 0 x with h | rfl | h
  · rw [realSign_pos h, realSign_neg (neg_lt_zero.mpr h)]
  · simp
  · rw [realSign_neg h, realSign_pos (neg_pos.mpr h), neg_neg]

theorem realSign_mul (x y : ℝ) : realSign (x * y) = realSign x * realSign y := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · rcases lt_trichotomy 0 y with hy | rfl | hy
    · rw [realSign_pos hx, realSign_pos hy, realSign_pos (mul_pos hx hy), mul_one]
    · simp
    · rw [realSign_pos hx, realSign_neg hy, realSign_neg (mul_neg_of_pos_of_neg hx hy), one_mul]
  · simp
  · rcases lt_trichotomy 0 y with hy | rfl | hy
    · rw [realSign_neg hx, realSign_pos hy, realSign_neg (mul_neg_of_neg_of_pos hx hy), mul_one]
    · simp
    · rw [realSign_neg hx, realSign_neg hy, realSign_pos (mul_pos_of_neg_of_neg hx hy)]
      ring

theorem realSign_pow (x : ℝ) (n : ℕ) : realSign (x ^ n) = realSign x ^ n := by
  induction n with
  | zero => simp [realSign_pos zero_lt_one]
  | succ m ih => rw [pow_succ, pow_succ, realSign_mul, ih]

@[simp] theorem realSign_neg_one : realSign (-1 : ℝ) = -1 :=
  realSign_neg (by norm_num)

@[simp] theorem realSign_one : realSign (1 : ℝ) = 1 :=
  realSign_pos zero_lt_one

theorem realSign_neg_one_pow (n : ℕ) : realSign ((-1 : ℝ) ^ n) = (-1 : ℤ) ^ n := by
  rw [realSign_pow, realSign_neg_one]

theorem realSign_sq_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    realSign x * realSign x = 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [realSign_neg h]; rfl
  · rw [realSign_pos h]; rfl

theorem realSign_mul_of_pos {c x : ℝ} (hc : 0 < c) :
    realSign (c * x) = realSign x := by
  rw [realSign_mul, realSign_pos hc, one_mul]

theorem realSign_mul_of_neg {c x : ℝ} (hc : c < 0) :
    realSign (c * x) = -realSign x := by
  rw [realSign_mul, realSign_neg hc, neg_one_mul]

theorem two_mul_ite_neg_sub {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (haveI := Classical.propDecidable
     2 * ((if u < 0 then (1 : ℤ) else 0) - (if v < 0 then (1 : ℤ) else 0))) =
      realSign v - realSign u := by
  classical
  rcases lt_or_gt_of_ne hu with h1 | h1 <;> rcases lt_or_gt_of_ne hv with h2 | h2
  · simp [h1, h2, realSign_neg h1, realSign_neg h2]
  · simp [h1, not_lt.mpr (le_of_lt h2), realSign_neg h1, realSign_pos h2]
  · simp [not_lt.mpr (le_of_lt h1), h2, realSign_pos h1, realSign_neg h2]
  · simp [not_lt.mpr (le_of_lt h1), not_lt.mpr (le_of_lt h2), realSign_pos h1, realSign_pos h2]

/-- Taylor-shifted polynomial `p(X + t)`. -/
noncomputable def shiftPoly (p : Polynomial ℝ) (t : ℝ) : Polynomial ℝ :=
  p.comp (Polynomial.X + Polynomial.C t)

@[simp] theorem shiftPoly_zero (t : ℝ) : shiftPoly 0 t = 0 :=
  Polynomial.zero_comp

@[simp] theorem shiftPoly_eq_zero_iff (p : Polynomial ℝ) (t : ℝ) :
    shiftPoly p t = 0 ↔ p = 0 :=
  Polynomial.comp_X_add_C_eq_zero_iff

theorem shiftPoly_mul (p q : Polynomial ℝ) (t : ℝ) :
    shiftPoly (p * q) t = shiftPoly p t * shiftPoly q t :=
  Polynomial.mul_comp p q (Polynomial.X + Polynomial.C t)

theorem shiftPoly_C (c t : ℝ) : shiftPoly (Polynomial.C c) t = Polynomial.C c :=
  Polynomial.C_comp

theorem shiftPoly_X_sub_C_self (t : ℝ) :
    shiftPoly (Polynomial.X - Polynomial.C t) t = Polynomial.X := by
  simp [shiftPoly]

theorem coeff_zero_shiftPoly (p : Polynomial ℝ) (t : ℝ) :
    (shiftPoly p t).coeff 0 = p.eval t := by
  rw [Polynomial.coeff_zero_eq_eval_zero, shiftPoly, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]

theorem rootMultiplicity_eq_natTrailingDegree_shiftPoly (p : Polynomial ℝ) (t : ℝ) :
    p.rootMultiplicity t = (shiftPoly p t).natTrailingDegree :=
  Polynomial.rootMultiplicity_eq_natTrailingDegree

theorem derivative_shiftPoly (p : Polynomial ℝ) (t : ℝ) :
    (shiftPoly p t).derivative = shiftPoly p.derivative t := by
  simp [shiftPoly, Polynomial.derivative_comp]

/-- Right-germ coefficient of `p` at `t`, defined algebraically as the trailing
coefficient of `p(X + t)`. -/
noncomputable def germRight (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  (shiftPoly p t).trailingCoeff

/-- Left-germ coefficient of `p` at `t`. -/
noncomputable def germLeft (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ p.rootMultiplicity t * germRight p t

@[simp] theorem germRight_zero (t : ℝ) : germRight 0 t = 0 := by
  simp [germRight]

@[simp] theorem germLeft_zero (t : ℝ) : germLeft 0 t = 0 := by
  simp [germLeft]

@[simp] theorem germRight_eq_zero_iff (p : Polynomial ℝ) (t : ℝ) :
    germRight p t = 0 ↔ p = 0 := by
  rw [germRight, Polynomial.trailingCoeff_eq_zero, shiftPoly_eq_zero_iff]

theorem germRight_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (t : ℝ) :
    germRight p t ≠ 0 :=
  (germRight_eq_zero_iff p t).not.mpr hp

@[simp] theorem germLeft_eq_zero_iff (p : Polynomial ℝ) (t : ℝ) :
    germLeft p t = 0 ↔ p = 0 := by
  simp [germLeft, pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)]

theorem germLeft_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (t : ℝ) :
    germLeft p t ≠ 0 :=
  (germLeft_eq_zero_iff p t).not.mpr hp

theorem trailingCoeff_mul_real (f g : Polynomial ℝ) :
    (f * g).trailingCoeff = f.trailingCoeff * g.trailingCoeff := by
  by_cases hf : f = 0
  · simp [hf]
  · by_cases hg : g = 0
    · simp [hg]
    · rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_mul hf hg,
          Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]

theorem germRight_mul (p q : Polynomial ℝ) (t : ℝ) :
    germRight (p * q) t = germRight p t * germRight q t := by
  rw [germRight, shiftPoly_mul, trailingCoeff_mul_real]
  rfl

theorem germRight_pow (p : Polynomial ℝ) (n : ℕ) (t : ℝ) :
    germRight (p ^ n) t = germRight p t ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, germRight, shiftPoly, Polynomial.one_comp,
      Polynomial.trailingCoeff, Polynomial.natTrailingDegree_one, Polynomial.coeff_one_zero]
  | succ m ih => rw [pow_succ, pow_succ, germRight_mul, ih]

theorem germLeft_mul {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (t : ℝ) :
    germLeft (p * q) t = germLeft p t * germLeft q t := by
  unfold germLeft
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hp hq), pow_add, germRight_mul]
  ring

theorem germRight_of_eval_ne_zero {p : Polynomial ℝ} {t : ℝ} (h : p.eval t ≠ 0) :
    germRight p t = p.eval t := by
  have hc0 : (shiftPoly p t).coeff 0 ≠ 0 := by rwa [coeff_zero_shiftPoly]
  rw [germRight, Polynomial.trailingCoeff_eq_coeff_zero hc0, coeff_zero_shiftPoly]

theorem germLeft_of_eval_ne_zero {p : Polynomial ℝ} {t : ℝ} (h : p.eval t ≠ 0) :
    germLeft p t = p.eval t := by
  have hnr : ¬ p.IsRoot t := h
  rw [germLeft, Polynomial.rootMultiplicity_eq_zero hnr, pow_zero, one_mul,
      germRight_of_eval_ne_zero h]

@[simp] theorem germRight_X_sub_C_self (t : ℝ) :
    germRight (Polynomial.X - Polynomial.C t) t = 1 := by
  rw [germRight, shiftPoly_X_sub_C_self, Polynomial.trailingCoeff,
      Polynomial.natTrailingDegree_X, Polynomial.coeff_X_one]

theorem natTrailingDegree_eq_of_coeff_ne_zero {f : Polynomial ℝ} {n : ℕ}
    (hn : f.coeff n ≠ 0) (h0 : ∀ i < n, f.coeff i = 0) :
    f.natTrailingDegree = n := by
  have hf : f ≠ 0 := fun h ↦ hn (by simp [h])
  exact le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hn)
    (Polynomial.le_natTrailingDegree hf h0)

theorem trailingCoeff_eq_of_coeff_ne_zero {f : Polynomial ℝ} {n : ℕ}
    (hn : f.coeff n ≠ 0) (h0 : ∀ i < n, f.coeff i = 0) :
    f.trailingCoeff = f.coeff n := by
  rw [Polynomial.trailingCoeff, natTrailingDegree_eq_of_coeff_ne_zero hn h0]

/-- At any root `t` of a nonzero polynomial `p`, `p.derivative` has root multiplicity
`p.rootMultiplicity t - 1` and positive-multiple right germ. -/
theorem rootMultiplicity_and_germRight_derivative {p : Polynomial ℝ} {t : ℝ}
    (hp : p ≠ 0) (ht : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 ∧
      germRight p.derivative t = (p.rootMultiplicity t : ℝ) * germRight p t := by
  let f := shiftPoly p t
  let m := p.rootMultiplicity t
  have hm_pos : 0 < m := (Polynomial.rootMultiplicity_pos hp).mpr ht
  have hm_eq : f.natTrailingDegree = m :=
    (rootMultiplicity_eq_natTrailingDegree_shiftPoly p t).symm
  have htc : f.coeff m = germRight p t := by
    change f.coeff m = f.trailingCoeff
    rw [Polynomial.trailingCoeff, hm_eq]
  have htc_ne : germRight p t ≠ 0 := germRight_ne_zero hp t
  have hm_real_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm_pos)
  have hcoeff_m1 : f.derivative.coeff (m - 1) = (m : ℝ) * germRight p t := by
    rw [Polynomial.coeff_derivative]
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm1
    rw [hm1, htc, hcast, mul_comm]
  have hne : f.derivative.coeff (m - 1) ≠ 0 := by
    rw [hcoeff_m1]
    exact mul_ne_zero hm_real_ne htc_ne
  have hzero : ∀ i < m - 1, f.derivative.coeff i = 0 := by
    intro i hi
    rw [Polynomial.coeff_derivative]
    have hi1 : i + 1 < f.natTrailingDegree := by omega
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi1, zero_mul]
  have hntd := natTrailingDegree_eq_of_coeff_ne_zero hne hzero
  have htr := trailingCoeff_eq_of_coeff_ne_zero hne hzero
  refine ⟨?_, ?_⟩
  · rw [rootMultiplicity_eq_natTrailingDegree_shiftPoly, ← derivative_shiftPoly, hntd]
  · rw [germRight, ← derivative_shiftPoly, htr, hcoeff_m1]

theorem coeff_mul_eq_zero_of_lt_natTrailingDegree_right (a q : Polynomial ℝ) {i : ℕ}
    (hi : i < q.natTrailingDegree) :
    (a * q).coeff i = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨u, v⟩ huv
  rw [Finset.mem_antidiagonal] at huv
  have hv : v < q.natTrailingDegree := by omega
  rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hv, mul_zero]

/-- When `p.rootMultiplicity t < q.rootMultiplicity t`, `realNextMod p q` has the same
root multiplicity as `p` at `t` and opposite-sign right germ. -/
theorem rootMultiplicity_and_germRight_realNextMod {p q : Polynomial ℝ} {t : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hlt : p.rootMultiplicity t < q.rootMultiplicity t) :
    (realNextMod p q).rootMultiplicity t = p.rootMultiplicity t ∧
      germRight (realNextMod p q) t = -realNextModScale p q * germRight p t ∧
      realNextMod p q ≠ 0 := by
  have hid := congrArg (fun f ↦ shiftPoly f t) (realNextMod_sturm_identity p q)
  simp only [shiftPoly, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp] at hid
  change Polynomial.C (realNextModScale p q) * shiftPoly p t =
    shiftPoly (realNextModQuot p q) t * shiftPoly q t - shiftPoly (realNextMod p q) t at hid
  have hR_eq : shiftPoly (realNextMod p q) t =
      shiftPoly (realNextModQuot p q) t * shiftPoly q t -
        Polynomial.C (realNextModScale p q) * shiftPoly p t := by
    rw [hid]; ring
  let m := p.rootMultiplicity t
  have hm_eq : (shiftPoly p t).natTrailingDegree = m :=
    (rootMultiplicity_eq_natTrailingDegree_shiftPoly p t).symm
  have hq_eq : (shiftPoly q t).natTrailingDegree = q.rootMultiplicity t :=
    (rootMultiplicity_eq_natTrailingDegree_shiftPoly q t).symm
  have hcoeff_le : ∀ i ≤ m,
      (shiftPoly (realNextMod p q) t).coeff i =
        -realNextModScale p q * (shiftPoly p t).coeff i := by
    intro i hi
    have hi_q : i < (shiftPoly q t).natTrailingDegree := by omega
    rw [hR_eq, Polynomial.coeff_sub,
        coeff_mul_eq_zero_of_lt_natTrailingDegree_right _ _ hi_q,
        Polynomial.coeff_C_mul, zero_sub, neg_mul]
  have hScale_pos : 0 < realNextModScale p q := realNextModScale_pos p q hq
  have htc : (shiftPoly p t).coeff m = germRight p t := by
    change (shiftPoly p t).coeff m = (shiftPoly p t).trailingCoeff
    rw [Polynomial.trailingCoeff, hm_eq]
  have hcoeff_m : (shiftPoly (realNextMod p q) t).coeff m =
      -realNextModScale p q * germRight p t := by
    rw [hcoeff_le m (le_refl m), htc]
  have hne : (shiftPoly (realNextMod p q) t).coeff m ≠ 0 := by
    rw [hcoeff_m]
    exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hScale_pos)) (germRight_ne_zero hp t)
  have hzero : ∀ i < m, (shiftPoly (realNextMod p q) t).coeff i = 0 := by
    intro i hi
    rw [hcoeff_le i (le_of_lt hi)]
    have hi' : i < (shiftPoly p t).natTrailingDegree := by omega
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi', mul_zero]
  have hntd := natTrailingDegree_eq_of_coeff_ne_zero hne hzero
  have htr := trailingCoeff_eq_of_coeff_ne_zero hne hzero
  have hr_ne : realNextMod p q ≠ 0 := by
    intro h0
    rw [h0, shiftPoly_zero, Polynomial.coeff_zero] at hne
    exact hne rfl
  refine ⟨?_, ?_, hr_ne⟩
  · rw [rootMultiplicity_eq_natTrailingDegree_shiftPoly, hntd]
  · rw [germRight, htr, hcoeff_m]

/-- Local Cauchy index jump of `q / p` at `t : ℝ`. -/
noncomputable def cauchyJump (p q : Polynomial ℝ) (t : ℝ) : ℤ :=
  haveI := Classical.propDecidable
  if p ≠ 0 ∧ q ≠ 0 ∧ q.rootMultiplicity t < p.rootMultiplicity t ∧
      Odd (p.rootMultiplicity t - q.rootMultiplicity t) then
    realSign (germRight p t * germRight q t)
  else 0

@[simp] theorem cauchyJump_zero_left (q : Polynomial ℝ) (t : ℝ) :
    cauchyJump 0 q t = 0 := by
  classical
  simp [cauchyJump]

@[simp] theorem cauchyJump_zero_right (p : Polynomial ℝ) (t : ℝ) :
    cauchyJump p 0 t = 0 := by
  classical
  simp [cauchyJump]

theorem cauchyJump_eq_zero_of_not_mem_roots {p q : Polynomial ℝ} {t : ℝ}
    (ht : t ∉ p.roots.toFinset) : cauchyJump p q t = 0 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  · have hnr : ¬ p.IsRoot t := by
      intro hr
      exact ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hr))
    have hm0 : p.rootMultiplicity t = 0 := Polynomial.rootMultiplicity_eq_zero hnr
    simp [cauchyJump, hm0]

/-- Global Cauchy index of `q / p` over `ℝ`. -/
noncomputable def cauchyIndex (p q : Polynomial ℝ) : ℤ :=
  ∑ t ∈ p.roots.toFinset, cauchyJump p q t

@[simp] theorem cauchyIndex_zero_left (q : Polynomial ℝ) : cauchyIndex 0 q = 0 := by
  simp [cauchyIndex]

@[simp] theorem cauchyIndex_zero_right (p : Polynomial ℝ) : cauchyIndex p 0 = 0 := by
  simp [cauchyIndex]

theorem cauchyIndex_eq_sum_of_subset (p q : Polynomial ℝ) (S : Finset ℝ)
    (hS : p.roots.toFinset ⊆ S) :
    cauchyIndex p q = ∑ t ∈ S, cauchyJump p q t := by
  unfold cauchyIndex
  exact Finset.sum_subset hS (fun t _ ht ↦ cauchyJump_eq_zero_of_not_mem_roots ht)

/-- Tarski query over `ℝ`: sum of `realSign (q.eval x)` over distinct real roots `x` of `p`. -/
noncomputable def tarskiQueryR (p q : Polynomial ℝ) : ℤ :=
  ∑ x ∈ p.roots.toFinset, realSign (q.eval x)

@[simp] theorem tarskiQueryR_zero_left (q : Polynomial ℝ) : tarskiQueryR 0 q = 0 := by
  simp [tarskiQueryR]

/-- At any root `t` of a nonzero polynomial `p`, `cauchyJump p (p.derivative * q) t`
equals `realSign (q.eval t)`. -/
theorem cauchyJump_derivative_mul {p : Polynomial ℝ} (q : Polynomial ℝ) {t : ℝ}
    (hp : p ≠ 0) (ht : p.IsRoot t) :
    cauchyJump p (p.derivative * q) t = realSign (q.eval t) := by
  classical
  rcases rootMultiplicity_and_germRight_derivative hp ht with ⟨hdm, hdg⟩
  have hm_pos : 0 < p.rootMultiplicity t := (Polynomial.rootMultiplicity_pos hp).mpr ht
  have hp' : p.derivative ≠ 0 := by
    intro h0
    have h := germRight_ne_zero hp t
    have hm_ne : (p.rootMultiplicity t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm_pos)
    rw [h0, germRight_zero] at hdg
    exact mul_ne_zero hm_ne h hdg.symm
  by_cases hqt : q.eval t = 0
  · rw [hqt, realSign_zero]
    by_cases hq : q = 0
    · simp [hq]
    · have hq_pos : 0 < q.rootMultiplicity t :=
        (Polynomial.rootMultiplicity_pos hq).mpr hqt
      have hmul_ne : p.derivative * q ≠ 0 := mul_ne_zero hp' hq
      have hrm : (p.derivative * q).rootMultiplicity t =
          p.rootMultiplicity t - 1 + q.rootMultiplicity t := by
        rw [Polynomial.rootMultiplicity_mul hmul_ne, hdm]
      have hnlt : ¬ (p.derivative * q).rootMultiplicity t < p.rootMultiplicity t := by omega
      simp [cauchyJump, hnlt]
  · have hq : q ≠ 0 := fun h0 ↦ hqt (by simp [h0])
    have hmul_ne : p.derivative * q ≠ 0 := mul_ne_zero hp' hq
    have hq_rm : q.rootMultiplicity t = 0 := Polynomial.rootMultiplicity_eq_zero hqt
    have hrm : (p.derivative * q).rootMultiplicity t = p.rootMultiplicity t - 1 := by
      rw [Polynomial.rootMultiplicity_mul hmul_ne, hdm, hq_rm, add_zero]
    have hlt : (p.derivative * q).rootMultiplicity t < p.rootMultiplicity t := by omega
    have hsub : p.rootMultiplicity t - (p.derivative * q).rootMultiplicity t = 1 := by omega
    have hodd : Odd (p.rootMultiplicity t - (p.derivative * q).rootMultiplicity t) := by
      rw [hsub]; exact odd_one
    unfold cauchyJump
    rw [if_pos ⟨hp, hmul_ne, hlt, hodd⟩]
    rw [germRight_mul, hdg, germRight_of_eval_ne_zero hqt]
    have hpos : 0 < (p.rootMultiplicity t : ℝ) := Nat.cast_pos.mpr hm_pos
    have hsq : realSign (germRight p t) * realSign (germRight p t) = 1 :=
      realSign_sq_of_ne_zero (germRight_ne_zero hp t)
    calc
      realSign (germRight p t * ((p.rootMultiplicity t : ℝ) * germRight p t * q.eval t))
        = realSign ((p.rootMultiplicity t : ℝ) *
            (germRight p t * germRight p t * q.eval t)) := by ring_nf
      _ = realSign (germRight p t * germRight p t * q.eval t) := realSign_mul_of_pos hpos
      _ = realSign (germRight p t) * realSign (germRight p t) * realSign (q.eval t) := by
            rw [realSign_mul, realSign_mul]
      _ = realSign (q.eval t) := by rw [hsq, one_mul]

theorem cauchyIndex_derivative_mul (p q : Polynomial ℝ) :
    cauchyIndex p (p.derivative * q) = tarskiQueryR p q := by
  by_cases hp : p = 0
  · simp [hp]
  · unfold cauchyIndex tarskiQueryR
    refine Finset.sum_congr rfl ?_
    intro t ht
    have hr : p.IsRoot t := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp ht)
    exact cauchyJump_derivative_mul q hp hr

/-- Recurrence negation for Cauchy jumps under `realNextMod`. -/
theorem cauchyJump_realNextMod {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (t : ℝ) :
    cauchyJump q (realNextMod p q) t = -cauchyJump q p t := by
  classical
  by_cases hlt : p.rootMultiplicity t < q.rootMultiplicity t
  · rcases rootMultiplicity_and_germRight_realNextMod hp hq hlt with ⟨hrm, hg, hr_ne⟩
    have hlt' : (realNextMod p q).rootMultiplicity t < q.rootMultiplicity t := by
      rwa [hrm]
    unfold cauchyJump
    rw [hrm]
    by_cases hodd : Odd (q.rootMultiplicity t - p.rootMultiplicity t)
    · rw [if_pos ⟨hq, hr_ne, hlt, hodd⟩, if_pos ⟨hq, hp, hlt, hodd⟩, hg]
      have hneg : -realNextModScale p q < 0 :=
        neg_lt_zero.mpr (realNextModScale_pos p q hq)
      calc
        realSign (germRight q t * (-realNextModScale p q * germRight p t))
          = realSign (-realNextModScale p q * (germRight q t * germRight p t)) := by ring_nf
        _ = -realSign (germRight q t * germRight p t) := realSign_mul_of_neg hneg
    · rw [if_neg (by tauto), if_neg (by tauto), neg_zero]
  · by_cases hr0 : realNextMod p q = 0
    · simp [cauchyJump, hr0, hlt]
    · have hnlt' : ¬ (realNextMod p q).rootMultiplicity t < q.rootMultiplicity t := by
        intro hlt'
        have hq_le : q.rootMultiplicity t ≤ p.rootMultiplicity t := not_lt.mp hlt
        have hdvd_p : (Polynomial.X - Polynomial.C t) ^ q.rootMultiplicity t ∣ p :=
          (Polynomial.le_rootMultiplicity_iff hp).mp hq_le
        have hdvd_q : (Polynomial.X - Polynomial.C t) ^ q.rootMultiplicity t ∣ q :=
          Polynomial.pow_rootMultiplicity_dvd q t
        have hdvd_r : (Polynomial.X - Polynomial.C t) ^ q.rootMultiplicity t ∣
            realNextMod p q :=
          ((dvd_and_dvd_realNextMod_iff _ p q hq).mp ⟨hdvd_p, hdvd_q⟩).2
        have hle_r : q.rootMultiplicity t ≤ (realNextMod p q).rootMultiplicity t :=
          (Polynomial.le_rootMultiplicity_iff hr0).mpr hdvd_r
        omega
      simp [cauchyJump, hlt, hnlt']

theorem cauchyIndex_realNextMod {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    cauchyIndex q (realNextMod p q) = -cauchyIndex q p := by
  unfold cauchyIndex
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro t _
  exact cauchyJump_realNextMod hp hq t

/-- Local sign change of a single polynomial `f` across `t`. -/
noncomputable def singleRootJump (f : Polynomial ℝ) (t : ℝ) : ℤ :=
  haveI := Classical.propDecidable
  (if germLeft f t < 0 then 1 else 0) - (if germRight f t < 0 then 1 else 0)

theorem two_mul_singleRootJump {f : Polynomial ℝ} (hf : f ≠ 0) (t : ℝ) :
    2 * singleRootJump f t = realSign (germRight f t) - realSign (germLeft f t) :=
  two_mul_ite_neg_sub (germLeft_ne_zero hf t) (germRight_ne_zero hf t)

theorem realSign_germLeft (f : Polynomial ℝ) (t : ℝ) :
    realSign (germLeft f t) = (-1 : ℤ) ^ f.rootMultiplicity t * realSign (germRight f t) := by
  rw [germLeft, realSign_mul, realSign_neg_one_pow]

/-- Symmetry identity relating `cauchyJump p q t + cauchyJump q p t` to `singleRootJump (p * q) t`. -/
theorem cauchyJump_add_symm {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (t : ℝ) :
    cauchyJump p q t + cauchyJump q p t = singleRootJump (p * q) t := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  suffices h2 : 2 * (cauchyJump p q t + cauchyJump q p t) = 2 * singleRootJump (p * q) t by
    omega
  rw [two_mul_singleRootJump hpq t, realSign_germLeft,
      Polynomial.rootMultiplicity_mul hpq, germRight_mul]
  let m := p.rootMultiplicity t
  let k := q.rootMultiplicity t
  have hs_comm : realSign (germRight q t * germRight p t) =
      realSign (germRight p t * germRight q t) := by
    rw [mul_comm]
  unfold cauchyJump
  rw [hs_comm]
  rcases Nat.even_or_odd (m + k) with heven | hodd
  · have hno1 : ¬ (p ≠ 0 ∧ q ≠ 0 ∧ k < m ∧ Odd (m - k)) := by
      rintro ⟨_, _, hkm, hod⟩
      have hsum : m + k = (m - k) + 2 * k := by omega
      have : Odd (m + k) := by
        rw [hsum]
        exact Odd.add_even hod (even_two_mul k)
      exact (Nat.not_even_iff_odd.mpr this) heven
    have hno2 : ¬ (q ≠ 0 ∧ p ≠ 0 ∧ m < k ∧ Odd (k - m)) := by
      rintro ⟨_, _, hmk, hod⟩
      have hsum : m + k = (k - m) + 2 * m := by omega
      have : Odd (m + k) := by
        rw [hsum]
        exact Odd.add_even hod (even_two_mul m)
      exact (Nat.not_even_iff_odd.mpr this) heven
    rw [if_neg hno1, if_neg hno2, Even.neg_one_pow heven, one_mul, sub_self,
        add_zero, mul_zero]
  · rw [Odd.neg_one_pow hodd, neg_one_mul, sub_neg_eq_add, ← two_mul]
    rcases lt_trichotomy k m with hkm | hkm | hmk
    · have hod1 : Odd (m - k) := by
        have hsum : m + k = (m - k) + 2 * k := by omega
        rcases Nat.even_or_odd (m - k) with hev | hod
        · exfalso
          have : Even (m + k) := by rw [hsum]; exact Even.add hev (even_two_mul k)
          exact (Nat.not_even_iff_odd.mpr hodd) this
        · exact hod
      have hnmk : ¬ (q ≠ 0 ∧ p ≠ 0 ∧ m < k ∧ Odd (k - m)) := by
        rintro ⟨_, _, hmk, _⟩
        exact (not_lt.mpr (le_of_lt hkm)) hmk
      rw [if_pos ⟨hp, hq, hkm, hod1⟩, if_neg hnmk, add_zero]
    · exfalso
      have : Even (m + k) := by rw [hkm, ← two_mul]; exact even_two_mul m
      exact (Nat.not_even_iff_odd.mpr hodd) this
    · have hod2 : Odd (k - m) := by
        have hsum : m + k = (k - m) + 2 * m := by omega
        rcases Nat.even_or_odd (k - m) with hev | hod
        · exfalso
          have : Even (m + k) := by rw [hsum]; exact Even.add hev (even_two_mul m)
          exact (Nat.not_even_iff_odd.mpr hodd) this
        · exact hod
      have hnkm : ¬ (p ≠ 0 ∧ q ≠ 0 ∧ k < m ∧ Odd (m - k)) := by
        rintro ⟨_, _, hkm, _⟩
        exact (not_lt.mpr (le_of_lt hmk)) hkm
      rw [if_neg hnkm, if_pos ⟨hq, hp, hmk, hod2⟩, zero_add]

/-- Every positive-degree polynomial over `ℝ` takes arbitrarily large values of the
form `p.leadingCoeff * p.eval M` for `M ≥ r`. -/
theorem exists_eval_ge_of_degree_pos (p : Polynomial ℝ) (hd : 0 < p.degree) :
    ∀ (B r : ℝ), ∃ M ≥ r, B ≤ p.leadingCoeff * p.eval M := by
  refine Polynomial.degree_pos_induction_on p hd ?_ ?_ ?_
  · intro a ha B r
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    let M := max r (B / a ^ 2)
    refine ⟨M, le_max_left _ _, ?_⟩
    simp only [Polynomial.leadingCoeff_mul_X, Polynomial.leadingCoeff_C,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hBM : B / a ^ 2 ≤ M := le_max_right _ _
    have hmul : a ^ 2 * (B / a ^ 2) ≤ a ^ 2 * M :=
      mul_le_mul_of_nonneg_left hBM (le_of_lt ha2)
    have hcancel : a ^ 2 * (B / a ^ 2) = B := mul_div_cancel₀ B (ne_of_gt ha2)
    linarith [show a * (a * M) = a ^ 2 * M by ring]
  · intro q hq ih B r
    obtain ⟨M, hMr, hMB⟩ := ih (max B 0) (max r 1)
    refine ⟨M, le_trans (le_max_left r 1) hMr, ?_⟩
    simp only [Polynomial.leadingCoeff_mul_X, Polynomial.eval_mul, Polynomial.eval_X]
    have hM1 : 1 ≤ M := le_trans (le_max_right r 1) hMr
    have hq_nonneg : 0 ≤ q.leadingCoeff * q.eval M := le_trans (le_max_right B 0) hMB
    have hB : B ≤ q.leadingCoeff * q.eval M := le_trans (le_max_left B 0) hMB
    nlinarith
  · intro q a hq ih B r
    obtain ⟨M, hMr, hMB⟩ := ih (B - q.leadingCoeff * a) r
    refine ⟨M, hMr, ?_⟩
    have hdeg : (Polynomial.C a).degree < q.degree :=
      Polynomial.degree_C_le.trans_lt hq
    rw [add_comm, Polynomial.leadingCoeff_add_of_degree_lt hdeg]
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    linarith

theorem exists_pos_leadingCoeff_mul_eval (g : Polynomial ℝ) (hg : g ≠ 0) (r : ℝ) :
    ∃ M ≥ r, 0 < g.leadingCoeff * g.eval M := by
  rcases le_or_gt g.degree 0 with hd | hd
  · refine ⟨r, le_refl r, ?_⟩
    rw [Polynomial.eq_C_of_degree_le_zero hd] at hg ⊢
    have hc : g.coeff 0 ≠ 0 := fun h ↦ hg (by simp [h])
    simp only [Polynomial.leadingCoeff_C, Polynomial.eval_C]
    exact mul_self_pos.mpr hc
  · obtain ⟨M, hMr, hM⟩ := exists_eval_ge_of_degree_pos g hd 1 r
    exact ⟨M, hMr, lt_of_lt_of_le zero_lt_one hM⟩

/-- If `g ≠ 0` has no real roots `≥ r`, then `g.eval r` has the same sign as `g.leadingCoeff`. -/
theorem realSign_eval_of_forall_root_lt (g : Polynomial ℝ) (hg : g ≠ 0) (r : ℝ)
    (hroots : ∀ x : ℝ, g.IsRoot x → x < r) :
    realSign (g.eval r) = realSign g.leadingCoeff := by
  obtain ⟨M, hMr, hM⟩ := exists_pos_leadingCoeff_mul_eval g hg r
  have hlc_ne : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg
  have hpos : 0 < g.leadingCoeff * g.eval r := by
    refine lt_of_not_ge (fun hle ↦ ?_)
    have hcont : ContinuousOn (fun x ↦ g.leadingCoeff * g.eval x) (Set.Icc r M) :=
      (continuous_const.mul g.continuous).continuousOn
    have h0_mem : (0 : ℝ) ∈ Set.Icc (g.leadingCoeff * g.eval r) (g.leadingCoeff * g.eval M) :=
      ⟨hle, le_of_lt hM⟩
    obtain ⟨z, ⟨hzr, _⟩, hfz⟩ := intermediate_value_Icc hMr hcont h0_mem
    have hgz : g.IsRoot z := (mul_eq_zero.mp hfz).resolve_left hlc_ne
    exact (not_lt_of_ge hzr) (hroots z hgz)
  have hsq : realSign g.leadingCoeff * realSign g.leadingCoeff = 1 :=
    realSign_sq_of_ne_zero hlc_ne
  have hmul : realSign g.leadingCoeff * realSign (g.eval r) = 1 := by
    rw [← realSign_mul, realSign_pos hpos]
  calc
    realSign (g.eval r) = (realSign g.leadingCoeff * realSign g.leadingCoeff) *
        realSign (g.eval r) := by rw [hsq, one_mul]
    _ = realSign g.leadingCoeff * (realSign g.leadingCoeff * realSign (g.eval r)) := by ring
    _ = realSign g.leadingCoeff := by rw [hmul, mul_one]

/-- When `f ≠ 0` has no real roots at all, `minftyCoeff f` and `f.leadingCoeff` have the
same sign. -/
theorem realSign_leadingCoeff_eq_minftyCoeff_of_no_roots (f : Polynomial ℝ) (hf : f ≠ 0)
    (hroots : ∀ x : ℝ, ¬ f.IsRoot x) :
    realSign f.leadingCoeff = realSign (minftyCoeff f) := by
  have h1 : realSign (f.eval 0) = realSign f.leadingCoeff :=
    realSign_eval_of_forall_root_lt f hf 0 (fun x hx ↦ False.elim (hroots x hx))
  let fn := f.comp (Polynomial.C (-1 : ℝ) * Polynomial.X)
  have hfn_coeff_gen : ∀ (p : Polynomial ℝ) (i : ℕ),
      (p.comp (Polynomial.C (-1 : ℝ) * Polynomial.X)).coeff i = p.coeff i * (-1 : ℝ) ^ i := by
    intro p
    refine Polynomial.induction_on' p ?_ ?_
    · intro p₁ p₂ h₁ h₂ i
      rw [Polynomial.add_comp, Polynomial.coeff_add, h₁, h₂, Polynomial.coeff_add, add_mul]
    · intro k a i
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
          Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow,
          ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
          Polynomial.coeff_C_mul_X_pow]
      split_ifs with h
      · subst h; rfl
      · simp
  have hfn_coeff : ∀ i : ℕ, fn.coeff i = f.coeff i * (-1 : ℝ) ^ i := hfn_coeff_gen f
  have hfn_ne : fn ≠ 0 := by
    intro h0
    have hc := hfn_coeff f.natDegree
    rw [h0, Polynomial.coeff_zero, Polynomial.coeff_natDegree] at hc
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf)
      (pow_ne_zero _ (by norm_num)) hc.symm
  have hfn_roots : ∀ x : ℝ, ¬ fn.IsRoot x := by
    intro x hx
    rw [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, neg_one_mul] at hx
    exact hroots (-x) hx
  have h2 : realSign (fn.eval 0) = realSign fn.leadingCoeff :=
    realSign_eval_of_forall_root_lt fn hfn_ne 0 (fun x hx ↦ False.elim (hfn_roots x hx))
  have heval0 : fn.eval 0 = f.eval 0 := by
    simp [fn, Polynomial.eval_comp]
  have hnd : fn.natDegree = f.natDegree := by
    refine le_antisymm ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro i hi
      rw [hfn_coeff i, Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
    · refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [hfn_coeff f.natDegree, Polynomial.coeff_natDegree]
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf) (pow_ne_zero _ (by norm_num))
  have hlc_fn : fn.leadingCoeff = minftyCoeff f := by
    rw [minftyCoeff_eq_of_ne_zero f hf, Polynomial.leadingCoeff, hnd,
        hfn_coeff f.natDegree, Polynomial.coeff_natDegree, mul_comm]
  rw [← h1, ← heval0, h2, hlc_fn]

/-- Telescoping sign-change theorem for a single nonzero polynomial `f`:
the sum of `realSign (germRight f x) - realSign (germLeft f x)` over all distinct real roots `x`
of `f` equals `realSign f.leadingCoeff - realSign (minftyCoeff f)`. -/
theorem sum_realSign_germ_sub_eq (f : Polynomial ℝ) (hf : f ≠ 0) :
    ∑ x ∈ f.roots.toFinset, (realSign (germRight f x) - realSign (germLeft f x)) =
      realSign f.leadingCoeff - realSign (minftyCoeff f) := by
  induction hn : f.natDegree using Nat.strongRecOn generalizing f with
  | ind n ih =>
    by_cases hne : f.roots.toFinset.Nonempty
    · let r := f.roots.toFinset.max' hne
      have hr_mem : r ∈ f.roots.toFinset := Finset.max'_mem _ hne
      have hr_root : f.IsRoot r := (Polynomial.mem_roots hf).mp (Multiset.mem_toFinset.mp hr_mem)
      let m := f.rootMultiplicity r
      have hm_pos : 0 < m := (Polynomial.rootMultiplicity_pos hf).mpr hr_root
      let g := f /ₘ (Polynomial.X - Polynomial.C r) ^ m
      have hfg : (Polynomial.X - Polynomial.C r) ^ m * g = f :=
        Polynomial.pow_mul_divByMonic_rootMultiplicity_eq f r
      have hmonic : ((Polynomial.X - Polynomial.C r) ^ m).Monic :=
        (Polynomial.monic_X_sub_C r).pow m
      have hg_ne : g ≠ 0 := by
        intro hg0
        rw [hg0, mul_zero] at hfg
        exact hf hfg.symm
      have hgr_ne : g.eval r ≠ 0 :=
        Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero r hf
      have hnd_f : f.natDegree = m + g.natDegree := by
        rw [← hfg, Polynomial.natDegree_mul hmonic.ne_zero hg_ne,
            Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      have hnd_lt : g.natDegree < n := by omega
      have hlc_fg : f.leadingCoeff = g.leadingCoeff := by
        rw [← hfg, Polynomial.leadingCoeff_monic_mul hmonic]
      have hminf_fg : minftyCoeff f = (-1 : ℝ) ^ m * minftyCoeff g := by
        rw [minftyCoeff_eq_of_ne_zero f hf, minftyCoeff_eq_of_ne_zero g hg_ne,
            hnd_f, pow_add, hlc_fg, mul_assoc]
      have hr_not_mem_g : r ∉ g.roots.toFinset := by
        intro hmem
        exact hgr_ne ((Polynomial.mem_roots hg_ne).mp (Multiset.mem_toFinset.mp hmem))
      have hroots_eq : f.roots.toFinset = insert r g.roots.toFinset := by
        ext x
        simp only [Multiset.mem_toFinset, Finset.mem_insert,
          Polynomial.mem_roots hf, Polynomial.mem_roots hg_ne]
        rw [← hfg, Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero,
            pow_eq_zero_iff (ne_of_gt hm_pos), sub_eq_zero]
        rfl
      have hg_roots_lt : ∀ x : ℝ, g.IsRoot x → x < r := by
        intro x hx
        have hx_f : x ∈ f.roots.toFinset := by
          rw [hroots_eq]
          exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hg_ne).mpr hx))
        have hx_le : x ≤ r := Finset.le_max' _ x hx_f
        have hx_ne : x ≠ r := fun h ↦ by subst h; exact hgr_ne hx
        exact lt_of_le_of_ne hx_le hx_ne
      have hsign_gr : realSign (g.eval r) = realSign g.leadingCoeff :=
        realSign_eval_of_forall_root_lt g hg_ne r hg_roots_lt
      have hterm_r :
          realSign (germRight f r) - realSign (germLeft f r) =
            (1 - (-1 : ℤ) ^ m) * realSign g.leadingCoeff := by
        have hgr_f : germRight f r = g.eval r := by
          rw [← hfg, germRight_mul, germRight_pow, germRight_X_sub_C_self,
              one_pow, one_mul, germRight_of_eval_ne_zero hgr_ne]
        rw [realSign_germLeft, show f.rootMultiplicity r = m from rfl, hgr_f, hsign_gr]
        ring
      have hterm_other : ∀ x ∈ g.roots.toFinset,
          realSign (germRight f x) - realSign (germLeft f x) =
            (-1 : ℤ) ^ m * (realSign (germRight g x) - realSign (germLeft g x)) := by
        intro x hx
        have hx_root : g.IsRoot x := (Polynomial.mem_roots hg_ne).mp (Multiset.mem_toFinset.mp hx)
        have hxr : x < r := hg_roots_lt x hx_root
        have hpow_eval : ((Polynomial.X - Polynomial.C r) ^ m).eval x = (x - r) ^ m := by
          simp
        have hpow_ne : ((Polynomial.X - Polynomial.C r) ^ m).eval x ≠ 0 := by
          rw [hpow_eval]
          exact pow_ne_zero m (sub_ne_zero.mpr (ne_of_lt hxr))
        have hsign_pow : realSign (((Polynomial.X - Polynomial.C r) ^ m).eval x) = (-1 : ℤ) ^ m := by
          rw [hpow_eval, realSign_pow, realSign_neg (sub_neg.mpr hxr)]
        have hgr_x : realSign (germRight f x) = (-1 : ℤ) ^ m * realSign (germRight g x) := by
          rw [← hfg, germRight_mul, germRight_of_eval_ne_zero hpow_ne, realSign_mul, hsign_pow]
        have hgl_x : realSign (germLeft f x) = (-1 : ℤ) ^ m * realSign (germLeft g x) := by
          rw [← hfg, germLeft_mul hmonic.ne_zero hg_ne, germLeft_of_eval_ne_zero hpow_ne,
              realSign_mul, hsign_pow]
        rw [hgr_x, hgl_x, ← mul_sub]
      have ih_g := ih g.natDegree hnd_lt g hg_ne rfl
      rw [hroots_eq, Finset.sum_insert hr_not_mem_g, hterm_r,
          Finset.sum_congr rfl (fun x hx ↦ hterm_other x hx), ← Finset.mul_sum,
          ih_g, hlc_fg, hminf_fg, realSign_mul, realSign_neg_one_pow]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty]
      have hno_roots : ∀ x : ℝ, ¬ f.IsRoot x := by
        intro x hx
        have : x ∈ f.roots.toFinset :=
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf).mpr hx)
        rw [hne] at this
        simp at this
      rw [realSign_leadingCoeff_eq_minftyCoeff_of_no_roots f hf hno_roots, sub_self]

/-- Sign-change step at `±∞` for a single polynomial `f`. -/
noncomputable def singleInftyJump (f : Polynomial ℝ) : ℤ :=
  haveI := Classical.propDecidable
  (if minftyCoeff f < 0 then 1 else 0) - (if f.leadingCoeff < 0 then 1 else 0)

theorem two_mul_singleInftyJump {f : Polynomial ℝ} (hf : f ≠ 0) :
    2 * singleInftyJump f = realSign f.leadingCoeff - realSign (minftyCoeff f) :=
  two_mul_ite_neg_sub (minftyCoeff_ne_zero f hf) (Polynomial.leadingCoeff_ne_zero.mpr hf)

theorem sum_singleRootJump_eq_singleInftyJump (f : Polynomial ℝ) (hf : f ≠ 0) :
    ∑ x ∈ f.roots.toFinset, singleRootJump f x = singleInftyJump f := by
  suffices h2 : 2 * (∑ x ∈ f.roots.toFinset, singleRootJump f x) = 2 * singleInftyJump f by
    omega
  rw [Finset.mul_sum,
      Finset.sum_congr rfl (fun x _ ↦ two_mul_singleRootJump hf x),
      two_mul_singleInftyJump hf]
  exact sum_realSign_germ_sub_eq f hf

/-- Sign-change step at `±∞` between consecutive polynomials `p` and `q`. -/
noncomputable def inftyJump (p q : Polynomial ℝ) : ℤ :=
  haveI := Classical.propDecidable
  (if minftyCoeff p * minftyCoeff q < 0 then 1 else 0) -
    (if p.leadingCoeff * q.leadingCoeff < 0 then 1 else 0)

theorem minftyCoeff_mul {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    minftyCoeff (p * q) = minftyCoeff p * minftyCoeff q := by
  rw [minftyCoeff_eq_of_ne_zero (p * q) (mul_ne_zero hp hq),
      minftyCoeff_eq_of_ne_zero p hp,
      minftyCoeff_eq_of_ne_zero q hq,
      Polynomial.natDegree_mul hp hq, pow_add, Polynomial.leadingCoeff_mul]
  ring

theorem inftyJump_eq_singleInftyJump_mul {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    inftyJump p q = singleInftyJump (p * q) := by
  unfold inftyJump singleInftyJump
  rw [minftyCoeff_mul hp hq, Polynomial.leadingCoeff_mul]

theorem cauchyIndex_add_symm {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    cauchyIndex p q + cauchyIndex q p = inftyJump p q := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  have hsub_p : p.roots.toFinset ⊆ (p * q).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.roots_mul hpq, Multiset.mem_add]
    exact Or.inl (Multiset.mem_toFinset.mp hx)
  have hsub_q : q.roots.toFinset ⊆ (p * q).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.roots_mul hpq, Multiset.mem_add]
    exact Or.inr (Multiset.mem_toFinset.mp hx)
  rw [cauchyIndex_eq_sum_of_subset p q (p * q).roots.toFinset hsub_p,
      cauchyIndex_eq_sum_of_subset q p (p * q).roots.toFinset hsub_q,
      ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun x _ ↦ cauchyJump_add_symm hp hq x),
      sum_singleRootJump_eq_singleInftyJump (p * q) hpq,
      inftyJump_eq_singleInftyJump_mul hp hq]

/-- Recurrence theorem for the global Cauchy index under `realNextMod`. -/
theorem cauchyIndex_step {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    cauchyIndex p q = inftyJump p q + cauchyIndex q (realNextMod p q) := by
  rw [cauchyIndex_realNextMod hp hq, ← cauchyIndex_add_symm hp hq]
  ring

/-- Recurrence theorem for `realChangesPoly (realMods p q)`. -/
theorem realChangesPoly_realMods_step {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    realChangesPoly (realMods p q) =
      inftyJump p q + realChangesPoly (realMods q (realNextMod p q)) := by
  classical
  rw [realMods_cons p q hp, realMods_cons q (realNextMod p q) hq]
  unfold realChangesPoly realSeqMInfty realSeqPInfty inftyJump
  simp only [List.map, realChanges_cons_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  ring

/-- For all real polynomials `p` and `q`, `realChangesPoly (realMods p q)` equals
the global Cauchy index `cauchyIndex p q`. -/
theorem realChangesPoly_realMods_eq_cauchyIndex (p q : Polynomial ℝ) :
    realChangesPoly (realMods p q) = cauchyIndex p q := by
  induction hs : realSize q using Nat.strongRecOn generalizing p q with
  | ind s ih =>
    by_cases hp : p = 0
    · subst hp
      simp [realMods_zero_left, realChangesPoly, realSeqMInfty, realSeqPInfty]
    · by_cases hq : q = 0
      · subst hq
        rw [realMods_cons p 0 hp, realMods_zero_left]
        simp [realChangesPoly, realSeqMInfty, realSeqPInfty]
      · have hlt : realSize (realNextMod p q) < s := by
          rw [← hs]
          exact realSize_realNextMod_lt p q hq
        rw [realChangesPoly_realMods_step hp hq, cauchyIndex_step hp hq,
            ih (realSize (realNextMod p q)) hlt q (realNextMod p q) rfl]

/-- Semantic Sturm–Tarski query over `Polynomial ℝ`. -/
noncomputable def realTaqR (p q : Polynomial ℝ) : ℤ :=
  realChangesPoly (realMods p (p.derivative * q))

/-- **Sturm–Tarski Theorem over `Polynomial ℝ`**:
For any polynomials `p, q : Polynomial ℝ` (including `p = 0`, `q = 0`, repeated roots,
and common roots), `realTaqR p q` equals `∑ x ∈ p.roots.toFinset, realSign (q.eval x)`. -/
theorem realTaqR_eq_tarskiQueryR (p q : Polynomial ℝ) :
    realTaqR p q = tarskiQueryR p q := by
  rw [realTaqR, realChangesPoly_realMods_eq_cauchyIndex, cauchyIndex_derivative_mul]

theorem realTaqR_one (p : Polynomial ℝ) :
    realTaqR p 1 = (p.roots.toFinset.card : ℤ) := by
  rw [realTaqR_eq_tarskiQueryR, tarskiQueryR]
  simp [Polynomial.eval_one, realSign_one]


end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003

open Grunbaum2003.FormulaCompiler.Parametric

theorem sturm_tarski_and_signed_remainder_cauchy_index :
    ∃ (realSign : ℝ → ℤ)
      (realNextMod : Polynomial ℝ → Polynomial ℝ → Polynomial ℝ)
      (realMods : Polynomial ℝ → Polynomial ℝ → List (Polynomial ℝ))
      (realChangesPoly : List (Polynomial ℝ) → ℤ)
      (cauchyIndex : Polynomial ℝ → Polynomial ℝ → ℤ),
      (∀ x : ℝ, realSign x = (haveI := Classical.propDecidable; if 0 < x then 1 else if x < 0 then -1 else 0)) ∧
      (∀ p q : Polynomial ℝ, q ≠ 0 → (realNextMod p q).degree < q.degree) ∧
      (∀ p q : Polynomial ℝ, p ≠ 0 → realMods p q = p :: realMods q (realNextMod p q)) ∧
      (∀ p q : Polynomial ℝ, realChangesPoly (realMods p q) = cauchyIndex p q) ∧
      (∀ p q : Polynomial ℝ,
        realChangesPoly (realMods p (p.derivative * q)) =
          ∑ x ∈ p.roots.toFinset, realSign (q.eval x)) ∧
      (∀ p : Polynomial ℝ,
        realChangesPoly (realMods p p.derivative) = (p.roots.toFinset.card : ℤ)) := by
  refine ⟨realSign, realNextMod, realMods, realChangesPoly, cauchyIndex,
    fun _ => rfl, degree_realNextMod_lt, realMods_cons,
    realChangesPoly_realMods_eq_cauchyIndex, realTaqR_eq_tarskiQueryR, ?_⟩
  intro p
  simpa [realTaqR] using realTaqR_one p

end Grunbaum2003

theorem solution :
    ∃ (realSign : ℝ → ℤ)
      (realNextMod : Polynomial ℝ → Polynomial ℝ → Polynomial ℝ)
      (realMods : Polynomial ℝ → Polynomial ℝ → List (Polynomial ℝ))
      (realChangesPoly : List (Polynomial ℝ) → ℤ)
      (cauchyIndex : Polynomial ℝ → Polynomial ℝ → ℤ),
      (∀ x : ℝ, realSign x = (haveI := Classical.propDecidable; if 0 < x then 1 else if x < 0 then -1 else 0)) ∧
      (∀ p q : Polynomial ℝ, q ≠ 0 → (realNextMod p q).degree < q.degree) ∧
      (∀ p q : Polynomial ℝ, p ≠ 0 → realMods p q = p :: realMods q (realNextMod p q)) ∧
      (∀ p q : Polynomial ℝ, realChangesPoly (realMods p q) = cauchyIndex p q) ∧
      (∀ p q : Polynomial ℝ,
        realChangesPoly (realMods p (p.derivative * q)) =
          ∑ x ∈ p.roots.toFinset, realSign (q.eval x)) ∧
      (∀ p : Polynomial ℝ,
        realChangesPoly (realMods p p.derivative) = (p.roots.toFinset.card : ℤ)) :=
  Grunbaum2003.sturm_tarski_and_signed_remainder_cauchy_index
