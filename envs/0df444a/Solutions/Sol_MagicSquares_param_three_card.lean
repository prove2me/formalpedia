-- Prove2me | solution 1 for MagicSquares.param_three_card
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T17:23:21.82375+00:00
-- url     : https://prove2.me/submissions/db22e0b4-3aa3-4f5b-acd2-5454481f28a1

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

open scoped BigOperators

namespace MagicSquares

/-! ## Fibre decomposition of the MacMahon parameter set

For a fixed `a`, the admissible `c` form the interval `[paramLo, paramHi]`, so
`paramSet e` is a sigma over `a ∈ [0, 2e]` of those intervals. Counting each
interval and summing the two resulting arithmetic progressions gives MacMahon's
`2e^2 + 2e + 1`. -/

/-- Lower end of the admissible `c`-interval for a given `a`. -/
def paramLo (e a : ℕ) : ℕ := if a ≤ e then e - a else a - e

/-- Upper end of the admissible `c`-interval for a given `a`. -/
def paramHi (e a : ℕ) : ℕ := if a ≤ e then e + a else 3 * e - a

/-- Number of admissible `c` for a given `a`. -/
def paramWidth (e a : ℕ) : ℕ := if a ≤ e then 2 * a + 1 else 4 * e - 2 * a + 1

/-- Admissibility of `(a, c)` is exactly membership of `c` in the interval
`[paramLo e a, paramHi e a]`, provided `a ≤ 2 * e` (which admissibility forces). -/
private theorem isParam3_iff_interval (e a c : ℕ) (ha : a ≤ 2 * e) :
    IsParam3 e a c ↔ paramLo e a ≤ c ∧ c ≤ paramHi e a := by
  unfold IsParam3 paramLo paramHi
  by_cases hle : a ≤ e
  · simp [hle]
    constructor <;> intro h <;> omega
  · simp [hle]
    constructor <;> intro h <;> omega

/-- The interval is non-empty, so its cardinality is `hi - lo + 1 = width`. -/
private theorem paramInterval_card (e a : ℕ) (ha : a ≤ 2 * e) :
    (Finset.Icc (paramLo e a) (paramHi e a)).card = paramWidth e a := by
  simp [paramLo, paramHi, paramWidth]
  by_cases hle : a ≤ e
  · simp [hle]
    omega
  · simp [hle]
    omega

/-- Sum of the first `n` odd numbers. -/
private theorem sum_odd_range (n : ℕ) : (∑ a ∈ Finset.range n, (2 * a + 1)) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The decreasing odd progression `2e-1, 2e-3, …, 1` also sums to `e^2`;
this is `sum_odd_range` after the reflection `b ↦ e-1-b`. -/
private theorem sum_odd_reflected (e : ℕ) :
    (∑ b ∈ Finset.range e, (2 * e - 2 * b - 1)) = e ^ 2 := by
  have hterm : ∀ b ∈ Finset.range e, 2 * e - 2 * b - 1 = 2 * (e - 1 - b) + 1 := by
    intro b hb
    have hb' : b < e := Finset.mem_range.mp hb
    omega
  calc
    (∑ b ∈ Finset.range e, (2 * e - 2 * b - 1))
        = ∑ b ∈ Finset.range e, (2 * (e - 1 - b) + 1) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hterm b hb
    _ = ∑ b ∈ Finset.range e, (2 * b + 1) := Finset.sum_range_reflect (fun k => 2 * k + 1) e
    _ = e ^ 2 := sum_odd_range e

/-- Summing the widths over `a = 0, …, 2e`, split at `a = e`. -/
private theorem sum_paramWidth (e : ℕ) :
    (∑ a ∈ Finset.range (2 * e + 1), paramWidth e a) = 2 * e ^ 2 + 2 * e + 1 := by
  have hsplit := Finset.sum_range_add (fun a => paramWidth e a) (e + 1) e
  have htwo : 2 * e + 1 = (e + 1) + e := by omega
  conv_lhs => rw [htwo]
  rw [hsplit]
  have hfirst : (∑ a ∈ Finset.range (e + 1), paramWidth e a) = (e + 1) ^ 2 := by
    calc
      (∑ a ∈ Finset.range (e + 1), paramWidth e a)
          = ∑ a ∈ Finset.range (e + 1), (2 * a + 1) := by
            apply Finset.sum_congr rfl
            intro a ha
            have ha' : a ≤ e := by
              have := Finset.mem_range.mp ha
              omega
            simp [paramWidth, ha']
      _ = (e + 1) ^ 2 := sum_odd_range (e + 1)
  have hsecond : (∑ b ∈ Finset.range e, paramWidth e (e + 1 + b)) = e ^ 2 := by
    calc
      (∑ b ∈ Finset.range e, paramWidth e (e + 1 + b))
          = ∑ b ∈ Finset.range e, (2 * e - 2 * b - 1) := by
            apply Finset.sum_congr rfl
            intro b hb
            have hnot : ¬ e + 1 + b ≤ e := by omega
            have hb' : b < e := Finset.mem_range.mp hb
            simp [paramWidth, hnot]
            omega
      _ = e ^ 2 := sum_odd_reflected e
  rw [hfirst, hsecond]
  ring

end MagicSquares

open MagicSquares

/-- `paramCount e = 2 e^2 + 2 e + 1`.

*Fibre decomposition.* Split `paramSet e ⊆ [0,2e] × [0,2e]` according to the
first coordinate. For fixed `a` the admissible `c` are exactly the integers in
`[paramLo e a, paramHi e a]`, where the endpoints are `e-a` / `e+a` for
`a ≤ e` and `a-e` / `3e-a` for `a ≥ e`. Hence `paramSet e` is in bijection with
the sigma (disjoint union over `a ∈ [0, 2e]`) of those intervals, so

  `paramCount e = Σ_{a=0}^{2e} paramWidth e a`.

*Summation.* The widths are `2a+1` on `[0, e]` and `4e-2a+1` on `[e+1, 2e]`;
the first block of odd numbers sums to `(e+1)^2` and the second (a reflected
block of odd numbers) to `e^2`, giving `2e^2 + 2e + 1`. -/
theorem solution (e : ℕ) : paramCount e = 2 * e ^ 2 + 2 * e + 1 := by
  classical
  unfold paramCount
  let sigma : Finset ((a : ℕ) × ℕ) :=
    (Finset.range (2 * e + 1)).sigma (fun a => Finset.Icc (paramLo e a) (paramHi e a))
  have hbij : (paramSet e).card = sigma.card := by
    refine Finset.card_bij (fun ac _hac => (⟨ac.1, ac.2⟩ : (a : ℕ) × ℕ)) ?mem ?inj ?surj
    · intro ac hac
      have hac' : ac ∈
          ((Finset.range (2 * e + 1)).product (Finset.range (2 * e + 1))).filter
            (fun ac => IsParam3 e ac.1 ac.2) := by
        simpa [paramSet] using hac
      have hf := Finset.mem_filter.mp hac'
      have hmem : ac.1 < 2 * e + 1 ∧ ac.2 < 2 * e + 1 := by
        have := hf.1
        simpa [Finset.mem_product, Finset.mem_range] using this
      simp only [sigma, Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc]
      refine ⟨hmem.1, ?_⟩
      exact (isParam3_iff_interval e ac.1 ac.2 (by omega)).mp hf.2
    · intro ac₁ hac₁ ac₂ hac₂ heq
      have h1 : ac₁.1 = ac₂.1 := congrArg Sigma.fst heq
      have h2 : ac₁.2 = ac₂.2 := congrArg (fun x : (a : ℕ) × ℕ => x.2) heq
      ext <;> assumption
    · intro x hx
      refine ⟨(x.1, x.2), ?_, rfl⟩
      simp only [sigma, Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hx
      have hres : (x.1, x.2) ∈
          ((Finset.range (2 * e + 1)).product (Finset.range (2 * e + 1))).filter
            (fun ac => IsParam3 e ac.1 ac.2) := by
        apply Finset.mem_filter.mpr
        constructor
        · have hi_le : paramHi e x.1 ≤ 2 * e := by
            simp [paramHi]
            by_cases hle : x.1 ≤ e
            · simp [hle]
              omega
            · simp [hle]
              omega
          have hc_lt : x.2 < 2 * e + 1 := by omega
          simpa [Finset.mem_product, Finset.mem_range] using And.intro hx.1 hc_lt
        · exact (isParam3_iff_interval e x.1 x.2 (by omega)).mpr ⟨hx.2.1, hx.2.2⟩
      simpa [paramSet] using hres
  rw [hbij]
  unfold sigma
  rw [Finset.card_sigma]
  calc
    (∑ a ∈ Finset.range (2 * e + 1), (Finset.Icc (paramLo e a) (paramHi e a)).card)
        = ∑ a ∈ Finset.range (2 * e + 1), paramWidth e a := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha2 : a ≤ 2 * e := by
            have := Finset.mem_range.mp ha
            omega
          exact paramInterval_card e a ha2
    _ = 2 * e ^ 2 + 2 * e + 1 := sum_paramWidth e
