-- Prove2me | solution 1 for GuthMaynard.sum_norm_dirichlet_poly_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:29:26.176924+00:00
-- url     : https://prove2.me/submissions/d1ef804a-b05a-41b4-bd87-a0d88d15f1e0

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_heath_brown_large_values
section
namespace GuthMaynardS56

open MeasureTheory Complex Set

end GuthMaynardS56
end

section
namespace GuthMaynardS56

open MeasureTheory Complex Set

end GuthMaynardS56
end

section
namespace GuthMaynardS56

open MeasureTheory Complex Set

end GuthMaynardS56
end

section
namespace GuthMaynardS56

open MeasureTheory Complex Set
open scoped Real

end GuthMaynardS56
end

section
namespace GuthMaynardS56

open MeasureTheory Complex Set
open scoped Real

end GuthMaynardS56
end

section
namespace GuthMaynardS56

end GuthMaynardS56
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-!
# Blueprint: Guth–Maynard Proposition 6.1 (the `S₂` bound)

Route (pp. 17–20 of arXiv v2, with the Mellin inversion replaced by Fourier inversion in the
variable `x = log u`, and van der Corput replaced by one explicit integration by parts):

* `S₂ = 3N³ ∑_{t₁,t₂,t₃} ĥ_{t₃-t₁}(0) A(t₁-t₂) A(t₂-t₃)` with `A(t) = ∑_{m ≠ 0} ĥ_t(mN)`.
* `A(t)` = (positive `m ≤ M`) + (negative `m ≤ M`, a conjugate of the positive sum at `-t`) + tail.
* Positive part: `w(u)² = u⁻¹ G(log u)`, `G(x) = eˣ w(eˣ)²`, and Fourier inversion of `G` give
  `∑_{m=1}^M ĥ_t(mN) = ∫ Ĝ(ρ) (∑_m (mN)^{-iτ}) I(τ) dρ`, `τ = t + 2πρ`,
  `I(τ) = ∫_N^{2NM} v^{-1+iτ} e(-v) dv`, and `|I(τ)| ≪ |τ|^{-1/2}`.
* Hölder + divisor bound + Heath-Brown (Theorem 1.6) bound the Dirichlet polynomial sums.
-/

/-- The Dirichlet polynomial `∑_{1 ≤ m ≤ M} c_m m^{it}`. -/
noncomputable def dpoly (c : ℕ → ℂ) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, c m * (m : ℂ) ^ ((t : ℂ) * I)

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartA
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartA
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part A: the oscillatory integral -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartA
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartA
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartB
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartB
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part B: Fourier inversion in `log u` -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartB
open Complex MeasureTheory FourierTransform


end GuthMaynard.S2.PartB
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartD
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartD
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part D: reduction of `S₂` and the splitting of `A(t)` -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartD
open Complex MeasureTheory FourierTransform


end GuthMaynard.S2.PartD
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartE1
open Complex MeasureTheory FourierTransform
/-! Helpers on `Gw` (same proofs as in Part B, restated here so this file only needs the
Blueprint). -/

/-! Dirichlet polynomial facts. -/

/-! Cauchy–Schwarz for a nonnegative integrable weight. -/

/-! The three factors of the integrand in `norm_sum_hHat_le`. -/

end GuthMaynard.S2.PartE1
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part E: the approximate functional equation, squared; the sum over pairs -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartC
open Complex MeasureTheory FourierTransform
/-- Pointwise bound behind the divisor bound. -/
theorem divisor_local {η : ℝ} (hη : 0 < η) (p a : ℕ) (hp : 2 ≤ p) :
    ((a : ℝ) + 1) ≤ (if p < ⌈(2 : ℝ) ^ (1 / η)⌉₊ then 1 + 1 / (η * Real.log 2) else 1) *
      (((p : ℝ) ^ η) ^ a) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  split_ifs with h
  · have hl : 0 < η * Real.log 2 := mul_pos hη (Real.log_pos (by norm_num))
    have h1 : (1 : ℝ) + a * (η * Real.log 2) ≤ ((2 : ℝ) ^ η) ^ a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      have := Real.add_one_le_exp (Real.log 2 * (η * a))
      nlinarith
    have h2 : ((2 : ℝ) ^ η) ^ a ≤ ((p : ℝ) ^ η) ^ a :=
      pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hη.le) _
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have h3 : (a : ℝ) + 1 ≤ (1 + 1 / (η * Real.log 2)) * (1 + a * (η * Real.log 2)) := by
      have : (1 + 1 / (η * Real.log 2)) * (1 + a * (η * Real.log 2)) =
          1 + a * (η * Real.log 2) + 1 / (η * Real.log 2) + a := by
        field_simp
        ring
      rw [this]
      have : 0 ≤ 1 / (η * Real.log 2) := by positivity
      nlinarith [mul_nonneg ha hl.le]
    calc (a : ℝ) + 1 ≤ _ := h3
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (h1.trans h2)
        positivity
  · push Not at h
    have hP : (2 : ℝ) ^ (1 / η) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast h)
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ η := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / η)) ^ η := by
              rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one]
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hP hη.le
    have h3 : (1 : ℝ) + a * 1 ≤ (1 + 1) ^ a := one_add_mul_le_pow (by norm_num) a
    calc (a : ℝ) + 1 ≤ 2 ^ a := by norm_num at h3; linarith
      _ ≤ ((p : ℝ) ^ η) ^ a := pow_le_pow_left₀ (by norm_num) h2 _
      _ = 1 * _ := (one_mul _).symm

theorem card_divisors_le_aux {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ η := by
  set B : ℝ := 1 + 1 / (η * Real.log 2) with hB
  set P0 : ℕ := ⌈(2 : ℝ) ^ (1 / η)⌉₊
  have hB1 : 1 ≤ B := by
    have : 0 ≤ 1 / (η * Real.log 2) := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
    linarith
  refine ⟨B ^ P0, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  set s := n.primeFactors
  set f : ℕ → ℝ := fun p => if p < P0 then B else 1
  have hd : (n.divisors.card : ℝ) = ∏ p ∈ s, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]; push_cast; rfl
  have hn : (n : ℝ) ^ η = ∏ p ∈ s, (((p : ℝ) ^ η) ^ (n.factorization p)) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  have hf : ∏ p ∈ s, f p ≤ B ^ P0 := by
    simp only [f]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    apply pow_le_pow_right₀ hB1
    calc (s.filter (· < P0)).card ≤ (Finset.range P0).card := by
          apply Finset.card_le_card
          intro x hx; simp only [Finset.mem_filter] at hx; simpa using hx.2
      _ = P0 := Finset.card_range _
  rw [hd, hn]
  calc ∏ p ∈ s, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ s, (f p * ((p : ℝ) ^ η) ^ (n.factorization p)) := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro p hp
        exact divisor_local hη p _ (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (∏ p ∈ s, f p) * ∏ p ∈ s, ((p : ℝ) ^ η) ^ (n.factorization p) :=
        Finset.prod_mul_distrib
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right hf
        exact Finset.prod_nonneg fun _ _ => by positivity

/-!
# Part C of the `S₂` Blueprint: the divisor bound, and Hölder + Heath-Brown

Helpers live in `S2PartC0.lean` (same namespace).
-/

end GuthMaynard.S2.PartC
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part C: the divisor bound, and Hölder + Heath-Brown -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartC
open Complex MeasureTheory FourierTransform
/-! ### Combinatorics of `(dpoly c M t)^k` -/
/-- The `k`-tuples of integers in `[1, M]`. -/
def tup (k M : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun _ => Finset.Icc 1 M

/-- The product of a tuple. -/
def tprod {k : ℕ} (f : Fin k → ℕ) : ℕ := ∏ i, f i

/-- The coefficient attached to a tuple. -/
noncomputable def tcoef (c : ℕ → ℂ) {k : ℕ} (f : Fin k → ℕ) : ℂ := ∏ i, c (f i)

/-- The coefficient of `n^{it}` in the `j`-th dyadic block of `(dpoly c M t)^k`. -/
noncomputable def bcoef (c : ℕ → ℂ) (k M j n : ℕ) : ℂ :=
  ∑ f ∈ (tup k M).filter (fun f => Nat.log 2 (tprod f) = j ∧ tprod f = n), tcoef c f

theorem prod_natCast_cpow {ι : Type*} (s : Finset ι) (n : ι → ℕ) (z : ℂ) :
    ∏ i ∈ s, ((n i : ℕ) : ℂ) ^ z = ((∏ i ∈ s, n i : ℕ) : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]

theorem tprod_pos {k M : ℕ} {f : Fin k → ℕ} (hf : f ∈ tup k M) : 0 < tprod f := by
  unfold tprod
  apply Finset.prod_pos
  intro i _
  have := Fintype.mem_piFinset.mp hf i
  simp only [Finset.mem_Icc] at this
  omega

theorem tprod_le {k M : ℕ} {f : Fin k → ℕ} (hf : f ∈ tup k M) : tprod f ≤ M ^ k := by
  unfold tprod
  have := Finset.prod_le_pow_card (Finset.univ : Finset (Fin k)) f M (fun i _ => by
    have := Fintype.mem_piFinset.mp hf i
    simp only [Finset.mem_Icc] at this
    exact this.2)
  simpa using this

theorem dpoly_pow (c : ℕ → ℂ) (M k : ℕ) (t : ℝ) :
    dpoly c M t ^ k = ∑ f ∈ tup k M, tcoef c f * ((tprod f : ℕ) : ℂ) ^ ((t : ℂ) * I) := by
  unfold dpoly tup
  rw [← Fin.prod_const k, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib, prod_natCast_cpow]
  rfl

theorem block_eq (c : ℕ → ℂ) (k M j : ℕ) (z : ℂ) :
    ∑ n ∈ Finset.Icc (2 ^ j) (2 * 2 ^ j), bcoef c k M j n * (n : ℂ) ^ z =
      ∑ f ∈ (tup k M).filter (fun f => Nat.log 2 (tprod f) = j),
        tcoef c f * ((tprod f : ℕ) : ℂ) ^ z := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := (tup k M).filter (fun f => Nat.log 2 (tprod f) = j))
    (t := Finset.Icc (2 ^ j) (2 * 2 ^ j)) (g := tprod)]
  · refine Finset.sum_congr rfl fun n _ => ?_
    unfold bcoef
    rw [Finset.sum_mul, Finset.filter_filter]
    refine Finset.sum_congr rfl fun f hf => ?_
    simp only [Finset.mem_filter] at hf
    rw [hf.2.2]
  · intro f hf
    simp only [Finset.mem_filter] at hf
    have h0 : tprod f ≠ 0 := (tprod_pos hf.1).ne'
    simp only [Finset.mem_Icc]
    constructor
    · rw [← hf.2]; exact Nat.pow_log_le_self 2 h0
    · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (tprod f)
      rw [hf.2, pow_succ] at this
      omega

theorem dpoly_pow_blocks (c : ℕ → ℂ) (M : ℕ) (k : ℕ) (t : ℝ) :
    dpoly c M t ^ k = ∑ j ∈ Finset.range (Nat.log 2 (M ^ k) + 1),
      ∑ n ∈ Finset.Icc (2 ^ j) (2 * 2 ^ j), bcoef c k M j n * (n : ℂ) ^ ((t : ℂ) * I) := by
  rw [dpoly_pow]
  simp_rw [block_eq]
  rw [Finset.sum_fiberwise_of_maps_to]
  intro f hf
  simp only [Finset.mem_range]
  exact Nat.lt_succ_of_le (Nat.log_mono_right (tprod_le hf))

theorem norm_bcoef_le (c : ℕ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) (k M j n : ℕ) :
    ‖bcoef c k M j n‖ ≤
      ((((tup k M).filter (fun f => Nat.log 2 (tprod f) = j ∧ tprod f = n)).card : ℕ) : ℝ) := by
  unfold bcoef
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun f _ => ?_
  unfold tcoef
  rw [norm_prod]
  push_cast
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hc _)

theorem card_fiber_le (k M j n : ℕ) :
    ((tup k M).filter (fun f => Nat.log 2 (tprod f) = j ∧ tprod f = n)).card ≤
      n.divisors.card ^ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · apply le_of_eq_of_le (b := 0) _ (Nat.zero_le _)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f hf h
    exact (tprod_pos hf).ne' h.2
  · calc _ ≤ (Fintype.piFinset fun _ : Fin k => n.divisors).card := by
          apply Finset.card_le_card
          intro f hf
          simp only [Finset.mem_filter] at hf
          rw [Fintype.mem_piFinset]
          intro i
          rw [Nat.mem_divisors]
          refine ⟨?_, hn.ne'⟩
          rw [← hf.2.2]
          exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      _ = _ := by simp

theorem fiber_nonempty_le (k M j n : ℕ)
    (h : ((tup k M).filter (fun f => Nat.log 2 (tprod f) = j ∧ tprod f = n)).Nonempty) :
    1 ≤ n ∧ n ≤ M ^ k := by
  obtain ⟨f, hf⟩ := h
  simp only [Finset.mem_filter] at hf
  rw [← hf.2.2]
  exact ⟨tprod_pos hf.1, tprod_le hf.1⟩

/-! ### Analytic helpers -/
theorem log_count (k : ℕ) {s : ℝ} (hs : 0 < s) : ∃ c1 : ℝ, 0 ≤ c1 ∧ ∀ T : ℝ, 1 ≤ T → ∀ M : ℕ,
    1 ≤ M → (M : ℝ) ≤ T ^ 2 → (((Nat.log 2 (M ^ k) + 1 : ℕ)) : ℝ) ≤ c1 * T ^ s := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * k / (Real.log 2 * s) + 1, by positivity, fun T hT M hM hMT => ?_⟩
  set ℓ := Nat.log 2 (M ^ k)
  have hMk : M ^ k ≠ 0 := pow_ne_zero _ (by omega)
  have h1 : ((2 : ℝ) ^ ℓ) ≤ (M : ℝ) ^ k := by exact_mod_cast Nat.pow_log_le_self 2 hMk
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : (ℓ : ℝ) * Real.log 2 ≤ k * Real.log M := by
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow, Real.log_pow] at this
  have h3 : Real.log M ≤ 2 * Real.log T := by
    have := Real.log_le_log hMpos hMT
    rwa [Real.log_pow] at this
  have h4 : Real.log T ≤ T ^ s / s := Real.log_le_rpow_div (by linarith) hs
  have hTs : 1 ≤ T ^ s := Real.one_le_rpow hT hs.le
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have h5 : (ℓ : ℝ) ≤ 2 * k / (Real.log 2 * s) * T ^ s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : (k : ℝ) * Real.log M ≤ k * (2 * (T ^ s / s)) := by
      apply mul_le_mul_of_nonneg_left _ hk; linarith
    have e : (k : ℝ) * (2 * (T ^ s / s)) * s = 2 * k * T ^ s := by field_simp
    nlinarith
  push_cast
  nlinarith

theorem holder_pairs (W : Finset ℝ) (F : ℝ → ℝ → ℝ) (hF : ∀ x y, 0 ≤ F x y) (K : ℕ) :
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, F t₁ t₂) ^ (K + 1) ≤
      ((W.card : ℝ) ^ 2) ^ K * ∑ t₁ ∈ W, ∑ t₂ ∈ W, F t₁ t₂ ^ (K + 1) := by
  have := pow_sum_le_card_mul_sum_pow (s := W ×ˢ W) (f := fun p => F p.1 p.2)
    (fun p _ => hF _ _) K
  rw [Finset.sum_product, Finset.sum_product, Finset.card_product] at this
  simpa [sq] using this

theorem sum_sq_le_card_mul {ι : Type*} (s : Finset ι) (Y : ι → ℂ) :
    ‖∑ j ∈ s, Y j‖ ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖Y j‖ ^ 2 := by
  calc ‖∑ j ∈ s, Y j‖ ^ 2 ≤ (∑ j ∈ s, ‖Y j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

/-- The sum of `2k`-th powers, after the dyadic splitting, given a bound on each block. -/
theorem sum_pow_le (W : Finset ℝ) (c : ℕ → ℂ) (M k : ℕ) (B : ℝ)
    (hB : ∀ j ∈ Finset.range (Nat.log 2 (M ^ k) + 1), ∑ t₁ ∈ W, ∑ t₂ ∈ W,
      ‖∑ n ∈ Finset.Icc (2 ^ j) (2 * 2 ^ j),
        bcoef c k M j n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I)‖ ^ 2 ≤ B) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, (‖dpoly c M (t₁ - t₂)‖ ^ 2) ^ k ≤
      (((Nat.log 2 (M ^ k) + 1 : ℕ)) : ℝ) * ((((Nat.log 2 (M ^ k) + 1 : ℕ)) : ℝ) * B) := by
  set L := Nat.log 2 (M ^ k) + 1
  have e : ∀ t₁ t₂ : ℝ, (‖dpoly c M (t₁ - t₂)‖ ^ 2) ^ k = ‖dpoly c M (t₁ - t₂) ^ k‖ ^ 2 := by
    intro t₁ t₂; rw [norm_pow, ← pow_mul, ← pow_mul, mul_comm]
  simp_rw [e, dpoly_pow_blocks c M k]
  calc _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, (L : ℝ) * ∑ j ∈ Finset.range L,
          ‖∑ n ∈ Finset.Icc (2 ^ j) (2 * 2 ^ j),
            bcoef c k M j n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I)‖ ^ 2 := by
        gcongr with t₁ _ t₂ _
        simpa using sum_sq_le_card_mul (Finset.range L) _
    _ = (L : ℝ) * ∑ j ∈ Finset.range L, ∑ t₁ ∈ W, ∑ t₂ ∈ W,
          ‖∑ n ∈ Finset.Icc (2 ^ j) (2 * 2 ^ j),
            bcoef c k M j n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I)‖ ^ 2 := by
        simp_rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_congr rfl fun t₁ _ => Finset.sum_comm]
        exact Finset.sum_comm
    _ ≤ (L : ℝ) * ∑ j ∈ Finset.range L, B := by
        gcongr with j hj
        exact hB j hj
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Exponent bookkeeping -/
theorem expo_two (Wc Mr : ℝ) (hW : 0 < Wc) (K : ℕ) :
    (Mr ^ 2 * Wc ^ (2 - 1 / ((K + 1 : ℕ) : ℝ))) ^ (K + 1) = (Wc ^ 2) ^ K * (Wc * Mr ^ (2 * (K + 1))) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hW.le]
  have e : (2 - 1 / ((K + 1 : ℕ) : ℝ)) * ((K + 1 : ℕ) : ℝ) = ((2 * K + 1 : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e, Real.rpow_natCast]
  ring

theorem expo_three (Wc Mr T : ℝ) (hW : 0 < Wc) (hT : 0 ≤ T) (K : ℕ) :
    (Wc ^ (2 - 3 / (4 * ((K + 1 : ℕ) : ℝ))) * T ^ (1 / (2 * ((K + 1 : ℕ) : ℝ))) * Mr) ^ (K + 1) =
      (Wc ^ 2) ^ K * (Wc ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * Mr ^ (K + 1)) := by
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hW.le, ← Real.rpow_mul_natCast hT]
  have e1 : (2 - 3 / (4 * ((K + 1 : ℕ) : ℝ))) * ((K + 1 : ℕ) : ℝ) = ((2 * K : ℕ) : ℝ) + 5 / 4 := by
    push_cast; field_simp; ring
  have e2 : 1 / (2 * ((K + 1 : ℕ) : ℝ)) * ((K + 1 : ℕ) : ℝ) = 1 / 2 := by
    push_cast; field_simp
  rw [e1, e2, Real.rpow_add hW, Real.rpow_natCast]
  ring

theorem lv_holder (k : ℕ) (hk : 1 ≤ k) : ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
    ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ m, ‖c m‖ ≤ 1) →
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖dpoly c M (t₁ - t₂)‖ ^ 2 ≤
        C * T ^ δ * ((W.card : ℝ) ^ 2 * M + (M : ℝ) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) * M) := by
  intro δ hδ
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  set k := K + 1 with hkdef
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  obtain ⟨δH, hδH, T1, hHB⟩ :=
    GuthMaynard.heath_brown_large_values ((k : ℝ) * δ / 2) (by positivity)
  set η : ℝ := δH / (4 * (k : ℝ) ^ 2) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨Cd, hCd⟩ := card_divisors_le_aux hη
  set Cd' : ℝ := max Cd 1
  have hCd'1 : 1 ≤ Cd' := le_max_right _ _
  obtain ⟨c1, hc1, hL⟩ := log_count k (s := (k : ℝ) * δ / 4) (by positivity)
  refine ⟨max 1 (c1 ^ 2), max (max T1 1) ((Cd' ^ k) ^ (2 / δH)), ?_⟩
  intro T hT W a hW hWa M hM hMT c hc
  have hTT1 : T1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : 0 < T := by linarith
  have hTC : Cd' ^ k ≤ T ^ (δH / 2) := by
    have h1 : (Cd' ^ k) ^ (2 / δH) ≤ T := le_trans (le_max_right _ _) hT
    calc Cd' ^ k = ((Cd' ^ k) ^ (2 / δH)) ^ (δH / 2) := by
            rw [← Real.rpow_mul (by positivity)]
            have : 2 / δH * (δH / 2) = 1 := by field_simp
            rw [this, Real.rpow_one]
      _ ≤ T ^ (δH / 2) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  -- the coefficients of the dyadic blocks of `(dpoly)^k`
  have hcoef : ∀ j n, ‖bcoef c k M j n‖ ≤ T ^ δH := by
    intro j n
    refine (norm_bcoef_le c hc k M j n).trans ?_
    rcases Finset.eq_empty_or_nonempty
      ((tup k M).filter (fun f => Nat.log 2 (tprod f) = j ∧ tprod f = n)) with h | h
    · rw [h]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
    · obtain ⟨hn1, hnM⟩ := fiber_nonempty_le k M j n h
      have hnT : (n : ℝ) ≤ T ^ (((2 * k : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast, pow_mul]
        calc (n : ℝ) ≤ (M : ℝ) ^ k := by exact_mod_cast hnM
          _ ≤ (T ^ 2) ^ k := pow_le_pow_left₀ (by positivity) hMT k
      have hnη : ((n : ℝ) ^ η) ^ k ≤ T ^ (δH / 2) := by
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
        calc (n : ℝ) ^ (η * k) ≤ (T ^ (((2 * k : ℕ) : ℝ))) ^ (η * k) :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hnT (by positivity)
          _ = T ^ (δH / 2) := by
              rw [← Real.rpow_mul hT0.le]
              congr 1
              rw [hηdef]; push_cast; field_simp; ring
      calc ((((tup k M).filter (fun f => Nat.log 2 (tprod f) = j ∧ tprod f = n)).card : ℕ) : ℝ)
          ≤ ((n.divisors.card ^ k : ℕ) : ℝ) := by exact_mod_cast card_fiber_le k M j n
        _ = (n.divisors.card : ℝ) ^ k := by push_cast; rfl
        _ ≤ (Cd' * (n : ℝ) ^ η) ^ k := by
            apply pow_le_pow_left₀ (Nat.cast_nonneg _)
            refine (hCd n hn1).trans ?_
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = Cd' ^ k * ((n : ℝ) ^ η) ^ k := mul_pow _ _ _
        _ ≤ T ^ (δH / 2) * T ^ (δH / 2) := by
            apply mul_le_mul hTC hnη (by positivity) (by positivity)
        _ = T ^ δH := by rw [← Real.rpow_add hT0]; ring_nf
  -- notation
  set Wc : ℝ := (W.card : ℝ) with hWc
  set Mr : ℝ := (M : ℝ) with hMr
  have hMr0 : 0 ≤ Mr := Nat.cast_nonneg _
  set L : ℕ := Nat.log 2 (M ^ k) + 1 with hLdef
  set Q : ℝ := Wc ^ 2 * Mr ^ k + Wc * Mr ^ (2 * k) + Wc ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * Mr ^ k
    with hQ
  have hQ0 : 0 ≤ Q := by positivity
  -- Heath-Brown on each block
  have hblock : ∀ j ∈ Finset.range L, ∑ t₁ ∈ W, ∑ t₂ ∈ W,
      ‖∑ n ∈ Finset.Icc (2 ^ j) (2 * 2 ^ j),
        bcoef c k M j n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I)‖ ^ 2 ≤
        T ^ ((k : ℝ) * δ / 2) * Q := by
    intro j hj
    have hN := hHB T hTT1 (2 ^ j) (Nat.one_le_two_pow) (bcoef c k M j) (hcoef j) W a hW hWa
    refine hN.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hjM : ((2 ^ j : ℕ) : ℝ) ≤ Mr ^ k := by
      have : 2 ^ j ≤ M ^ k := by
        refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_)
          (Nat.pow_log_le_self 2 (pow_ne_zero _ (by omega)))
        simp only [Finset.mem_range, hLdef] at hj
        omega
      rw [hMr]; exact_mod_cast this
    have h0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hQ, pow_mul']
    gcongr
  have hS := sum_pow_le W c M k _ hblock
  -- the count of blocks
  have hLb : (L : ℝ) ≤ c1 * T ^ ((k : ℝ) * δ / 4) := hL T hT1 M hM hMT
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hS' : ∑ t₁ ∈ W, ∑ t₂ ∈ W, (‖dpoly c M (t₁ - t₂)‖ ^ 2) ^ k ≤
      c1 ^ 2 * T ^ ((k : ℝ) * δ) * Q := by
    refine hS.trans ?_
    have hTs : 0 ≤ T ^ ((k : ℝ) * δ / 4) := by positivity
    have e : T ^ ((k : ℝ) * δ) =
        T ^ ((k : ℝ) * δ / 4) * T ^ ((k : ℝ) * δ / 4) * T ^ ((k : ℝ) * δ / 2) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]; ring_nf
    rw [e]
    have hLL : (L : ℝ) * L ≤ (c1 * T ^ ((k : ℝ) * δ / 4)) * (c1 * T ^ ((k : ℝ) * δ / 4)) :=
      mul_le_mul hLb hLb hL0 (by positivity)
    have hB0 : 0 ≤ T ^ ((k : ℝ) * δ / 2) * Q := by positivity
    calc (L : ℝ) * ((L : ℝ) * (T ^ ((k : ℝ) * δ / 2) * Q))
        = ((L : ℝ) * L) * (T ^ ((k : ℝ) * δ / 2) * Q) := by ring
      _ ≤ (c1 * T ^ ((k : ℝ) * δ / 4)) * (c1 * T ^ ((k : ℝ) * δ / 4)) *
          (T ^ ((k : ℝ) * δ / 2) * Q) := mul_le_mul_of_nonneg_right hLL hB0
      _ = _ := by ring
  -- empty `W`
  rcases Nat.eq_zero_or_pos W.card with hW0 | hWpos
  · rw [Finset.card_eq_zero.mp hW0]
    simp only [Finset.sum_empty]
    have : (0 : ℝ) ≤ ((∅ : Finset ℝ).card : ℝ) := Nat.cast_nonneg _
    positivity
  have hWc0 : 0 < Wc := by rw [hWc]; exact_mod_cast hWpos
  -- the `k`-th power comparison
  set X := ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖dpoly c M (t₁ - t₂)‖ ^ 2 with hX
  set A : ℝ := Wc ^ 2 * Mr
  set B : ℝ := Mr ^ 2 * Wc ^ (2 - 1 / (k : ℝ))
  set D : ℝ := Wc ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) * Mr
  set C : ℝ := max 1 (c1 ^ 2)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hX0 : 0 ≤ X := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hid : (Wc ^ 2) ^ K * Q = A ^ k + B ^ k + D ^ k := by
    rw [hkdef, expo_two Wc Mr hWc0 K, expo_three Wc Mr T hWc0 hT0.le K, hQ]
    simp only [A, mul_pow]
    ring
  have hXk : X ^ k ≤ (C * T ^ δ * (A + B + D)) ^ k := by
    calc X ^ k ≤ (Wc ^ 2) ^ K * ∑ t₁ ∈ W, ∑ t₂ ∈ W, (‖dpoly c M (t₁ - t₂)‖ ^ 2) ^ k :=
          holder_pairs W (fun t₁ t₂ => ‖dpoly c M (t₁ - t₂)‖ ^ 2) (fun _ _ => by positivity) K
      _ ≤ (Wc ^ 2) ^ K * (c1 ^ 2 * T ^ ((k : ℝ) * δ) * Q) :=
          mul_le_mul_of_nonneg_left hS' (by positivity)
      _ = c1 ^ 2 * T ^ ((k : ℝ) * δ) * (A ^ k + B ^ k + D ^ k) := by rw [← hid]; ring
      _ ≤ C ^ k * (T ^ δ) ^ k * (A + B + D) ^ k := by
          have h1 : c1 ^ 2 ≤ C ^ k :=
            (le_max_right _ _).trans (le_self_pow₀ hC1 (by omega))
          have h2 : T ^ ((k : ℝ) * δ) = (T ^ δ) ^ k := by
            rw [mul_comm, Real.rpow_mul_natCast hT0.le]
          have h3 : A ^ k + B ^ k + D ^ k ≤ (A + B + D) ^ k :=
            ((add_le_add_left (pow_add_pow_le hA0 hB0 (by omega)) _).trans
              (pow_add_pow_le (by positivity) hD0 (by omega)))
          rw [h2]
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3
            (by positivity) (by positivity)
      _ = _ := by rw [mul_pow, mul_pow]
  exact (pow_le_pow_iff_left₀ hX0 (by positivity) (by omega)).mp hXk

end GuthMaynard.S2.PartC
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
alias lv_holder := GuthMaynard.S2.PartC.lv_holder

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartE2
open Complex MeasureTheory FourierTransform
/-! Helpers for Part E2 (`sum_Asum_sq_le`). -/
/-! ### `Gw` and its Fourier transform (same proofs as Part B / E1) -/

/-! ### Dirichlet polynomials -/

/-! ### Integrals against a nonnegative integrable weight -/

/-! ### Counting shells -/
theorem log_count {η : ℝ} (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) + 1 ≤ C * T ^ η := by
  have hb : 1 < (2 : ℝ) ^ η := Real.one_lt_rpow (by norm_num) hη
  refine ⟨1 / ((2 : ℝ) ^ η - 1) + 1, by
    have : 0 < (2 : ℝ) ^ η - 1 := by linarith
    positivity, fun T hT => ?_⟩
  have hfl : ⌊T⌋₊ ≠ 0 := (Nat.floor_pos.2 hT).ne'
  have h2m : ((2 : ℝ) ^ (Nat.log 2 ⌊T⌋₊)) ≤ T := by
    have := Nat.pow_log_le_self 2 hfl
    calc ((2 : ℝ) ^ (Nat.log 2 ⌊T⌋₊)) = ((2 ^ (Nat.log 2 ⌊T⌋₊) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ⌊T⌋₊ := by exact_mod_cast this
      _ ≤ T := Nat.floor_le (by linarith)
  have hbern : 1 + ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) * ((2 : ℝ) ^ η - 1) ≤
      ((2 : ℝ) ^ η) ^ (Nat.log 2 ⌊T⌋₊) := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ (2 : ℝ) ^ η - 1 by linarith) (Nat.log 2 ⌊T⌋₊)
    simpa using this
  have hbm : ((2 : ℝ) ^ η) ^ (Nat.log 2 ⌊T⌋₊) ≤ T ^ η := by
    calc ((2 : ℝ) ^ η) ^ (Nat.log 2 ⌊T⌋₊) = ((2 : ℝ) ^ (Nat.log 2 ⌊T⌋₊)) ^ η := by
          rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
      _ ≤ T ^ η := Real.rpow_le_rpow (by positivity) h2m hη.le
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hm : ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) ≤ T ^ η / ((2 : ℝ) ^ η - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  calc ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) + 1 ≤ T ^ η / ((2 : ℝ) ^ η - 1) + T ^ η := by linarith
    _ = (1 / ((2 : ℝ) ^ η - 1) + 1) * T ^ η := by ring

/-! ### Arithmetic -/

/-! ### Shells: the cut-off `M_j`, the per-pair bound -/

/-! ### The core estimate, with all constants given -/

/-! Part E2: `sum_Asum_sq_le`, from `norm_Asum_le`, `norm_sum_hHat_sq_le`, `lv_holder`
(Blueprint stubs) and the helpers of `S2PartE2a`. -/

end GuthMaynard.S2.PartE2
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartM
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartM
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Main -/

end GuthMaynard.S2
end


section
open GuthMaynard
theorem solution (k : ℕ) (hk : 1 ≤ k) : ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
    ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ m, ‖c m‖ ≤ 1) →
      ∑ t₁ ∈ W, ∑ t₂ ∈ W,
          ‖∑ m ∈ Finset.Icc 1 M, c m * (m : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
        C * T ^ δ * ((W.card : ℝ) ^ 2 * M + (M : ℝ) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) * M) := GuthMaynard.S2.lv_holder k hk
end
