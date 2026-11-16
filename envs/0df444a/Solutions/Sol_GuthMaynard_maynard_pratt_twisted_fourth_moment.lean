-- Prove2me | solution 1 for GuthMaynard.maynard_pratt_twisted_fourth_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:24:24.725522+00:00
-- url     : https://prove2.me/submissions/b76550d3-f082-48c3-872d-bbd81adbbb0a

import Mathlib
import Theorems.Thm_GuthMaynard_twisted_fourth_moment_dyadic_gaussian
import Theorems.Thm_RSSeam_rs_Z_C0_seam
import Theorems.Thm_GuthMaynard_norm_window_sum_le_perron
import Theorems.Thm_ArtinPrimitiveRoots_dirichlet_mean_value

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
/-!
# Twisted fourth moment (Maynard–Pratt, Lemma 24 input): blueprint

Target: `GuthMaynard.maynard_pratt_twisted_fourth_moment`.
Mathematics: `PLAN.md` and `BRIEF.md` in
`~/claude/guth-maynard-mission/proofs/maynard_pratt_twisted_fourth_moment/`.
Every `sorry` below is a stub proved by a Part; the assembly at the end is proved from the stubs.
-/
/-! ## Definitions -/
/-- The mollifier length `y = ⌊2 T^{1/100}⌋`. -/
def yT (T : ℝ) : ℕ := ⌊2 * T ^ (1 / 100 : ℝ)⌋₊

/-- `L = y²`, the length of `M²`. -/
def Lof (T : ℝ) : ℕ := yT T ^ 2

/-- The mollifier `M(s) = ∑_{m ≤ y} μ(m) m^{-s}`. -/
def Mol (T : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (yT T), (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)

/-- The coefficients of `M²`: `β(ℓ) = ∑_{de = ℓ, d ≤ y, e ≤ y} μ(d) μ(e)`. -/
def beta (y ℓ : ℕ) : ℤ :=
  ∑ d ∈ ℓ.divisors.filter (fun d => d ≤ y ∧ ℓ / d ≤ y),
    ArithmeticFunction.moebius d * ArithmeticFunction.moebius (ℓ / d)

/-- The divisor function as a real number. -/
def dv (n : ℕ) : ℝ := (n.divisors.card : ℝ)

/-- The dyadic partition function, taken from the published statement. -/
def V : ℝ → ℝ := Classical.choose GuthMaynard.twisted_fourth_moment_dyadic_gaussian

/-- The smooth dyadic block `Q_A(v) = ∑_ν V(ν/A) ν^{-1/2 + iv}`. -/
def Q (A : ℕ) (v : ℝ) : ℂ :=
  ∑ ν ∈ Finset.Icc 1 (2 * A), ((V ((ν : ℝ) / A) : ℝ) : ℂ) * (ν : ℂ) ^ (-(1 / 2 : ℂ) + (v : ℂ) * Complex.I)

/-- The width of the Gaussian windows. -/
def Delta (T : ℝ) : ℝ := T / Real.log T

/-- The Gaussian-windowed moment of one smooth dyadic block. -/
def IG (T : ℝ) (A : ℕ) (t₀ u : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-((t - t₀) / Delta T) ^ 2) * ‖Q A (u - t)‖ ^ 4 *
    ‖Mol T (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4

/-- Proposition G. -/
def PropG : Prop :=
  ∃ C A₀ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (j : ℕ) (t₀ u : ℝ), (2 : ℝ) ^ j ≤ 4 * Real.sqrt T →
    T / 2 ≤ t₀ → t₀ ≤ 4 * T → |u| ≤ 2 * T ^ (3 / 4 : ℝ) →
    IG T (2 ^ j) t₀ u ≤ C * Delta T * Real.log T ^ A₀

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartP
open Finset
theorem V_nonneg (x : ℝ) : 0 ≤ V x := ((Classical.choose_spec GuthMaynard.twisted_fourth_moment_dyadic_gaussian).1 x).1

end GuthMaynard.Twisted.PartP
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
/-! ## Part S: the partition function, Abel summation, reindexing -/
alias V_nonneg := GuthMaynard.Twisted.PartP.V_nonneg

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartP
open Finset
theorem V_le_one (x : ℝ) : V x ≤ 1 := ((Classical.choose_spec GuthMaynard.twisted_fourth_moment_dyadic_gaussian).1 x).2

end GuthMaynard.Twisted.PartP
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
alias V_le_one := GuthMaynard.Twisted.PartP.V_le_one

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartP
open Finset
theorem V_eq_zero_of_le (x : ℝ) (hx : x ≤ 1 / 2) : V x = 0 := (Classical.choose_spec GuthMaynard.twisted_fourth_moment_dyadic_gaussian).2.1 x hx

end GuthMaynard.Twisted.PartP
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
alias V_eq_zero_of_le := GuthMaynard.Twisted.PartP.V_eq_zero_of_le

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartP
open Finset
theorem V_eq_zero_of_ge (x : ℝ) (hx : 2 ≤ x) : V x = 0 := (Classical.choose_spec GuthMaynard.twisted_fourth_moment_dyadic_gaussian).2.2.1 x hx

end GuthMaynard.Twisted.PartP
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
alias V_eq_zero_of_ge := GuthMaynard.Twisted.PartP.V_eq_zero_of_ge

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartP
open Finset
theorem V_partition (J : ℕ) (x : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ 2 ^ J) :
    ∑ j ∈ Finset.range (J + 1), V (x / 2 ^ j) = 1 := (Classical.choose_spec GuthMaynard.twisted_fourth_moment_dyadic_gaussian).2.2.2.1 J x h1 h2

end GuthMaynard.Twisted.PartP
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
alias V_partition := GuthMaynard.Twisted.PartP.V_partition

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartX
open Finset Complex
noncomputable section
/-!
# Twisted fourth moment, Part X: the expansion

Proves the Blueprint stubs `abs_beta_le`, `Mol_sq`, `expansion`.
-/
/-! ## `abs_beta_le` -/
theorem abs_beta_le (y ℓ : ℕ) : |((beta y ℓ : ℤ) : ℝ)| ≤ dv ℓ := by
  unfold beta dv
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ d ∈ ℓ.divisors.filter (fun d => d ≤ y ∧ ℓ / d ≤ y),
      |((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius (ℓ / d) : ℤ) : ℝ)|
        ≤ 1 := by
    intro d _
    rw [abs_mul]
    have ha : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hb : |((ArithmeticFunction.moebius (ℓ / d) : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := ℓ / d)
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul ha hb (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_filter_le _ _

end
end GuthMaynard.Twisted.PartX
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
/-! ## Part X: the expansion -/
alias abs_beta_le := GuthMaynard.Twisted.PartX.abs_beta_le

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartX
open Finset Complex
noncomputable section
/-! ## `Mol_sq` -/
theorem beta_eq (y ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    beta y ℓ = ∑ d ∈ Finset.Icc 1 y, ∑ e ∈ Finset.Icc 1 y,
      if d * e = ℓ then ArithmeticFunction.moebius d * ArithmeticFunction.moebius e else 0 := by
  have hinner : ∀ d ∈ Finset.Icc 1 y, (∑ e ∈ Finset.Icc 1 y,
      if d * e = ℓ then ArithmeticFunction.moebius d * ArithmeticFunction.moebius e else 0) =
      if d ∣ ℓ ∧ ℓ / d ≤ y then
        ArithmeticFunction.moebius d * ArithmeticFunction.moebius (ℓ / d) else 0 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    by_cases h : d ∣ ℓ ∧ ℓ / d ≤ y
    · rw [if_pos h]
      obtain ⟨hdvd, hle⟩ := h
      have hq : d * (ℓ / d) = ℓ := Nat.mul_div_cancel' hdvd
      have hq1 : 1 ≤ ℓ / d := by
        rcases Nat.eq_zero_or_pos (ℓ / d) with h0 | h0
        · rw [h0] at hq; omega
        · exact h0
      rw [Finset.sum_eq_single (ℓ / d)]
      · rw [if_pos hq]
      · intro e _ hne
        rw [if_neg]
        intro he
        apply hne
        rw [← he, Nat.mul_div_cancel_left _ (by omega)]
      · intro hn
        exact absurd (Finset.mem_Icc.mpr ⟨hq1, hle⟩) hn
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun e he => ?_
      rw [if_neg]
      intro hde
      apply h
      refine ⟨⟨e, hde.symm⟩, ?_⟩
      rw [← hde, Nat.mul_div_cancel_left _ (by omega)]
      exact (Finset.mem_Icc.mp he).2
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  unfold beta
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hdy, hq⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), hdy⟩, hdvd, hq⟩
  · rintro ⟨⟨_, hdy⟩, hdvd, hq⟩
    exact ⟨⟨hdvd, by omega⟩, hdy, hq⟩

/-! ## The Gaussian integral -/
theorem Mol_sq (T : ℝ) (s : ℂ) :
    Mol T s ^ 2 = ∑ ℓ ∈ Finset.Icc 1 (Lof T), ((beta (yT T) ℓ : ℤ) : ℂ) * (ℓ : ℂ) ^ (-s) := by
  have hR : ∀ ℓ ∈ Finset.Icc 1 (Lof T), ((beta (yT T) ℓ : ℤ) : ℂ) * (ℓ : ℂ) ^ (-s) =
      ∑ d ∈ Finset.Icc 1 (yT T), ∑ e ∈ Finset.Icc 1 (yT T),
        if d * e = ℓ then (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.moebius e : ℂ) *
          ((d * e : ℕ) : ℂ) ^ (-s) else 0 := by
    intro ℓ hℓ
    rw [beta_eq _ _ (Finset.mem_Icc.mp hℓ).1]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : d * e = ℓ
    · rw [if_pos h, if_pos h, ← h]; push_cast; ring
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl hR, Finset.sum_comm]
  rw [sq, Mol, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.sum_ite_eq]
  have hmem : d * e ∈ Finset.Icc 1 (Lof T) := by
    rw [Finset.mem_Icc] at hd he ⊢
    refine ⟨Nat.mul_pos hd.1 he.1, ?_⟩
    unfold Lof
    rw [sq]
    exact Nat.mul_le_mul hd.2 he.2
  rw [if_pos hmem, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

end
end GuthMaynard.Twisted.PartX
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
alias Mol_sq := GuthMaynard.Twisted.PartX.Mol_sq

/-! ## Part B: counting on the modular hyperbola with a general residue -/

/-! ## Part W: the variation of `ω_h` -/

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartM
open Finset
open scoped Pointwise
/-!
# Twisted fourth moment, Part M: arithmetic sums
-/
theorem dv_nonneg (n : ℕ) : 0 ≤ dv n := by unfold dv; positivity

theorem dv_mul_le (m n : ℕ) : dv (m * n) ≤ dv m * dv n := by
  unfold dv
  rw [Nat.divisors_mul]
  exact_mod_cast Finset.card_mul_le

theorem sum_inv_le (X : ℕ) : ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / n ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  have e : ((harmonic X : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / n := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  rw [← e]; exact h

theorem sum_div_pairs_le (X : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ a b, 0 ≤ F a b) :
    ∑ n ∈ Finset.Icc 1 X, ∑ a ∈ n.divisors, F a (n / a) ≤
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X, F a b := by
  calc ∑ n ∈ Finset.Icc 1 X, ∑ a ∈ n.divisors, F a (n / a)
      = ∑ n ∈ Finset.Icc 1 X, ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
          (if a * b = n then F a b else 0) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn' := Finset.mem_Icc.mp hn
        rw [← Nat.sum_divisorsAntidiagonal (fun a b => F a b), ← Finset.sum_product',
          ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext ⟨a, b⟩
        simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Finset.mem_product,
          Finset.mem_Icc]
        constructor
        · rintro ⟨hab, _⟩
          have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
          have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; omega)
          have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
          have h2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
          exact ⟨⟨⟨ha, by omega⟩, ⟨hb, by omega⟩⟩, hab⟩
        · rintro ⟨_, hab⟩
          exact ⟨hab, by omega⟩
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          (if a * b = n then F a b else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ ≤ _ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [Finset.sum_ite_eq]
        split_ifs
        · exact le_rfl
        · exact hF a b

/-! ## Helpers for the diagonal sum -/
theorem sum_dv_pow_div_le (k X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, dv n ^ k / n ≤ (1 + Real.log X) ^ (2 ^ k) := by
  induction k with
  | zero => simpa using sum_inv_le X
  | succ k ih =>
    have h0 : 0 ≤ ∑ n ∈ Finset.Icc 1 X, dv n ^ k / n :=
      Finset.sum_nonneg fun n _ => div_nonneg (pow_nonneg (dv_nonneg n) k) (Nat.cast_nonneg n)
    calc ∑ n ∈ Finset.Icc 1 X, dv n ^ (k + 1) / n
        = ∑ n ∈ Finset.Icc 1 X, ∑ a ∈ n.divisors,
            dv (a * (n / a)) ^ k / ((a * (n / a) : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have : ∀ a ∈ n.divisors,
              dv (a * (n / a)) ^ k / ((a * (n / a) : ℕ) : ℝ) = dv n ^ k / n := by
            intro a ha; rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)]
          rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, pow_succ]
          unfold dv; ring
      _ ≤ ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X, dv (a * b) ^ k / ((a * b : ℕ) : ℝ) :=
          sum_div_pairs_le X (fun a b => dv (a * b) ^ k / ((a * b : ℕ) : ℝ))
            (fun a b => div_nonneg (pow_nonneg (dv_nonneg _) k) (Nat.cast_nonneg _))
      _ ≤ ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X, (dv a ^ k / a) * (dv b ^ k / b) := by
          refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
          rw [div_mul_div_comm, ← mul_pow]
          push_cast
          exact div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (dv_nonneg _) (dv_mul_le a b) k) (by positivity)
      _ = (∑ a ∈ Finset.Icc 1 X, dv a ^ k / a) ^ 2 := by rw [sq, Finset.sum_mul_sum]
      _ ≤ ((1 + Real.log X) ^ (2 ^ k)) ^ 2 := pow_le_pow_left₀ h0 ih 2
      _ = _ := by rw [← pow_mul, ← pow_succ]

end GuthMaynard.Twisted.PartM
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
/-! ## Part M: arithmetic sums -/
alias sum_dv_pow_div_le := GuthMaynard.Twisted.PartM.sum_dv_pow_div_le

/-! ## Part G: Gaussian replacement and Poisson summation -/

/-! ## Part H: the resonant frequencies -/

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted.PartP
open Finset
theorem propG : PropG := by
  obtain ⟨C, A₀, T₀, h⟩ := (Classical.choose_spec GuthMaynard.twisted_fourth_moment_dyadic_gaussian).2.2.2.2
  refine ⟨C, A₀, T₀, fun T hT j t₀ u h1 h2 h3 h4 => ?_⟩
  have := h T hT j t₀ u h1 h2 h3 h4
  simpa [IG, Q, Mol, yT, Delta, V] using this

end GuthMaynard.Twisted.PartP
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
/-! ## Part A: Proposition G -/
alias propG := GuthMaynard.Twisted.PartP.propG

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
namespace GuthMaynard.Twisted.PartR
noncomputable section
/-!
# Part R: the reduction of the twisted fourth moment to Proposition G
-/
/-! ## The Riemann–Siegel pointwise bound (copied from our fourth-moment proof) -/
/-- S_N(t) = Σ_{n=1}^{N} n^{-(1/2+it)}. -/
def S (N : ℕ) (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))

lemma abs_sin_ge {x : ℝ} (hx : |x| ≤ π / 2) : 2 / π * |x| ≤ |Real.sin x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx ⊢
    have := Real.mul_le_sin h hx
    exact this.trans (le_abs_self _)
  · rw [abs_of_nonpos h] at hx ⊢
    have := Real.mul_le_sin (neg_nonneg.2 h) hx
    rw [Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

lemma num_eq (p : ℝ) : Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) =
    Real.sin (2 * π * ((p - 1 / 4) * (p - 3 / 4))) := by
  rw [← Real.cos_sub_pi_div_two]
  congr 1; ring

theorem psi_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (hc : Real.cos (2 * π * p) ≠ 0) :
    |RSInt.rsPsi p| ≤ 2 := by
  unfold RSInt.rsPsi
  rw [abs_div, div_le_iff₀ (abs_pos.2 hc), num_eq]
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_four
  have hnum : |Real.sin (2 * π * ((p - 1 / 4) * (p - 3 / 4)))| ≤
      2 * π * (|p - 1 / 4| * |p - 3 / 4|) := by
    refine (Real.abs_sin_le_abs).trans ?_
    simp only [abs_mul, abs_two, abs_of_pos hpi, le_refl]
  rcases le_total p (1 / 2) with h | h
  · have hc' : Real.cos (2 * π * p) = Real.sin (2 * π * (1 / 4 - p)) := by
      rw [← Real.cos_pi_div_two_sub]; congr 1; ring
    have hx : |2 * π * (1 / 4 - p)| ≤ π / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    have hs := abs_sin_ge hx
    rw [← hc'] at hs
    have e : |2 * π * (1 / 4 - p)| = 2 * π * |p - 1 / 4| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_sub_comm]
    rw [e] at hs
    have h34 : |p - 3 / 4| ≤ 3 / 4 := by rw [abs_le]; constructor <;> linarith
    have ha := abs_nonneg (p - 1 / 4)
    have : 2 / π * (2 * π * |p - 1 / 4|) = 4 * |p - 1 / 4| := by field_simp; ring
    rw [this] at hs
    calc _ ≤ 2 * π * (|p - 1 / 4| * |p - 3 / 4|) := hnum
      _ ≤ 2 * π * (|p - 1 / 4| * (3 / 4)) := by gcongr
      _ ≤ 2 * (4 * |p - 1 / 4|) := by nlinarith
      _ ≤ _ := by linarith
  · have hc' : Real.cos (2 * π * p) = Real.sin (2 * π * (p - 3 / 4)) := by
      rw [← Real.cos_sub_pi_div_two]
      have : 2 * π * (p - 3 / 4) - π / 2 = 2 * π * p - 2 * π := by ring
      rw [this, Real.cos_sub_two_pi]
    have hx : |2 * π * (p - 3 / 4)| ≤ π / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    have hs := abs_sin_ge hx
    rw [← hc'] at hs
    have e : |2 * π * (p - 3 / 4)| = 2 * π * |p - 3 / 4| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    rw [e] at hs
    have h14 : |p - 1 / 4| ≤ 3 / 4 := by rw [abs_le]; constructor <;> linarith
    have ha := abs_nonneg (p - 3 / 4)
    have : 2 / π * (2 * π * |p - 3 / 4|) = 4 * |p - 3 / 4| := by field_simp; ring
    rw [this] at hs
    calc _ ≤ 2 * π * (|p - 1 / 4| * |p - 3 / 4|) := hnum
      _ ≤ 2 * π * ((3 / 4) * |p - 3 / 4|) := by gcongr
      _ ≤ 2 * (4 * |p - 3 / 4|) := by nlinarith
      _ ≤ _ := by linarith

lemma rsFrac_nonneg (t : ℝ) : 0 ≤ RSInt.rsFrac t := by
  unfold RSInt.rsFrac RSInt.rsNn RSInt.rsAlpha
  linarith [Nat.floor_le (Real.sqrt_nonneg (t / (2 * π)))]

lemma rsFrac_lt_one (t : ℝ) : RSInt.rsFrac t < 1 := by
  unfold RSInt.rsFrac RSInt.rsNn
  linarith [Nat.lt_floor_add_one (RSInt.rsAlpha t)]

lemma GammaR_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj]
  have h1 : -conj s / 2 = conj (-s / 2) := by simp [map_div₀, map_ofNat]
  have h2 : conj s / 2 = conj (s / 2) := by simp [map_div₀, map_ofNat]
  rw [h1, h2, Complex.cpow_conj _ _ (by simp [Complex.arg_ofReal_of_nonneg Real.pi_pos.le,
    Real.pi_ne_zero.symm])]
  simp

lemma completed_conj (s : ℂ) (h0 : s ≠ 0) (hre : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hc0 : conj s ≠ 0 := by simpa using h0
  have hre' : 0 < (conj s).re := by simpa using hre
  have e1 := riemannZeta_def_of_ne_zero h0
  have e2 := riemannZeta_def_of_ne_zero hc0
  have g1 := Gammaℝ_ne_zero_of_re_pos hre
  have g2 := Gammaℝ_ne_zero_of_re_pos hre'
  rw [eq_div_iff g1] at e1
  rw [eq_div_iff g2] at e2
  rw [← e1, ← e2, riemannZeta_conj, GammaR_conj, map_mul]

lemma completed_im_zero (t : ℝ) : (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).im = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + t * I
  have h0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [s] at this
  have hre : 0 < s.re := by simp [s]
  have hcs : conj s = 1 - s := by
    apply Complex.ext <;> simp [s]; norm_num
  have := completed_conj s h0 hre
  rw [hcs, completedRiemannZeta_one_sub] at this
  exact Complex.conj_eq_iff_im.1 this.symm

lemma term_re (φ t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (cexp (I * φ) * (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))).re =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hc, ← Complex.exp_add]
  have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
  rw [hl, Complex.exp_re, Real.rpow_def_of_pos hn0]
  generalize Real.log (n : ℝ) = L
  congr 1
  · congr 1; simp
  · congr 1; simp; ring

theorem rs_pointwise (t : ℝ) (ht : 509 ≤ t) (hp : 0 < RSInt.rsFrac t)
    (hcos : Real.cos (2 * π * RSInt.rsFrac t) ≠ 0) :
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ 2 * ‖S (RSInt.rsNn t) t‖ + 3 := by
  obtain ⟨M, φ, hM, hG, -, hb⟩ := RSSeam.rs_Z_C0_seam ht hp hcos
  set s : ℂ := (1 / 2 : ℂ) + t * I with hs
  have h0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [s] at this
  have enorm1 : ‖cexp (I * φ)‖ = 1 := by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hz : ‖riemannZeta s‖ = |(completedRiemannZeta s).re / M| := by
    rw [riemannZeta_def_of_ne_zero h0, norm_div, hG, norm_mul, enorm1,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, abs_div, abs_of_pos hM]
    congr 1
    have := completed_im_zero t
    rw [← hs] at this
    conv_lhs => rw [← Complex.re_add_im (completedRiemannZeta s), this]
    simp
  have hsum : ∑ n ∈ Finset.Icc 1 (RSInt.rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.cos (φ - t * Real.log n) = (cexp (I * φ) * S (RSInt.rsNn t) t).re := by
    rw [S, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [term_re φ t n (Finset.mem_Icc.1 hn).1]
  have hsumb : |(cexp (I * φ) * S (RSInt.rsNn t) t).re| ≤ ‖S (RSInt.rsNn t) t‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, enorm1, one_mul]
  have hpsi := psi_bound _ (rsFrac_nonneg t) (rsFrac_lt_one t) hcos
  have hpos : (0 : ℝ) < t := by linarith
  have h1 : (t / (2 * π)) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
    rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
  have h1' : 0 ≤ (t / (2 * π)) ^ (-(1 / 4 : ℝ)) := by positivity
  have h2 : 13 / 5 * t ^ (-(3 / 4 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hpos.le]
    have hq : Real.sqrt t ≤ t ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have : (22 : ℝ) ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by linarith)
    have hpos' : 0 < t ^ (3 / 4 : ℝ) := by positivity
    rw [← div_eq_mul_inv, div_le_one hpos']; linarith
  have hsign : |(-1 : ℝ) ^ (RSInt.rsNn t + 1)| = 1 := by simp
  have hterm : |(-1 : ℝ) ^ (RSInt.rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) *
      RSInt.rsPsi (RSInt.rsFrac t)| ≤ 2 := by
    rw [abs_mul, abs_mul, hsign, one_mul, abs_of_nonneg h1']
    nlinarith [abs_nonneg (RSInt.rsPsi (RSInt.rsFrac t))]
  rw [hz]
  rw [hsum] at hb
  have := abs_sub_abs_le_abs_sub ((completedRiemannZeta s).re / M)
    (2 * (cexp (I * φ) * S (RSInt.rsNn t) t).re + (-1 : ℝ) ^ (RSInt.rsNn t + 1) *
      (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * RSInt.rsPsi (RSInt.rsFrac t))
  have h3 := abs_add_le (2 * (cexp (I * φ) * S (RSInt.rsNn t) t).re) ((-1 : ℝ) ^ (RSInt.rsNn t + 1) *
      (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * RSInt.rsPsi (RSInt.rsFrac t))
  rw [abs_mul, abs_two] at h3
  linarith

theorem bad_countable :
    (Set.Ici (509 : ℝ) ∩ {t : ℝ | ¬ (0 < RSInt.rsFrac t ∧ Real.cos (2 * π * RSInt.rsFrac t) ≠ 0)}).Countable := by
  have hc : (Set.range (fun N : ℕ => 2 * π * (N : ℝ) ^ 2) ∪
      Set.range (fun q : ℕ × ℤ => 2 * π * ((q.1 : ℝ) + (2 * q.2 + 1) / 4) ^ 2)).Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  refine hc.mono ?_
  rintro t ⟨ht, hbad⟩
  simp only [Set.mem_Ici] at ht
  simp only [Set.mem_ofPred_eq, not_and_or, not_lt, not_not] at hbad
  have ht0 : 0 ≤ t / (2 * π) := by positivity
  have hα : t = 2 * π * ((RSInt.rsNn t : ℝ) + RSInt.rsFrac t) ^ 2 := by
    have : (RSInt.rsNn t : ℝ) + RSInt.rsFrac t = RSInt.rsAlpha t := by
      unfold RSInt.rsFrac; ring
    rw [this, RSInt.rsAlpha, Real.sq_sqrt ht0]
    field_simp
  rcases hbad with h | h
  · left
    have : RSInt.rsFrac t = 0 := le_antisymm h (rsFrac_nonneg t)
    refine ⟨RSInt.rsNn t, ?_⟩
    simp only
    rw [this, add_zero] at hα; exact hα.symm
  · right
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 h
    have hp : RSInt.rsFrac t = (2 * k + 1) / 4 := by
      have hpi := Real.pi_pos
      field_simp at hk ⊢
      nlinarith
    refine ⟨(RSInt.rsNn t, k), ?_⟩
    simp only
    rw [hp] at hα; exact hα.symm

theorem power_mean {ι : Type*} (s : Finset ι) (wt x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ wt i)
    (_hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, wt i * x i) ^ 4 ≤ (∑ i ∈ s, wt i) ^ 3 * ∑ i ∈ s, wt i * x i ^ 4 := by
  have h1 : (∑ i ∈ s, wt i * x i) ^ 2 ≤ (∑ i ∈ s, wt i) * ∑ i ∈ s, wt i * x i ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)) (fun i hi => by nlinarith [hw i hi])
  have h2 : (∑ i ∈ s, wt i * x i ^ 2) ^ 2 ≤ (∑ i ∈ s, wt i) * ∑ i ∈ s, wt i * x i ^ 4 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i hi => mul_nonneg (hw i hi) (by positivity)) (fun i hi => by nlinarith [hw i hi])
  have hW : 0 ≤ ∑ i ∈ s, wt i := Finset.sum_nonneg hw
  have hA : 0 ≤ ∑ i ∈ s, wt i * x i ^ 2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  calc (∑ i ∈ s, wt i * x i) ^ 4 = ((∑ i ∈ s, wt i * x i) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i ∈ s, wt i) * ∑ i ∈ s, wt i * x i ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (∑ i ∈ s, wt i) ^ 2 * (∑ i ∈ s, wt i * x i ^ 2) ^ 2 := by ring
    _ ≤ (∑ i ∈ s, wt i) ^ 2 * ((∑ i ∈ s, wt i) * ∑ i ∈ s, wt i * x i ^ 4) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- Conjugation of `k^{-it}`. -/
lemma conj_natCast_cpow (k : ℕ) (hk : k ≠ 0) (t : ℝ) :
    (starRingEnd ℂ) ((k : ℂ) ^ (-((t : ℂ) * I))) = (k : ℂ) ^ (I * t) := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [cpow_def_of_ne_zero hk', cpow_def_of_ne_zero hk', ← Complex.exp_conj]
  congr 1
  rw [map_mul, ← natCast_log, Complex.conj_ofReal, map_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  ring

lemma zeta_cont : Continuous (fun t : ℝ => riemannZeta (1 / 2 + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => 1 / 2 + (t : ℂ) * I)
    (differentiableAt_riemannZeta h).continuousAt (by fun_prop)

lemma four_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [mul_nonneg (sq_nonneg (a - b)) (add_nonneg (add_nonneg
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 7) (sq_nonneg a))
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) (mul_nonneg ha hb)))
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 7) (sq_nonneg b)))]

/-! ## One dyadic block via the Perron lemma -/
/-- The Perron weights. -/
def kap (μ : ℤ) : ℝ := if μ = 0 then 1 else 1 / (π * |(μ : ℝ)|)

lemma kap_nonneg (μ : ℤ) : 0 ≤ kap μ := by
  unfold kap; split_ifs <;> positivity

lemma V_low (j ν : ℕ) (h : ν < 2 ^ (j - 1)) : V ((ν : ℝ) / ((2 ^ j : ℕ) : ℝ)) = 0 := by
  apply V_eq_zero_of_le
  rcases j with _ | j
  · have : ν = 0 := by simpa using h
    subst this; simp
  · simp only [Nat.add_sub_cancel] at h
    have h' : (ν : ℝ) ≤ 2 ^ j := by exact_mod_cast h.le
    push_cast
    rw [div_le_iff₀ (by positivity), pow_succ]
    linarith

lemma V_high (j ν : ℕ) (h : 2 * 2 ^ j ≤ ν) : V ((ν : ℝ) / ((2 ^ j : ℕ) : ℝ)) = 0 := by
  apply V_eq_zero_of_ge
  have h' : (2 : ℝ) * 2 ^ j ≤ ν := by exact_mod_cast h
  push_cast
  rw [le_div_iff₀ (by positivity)]
  exact h'

/-- The coefficients fed to the Perron lemma. -/
def cf (j ν : ℕ) : ℂ :=
  if 2 ^ (j - 1) ≤ ν then
    ((V ((ν : ℝ) / ((2 ^ j : ℕ) : ℝ)) * Real.sqrt (((2 ^ (j - 1) : ℕ) : ℝ) / ν) : ℝ) : ℂ)
  else 0

lemma cf_norm (j ν : ℕ) : ‖cf j ν‖ ≤ 1 := by
  unfold cf
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (V_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : Real.sqrt (((2 ^ (j - 1) : ℕ) : ℝ) / ν) ≤ 1 := by
      exact Real.sqrt_le_one.2 (div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg _))
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (V_le_one _) h1 (Real.sqrt_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp

lemma cpow_neg_half (ν : ℕ) : (ν : ℂ) ^ (-(1 / 2 : ℂ)) = (((Real.sqrt ν)⁻¹ : ℝ) : ℂ) := by
  have h : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg ν),
    Real.rpow_neg (Nat.cast_nonneg ν), Real.sqrt_eq_rpow]

lemma cf_eq (j ν : ℕ) :
    cf j ν = ((Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) : ℝ) : ℂ) *
      (((V ((ν : ℝ) / ((2 ^ j : ℕ) : ℝ)) : ℝ) : ℂ) * (ν : ℂ) ^ (-(1 / 2 : ℂ))) := by
  unfold cf
  split_ifs with h
  · rw [cpow_neg_half, Real.sqrt_div (Nat.cast_nonneg _)]
    push_cast
    ring
  · rw [V_low j ν (not_le.1 h)]
    simp

lemma sqrtA_pos (j : ℕ) : 0 < Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) :=
  Real.sqrt_pos.2 (by positivity)

lemma Q_eq (j : ℕ) (v : ℝ) :
    ∑ ν ∈ Finset.Icc (2 ^ (j - 1)) (2 ^ (j + 1)), cf j ν * (ν : ℂ) ^ ((v : ℂ) * I) =
      ((Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) : ℝ) : ℂ) * Q (2 ^ j) v := by
  unfold Q
  rw [Finset.mul_sum]
  apply Finset.sum_subset_zero_on_sdiff
  · intro ν hν
    rw [Finset.mem_Icc] at hν ⊢
    have : 1 ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
    refine ⟨by omega, ?_⟩
    rw [pow_succ] at hν; omega
  · intro ν hν
    rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hν
    have hlt : ν < 2 ^ (j - 1) := by
      by_contra hc
      apply hν.2
      refine ⟨not_lt.1 hc, ?_⟩
      rw [pow_succ]; omega
    rw [V_low j ν hlt]; simp
  · intro ν hν
    have hν0 : (ν : ℂ) ≠ 0 := by
      have h1 : 1 ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
      have := (Finset.mem_Icc.1 hν).1
      exact_mod_cast (by omega : ν ≠ 0)
    rw [cf_eq, Complex.cpow_add _ _ hν0]
    ring

lemma W_eq (j N : ℕ) (t : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ((V ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) : ℝ) : ℂ) *
        (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) =
      ((Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ *
        ∑ ν ∈ Finset.Icc (2 ^ (j - 1)) (min (2 ^ (j + 1)) N),
          cf j ν * (ν : ℂ) ^ (((-t : ℝ) : ℂ) * I) := by
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro ν hν
    rw [Finset.mem_Icc] at hν ⊢
    have : 1 ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
    exact ⟨by omega, hν.2.trans (min_le_right _ _)⟩
  · intro ν hν
    rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hν
    by_cases hlt : ν < 2 ^ (j - 1)
    · rw [V_low j ν hlt]; simp
    · have hgt : 2 * 2 ^ j ≤ ν := by
        by_contra hc
        apply hν.2
        refine ⟨not_lt.1 hlt, le_min ?_ hν.1.2⟩
        rw [pow_succ]; omega
      rw [V_high j ν hgt]; simp
  · intro ν hν
    have hν0 : (ν : ℂ) ≠ 0 := by
      have h1 : 1 ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
      have := (Finset.mem_Icc.1 hν).1
      exact_mod_cast (by omega : ν ≠ 0)
    have hs : ((Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (sqrtA_pos j).ne'
    have he : (-((1 / 2 : ℂ) + t * I)) = -(1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [cf_eq, he, Complex.cpow_add _ _ hν0]
    field_simp

/-- One dyadic block of the Riemann–Siegel sum, bounded by shifted smooth blocks. -/
lemma block (CP : ℝ)
    (hP : ∀ (A B L M K : ℕ) (c : ℕ → ℂ) (v : ℝ),
      1 ≤ A → B ≤ 20 * A → A ≤ L → M ≤ B → 1 ≤ K → (∀ ν, ‖c ν‖ ≤ 1) →
      ‖∑ ν ∈ Finset.Icc L M, c ν * (ν : ℂ) ^ ((v : ℂ) * Complex.I)‖ ≤
        ∑ μ ∈ Finset.Icc (-(K : ℤ)) K,
          (if μ = 0 then 1 else 1 / (Real.pi * |(μ : ℝ)|)) *
            ‖∑ ν ∈ Finset.Icc A B, c ν * (ν : ℂ) ^ (((v + Real.pi * μ / 2 : ℝ) : ℂ) * Complex.I)‖ +
          CP * (B : ℝ) ^ 2 / K)
    (j N K : ℕ) (hK : 1 ≤ K) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, ((V ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) : ℝ) : ℂ) *
        (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ ≤
      ∑ μ ∈ Finset.Icc (-(K : ℤ)) K, kap μ * ‖Q (2 ^ j) (π * μ / 2 - t)‖ +
        CP * (((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / K / Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ)) := by
  have hs := sqrtA_pos j
  have h20 : 2 ^ (j + 1) ≤ 20 * 2 ^ (j - 1) := by
    rcases j with _ | j
    · norm_num
    · simp only [Nat.add_sub_cancel, pow_succ]; omega
  have h := hP (2 ^ (j - 1)) (2 ^ (j + 1)) (2 ^ (j - 1)) (min (2 ^ (j + 1)) N) K (cf j) (-t)
    Nat.one_le_two_pow h20 le_rfl (min_le_left _ _) hK (cf_norm j)
  have hterm : ∀ μ : ℤ, ‖∑ ν ∈ Finset.Icc (2 ^ (j - 1)) (2 ^ (j + 1)),
      cf j ν * (ν : ℂ) ^ (((-t + Real.pi * μ / 2 : ℝ) : ℂ) * Complex.I)‖ =
      Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) * ‖Q (2 ^ j) (π * μ / 2 - t)‖ := by
    intro μ
    rw [Q_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    congr 3
    ring
  simp_rw [hterm] at h
  rw [W_eq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    inv_mul_le_iff₀ hs]
  refine h.trans (le_of_eq ?_)
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun μ _ => ?_
    unfold kap; ring
  · field_simp

lemma sqrt_sqrt_cube (T : ℝ) (hT : 0 ≤ T) :
    Real.sqrt (Real.sqrt T) ^ 3 = T ^ (3 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hT, ← Real.rpow_natCast,
    ← Real.rpow_mul hT]
  norm_num

lemma err_le (T : ℝ) (hT : 16 ≤ T) (j : ℕ) (hj : (2 : ℝ) ^ j ≤ 2 * Real.sqrt T) :
    ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / (⌊T ^ (3 / 4 : ℝ)⌋₊ : ℝ) /
      Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) ≤ 32 := by
  have hs3 : Real.sqrt (Real.sqrt T) ^ 3 = T ^ (3 / 4 : ℝ) := sqrt_sqrt_cube T (by linarith)
  have h4 : (4 : ℝ) ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hs2 : (2 : ℝ) ≤ Real.sqrt (Real.sqrt T) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hs8 : (8 : ℝ) ≤ Real.sqrt (Real.sqrt T) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hs2 3
    linarith
  have hK : Real.sqrt (Real.sqrt T) ^ 3 / 2 ≤ (⌊T ^ (3 / 4 : ℝ)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (T ^ (3 / 4 : ℝ))
    rw [← hs3] at this ⊢
    linarith
  have hK0 : (0 : ℝ) < (⌊T ^ (3 / 4 : ℝ)⌋₊ : ℝ) := by linarith
  have ha : (0 : ℝ) < 2 ^ j := by positivity
  have hr2 : Real.sqrt ((2 : ℝ) ^ j / 2) ^ 2 = (2 : ℝ) ^ j / 2 := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ Real.sqrt ((2 : ℝ) ^ j / 2) := Real.sqrt_nonneg _
  have hrs : Real.sqrt ((2 : ℝ) ^ j / 2) ≤ Real.sqrt (Real.sqrt T) :=
    Real.sqrt_le_sqrt (by linarith)
  have hA : Real.sqrt ((2 : ℝ) ^ j / 2) ≤ Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    have h1 : 2 ^ j ≤ 2 * 2 ^ (j - 1) := by
      rcases j with _ | j
      · norm_num
      · simp only [Nat.add_sub_cancel, pow_succ]; omega
    have h2 : (2 : ℝ) ^ j ≤ 2 * ((2 ^ (j - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hB : ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 = 16 * Real.sqrt ((2 : ℝ) ^ j / 2) ^ 4 := by
    have : Real.sqrt ((2 : ℝ) ^ j / 2) ^ 4 = ((2 : ℝ) ^ j / 2) ^ 2 := by
      rw [show Real.sqrt ((2 : ℝ) ^ j / 2) ^ 4 = (Real.sqrt ((2 : ℝ) ^ j / 2) ^ 2) ^ 2 by ring, hr2]
    rw [this]; push_cast; ring
  have hsA := sqrtA_pos j
  rw [div_div, div_le_iff₀ (by positivity), hB]
  have h3 : Real.sqrt ((2 : ℝ) ^ j / 2) ^ 3 ≤ Real.sqrt (Real.sqrt T) ^ 3 :=
    pow_le_pow_left₀ hr0 hrs 3
  calc 16 * Real.sqrt ((2 : ℝ) ^ j / 2) ^ 4
      = 16 * (Real.sqrt ((2 : ℝ) ^ j / 2) ^ 3 * Real.sqrt ((2 : ℝ) ^ j / 2)) := by ring
    _ ≤ 16 * (Real.sqrt (Real.sqrt T) ^ 3 * Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ)) := by
        gcongr
    _ ≤ 16 * ((2 * (⌊T ^ (3 / 4 : ℝ)⌋₊ : ℝ)) * Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ)) := by
        gcongr; linarith
    _ = 32 * ((⌊T ^ (3 / 4 : ℝ)⌋₊ : ℝ) * Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ)) := by ring

/-! ## The pointwise bound for ζ -/
lemma S_split (J N : ℕ) (t : ℝ) (hN : N ≤ 2 ^ J) :
    S N t = ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.Icc 1 N,
      ((V ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) := by
  rw [Finset.sum_comm, S]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [← Finset.sum_mul]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
  have h2 : (n : ℝ) ≤ 2 ^ J := by exact_mod_cast (Finset.mem_Icc.1 hn).2.trans hN
  have h3 : ∑ j ∈ Finset.range (J + 1), ((V ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum]
    have := V_partition J n h1 h2
    push_cast
    exact_mod_cast this
  rw [h3, one_mul]

/-- The number of dyadic scales. -/
def Jof (T : ℝ) : ℕ := Nat.log 2 ⌊Real.sqrt T⌋₊ + 1

/-- The Perron truncation. -/
def Kof (T : ℝ) : ℕ := ⌊T ^ (3 / 4 : ℝ)⌋₊

/-- The index set of the scales and shifts. -/
def Pof (T : ℝ) : Finset (ℕ × ℤ) :=
  Finset.range (Jof T + 1) ×ˢ Finset.Icc (-(Kof T : ℤ)) (Kof T)

lemma floor_sqrt_pos (T : ℝ) (hT : 1 ≤ T) : 1 ≤ ⌊Real.sqrt T⌋₊ :=
  Nat.le_floor (by simpa using Real.one_le_sqrt.2 hT)

lemma two_pow_J_le (T : ℝ) (hT : 1 ≤ T) : (2 : ℝ) ^ Jof T ≤ 2 * Real.sqrt T := by
  unfold Jof
  have h1 := floor_sqrt_pos T hT
  have h2 : 2 ^ Nat.log 2 ⌊Real.sqrt T⌋₊ ≤ ⌊Real.sqrt T⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have h3 : ((⌊Real.sqrt T⌋₊ : ℕ) : ℝ) ≤ Real.sqrt T := Nat.floor_le (Real.sqrt_nonneg T)
  have h4 : (2 : ℝ) ^ Nat.log 2 ⌊Real.sqrt T⌋₊ ≤ (⌊Real.sqrt T⌋₊ : ℝ) := by exact_mod_cast h2
  rw [pow_succ]; linarith

lemma N_le (T t : ℝ) (hT : 1 ≤ T) (ht : t ≤ 3 * T) : RSInt.rsNn t ≤ 2 ^ Jof T := by
  have h1 : RSInt.rsNn t ≤ ⌊Real.sqrt T⌋₊ := by
    unfold RSInt.rsNn RSInt.rsAlpha
    apply Nat.floor_mono
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  exact h1.trans (Nat.lt_pow_succ_log_self (by norm_num) _).le

lemma K_pos (T : ℝ) (hT : 1 ≤ T) : 1 ≤ Kof T :=
  Nat.le_floor (by simpa using Real.one_le_rpow hT (by norm_num))

lemma zeta_pointwise (CP : ℝ) (hCP : 0 ≤ CP)
    (hP : ∀ (A B L M K : ℕ) (c : ℕ → ℂ) (v : ℝ),
      1 ≤ A → B ≤ 20 * A → A ≤ L → M ≤ B → 1 ≤ K → (∀ ν, ‖c ν‖ ≤ 1) →
      ‖∑ ν ∈ Finset.Icc L M, c ν * (ν : ℂ) ^ ((v : ℂ) * Complex.I)‖ ≤
        ∑ μ ∈ Finset.Icc (-(K : ℤ)) K,
          (if μ = 0 then 1 else 1 / (Real.pi * |(μ : ℝ)|)) *
            ‖∑ ν ∈ Finset.Icc A B, c ν * (ν : ℂ) ^ (((v + Real.pi * μ / 2 : ℝ) : ℂ) * Complex.I)‖ +
          CP * (B : ℝ) ^ 2 / K)
    (T t : ℝ) (hT : 1018 ≤ T) (ht1 : T / 2 ≤ t) (ht2 : t ≤ 3 * T)
    (hgood : 0 < RSInt.rsFrac t ∧ Real.cos (2 * π * RSInt.rsFrac t) ≠ 0) :
    ‖riemannZeta (1 / 2 + t * I)‖ ≤
      ∑ p ∈ Pof T, 2 * kap p.2 * ‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ +
        (64 * CP * (Jof T + 1) + 3) := by
  have h1 := rs_pointwise t (by linarith) hgood.1 hgood.2
  have hN := N_le T t (by linarith) ht2
  rw [S_split (Jof T) _ t hN] at h1
  have hK := K_pos T (by linarith)
  have h2 : ∀ j ∈ Finset.range (Jof T + 1),
      ‖∑ n ∈ Finset.Icc 1 (RSInt.rsNn t), ((V ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) : ℝ) : ℂ) *
        (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ ≤
      ∑ μ ∈ Finset.Icc (-(Kof T : ℤ)) (Kof T), kap μ * ‖Q (2 ^ j) (π * μ / 2 - t)‖ +
        32 * CP := by
    intro j hj
    have hj' : (2 : ℝ) ^ j ≤ 2 * Real.sqrt T :=
      (pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).trans
        (two_pow_J_le T (by linarith))
    have hb := block CP hP j (RSInt.rsNn t) (Kof T) hK t
    have he : ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / (Kof T : ℝ) /
        Real.sqrt ((2 ^ (j - 1) : ℕ) : ℝ) ≤ 32 := err_le T (by linarith) j hj'
    have := mul_le_mul_of_nonneg_left he hCP
    linarith
  have h3 := (norm_sum_le _ _).trans (Finset.sum_le_sum h2)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
  unfold Pof
  rw [Finset.sum_product]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  push_cast at h1 h3 ⊢
  linarith

lemma kap_sum_le (K : ℕ) : ∑ μ ∈ Finset.Icc (-(K : ℤ)) K, kap μ ≤ 4 + 2 * Real.log K := by
  have hsub : Finset.Icc (-(K : ℤ)) K ⊆
      (Finset.range (K + 1)).image (fun k : ℕ => (k : ℤ)) ∪
        (Finset.range (K + 1)).image (fun k : ℕ => -(k : ℤ)) := by
    intro μ hμ
    rw [Finset.mem_Icc] at hμ
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases le_total 0 μ with h | h
    · left; exact ⟨μ.toNat, Finset.mem_range.2 (by omega), by omega⟩
    · right; exact ⟨(-μ).toNat, Finset.mem_range.2 (by omega), by omega⟩
  have hhalf : ∑ k ∈ Finset.range (K + 1), kap (k : ℤ) ≤ 2 + Real.log K := by
    rw [Finset.sum_range_succ']
    have h0 : kap ((0 : ℕ) : ℤ) = 1 := by simp [kap]
    have hk : ∀ k ∈ Finset.range K, kap ((k + 1 : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℝ)⁻¹ := by
      intro k _
      unfold kap
      rw [if_neg (by exact_mod_cast Nat.succ_ne_zero k)]
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      rw [Int.cast_natCast, abs_of_pos hpos, one_div, mul_inv]
      have h1 : π⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
      have h2 := inv_pos.2 hpos
      nlinarith
    have hH : ∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℝ)⁻¹ = (harmonic K : ℝ) := by
      simp [harmonic]
    have h3 := harmonic_le_one_add_log K
    have h4 := Finset.sum_le_sum hk
    rw [h0]; linarith
  have hneg : ∀ k : ℕ, kap (-(k : ℤ)) = kap k := fun k => by simp [kap]
  calc ∑ μ ∈ Finset.Icc (-(K : ℤ)) K, kap μ
      ≤ ∑ μ ∈ (Finset.range (K + 1)).image (fun k : ℕ => (k : ℤ)) ∪
          (Finset.range (K + 1)).image (fun k : ℕ => -(k : ℤ)), kap μ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun μ _ _ => kap_nonneg μ)
    _ ≤ ∑ μ ∈ (Finset.range (K + 1)).image (fun k : ℕ => (k : ℤ)), kap μ +
          ∑ μ ∈ (Finset.range (K + 1)).image (fun k : ℕ => -(k : ℤ)), kap μ := by
        have h := Finset.sum_union_inter (s₁ := (Finset.range (K + 1)).image (fun k : ℕ => (k : ℤ)))
          (s₂ := (Finset.range (K + 1)).image (fun k : ℕ => -(k : ℤ))) (f := kap)
        have h0 : 0 ≤ ∑ μ ∈ (Finset.range (K + 1)).image (fun k : ℕ => (k : ℤ)) ∩
          (Finset.range (K + 1)).image (fun k : ℕ => -(k : ℤ)), kap μ :=
          Finset.sum_nonneg (fun μ _ => kap_nonneg μ)
        linarith
    _ = ∑ k ∈ Finset.range (K + 1), kap (k : ℤ) + ∑ k ∈ Finset.range (K + 1), kap (-(k : ℤ)) := by
        rw [Finset.sum_image (fun a _ b _ h => by simpa using h),
          Finset.sum_image (fun a _ b _ h => by simpa using h)]
    _ ≤ 4 + 2 * Real.log K := by
        simp_rw [hneg]; linarith

lemma zeta4_pointwise (CP : ℝ) (hCP : 0 ≤ CP)
    (hP : ∀ (A B L M K : ℕ) (c : ℕ → ℂ) (v : ℝ),
      1 ≤ A → B ≤ 20 * A → A ≤ L → M ≤ B → 1 ≤ K → (∀ ν, ‖c ν‖ ≤ 1) →
      ‖∑ ν ∈ Finset.Icc L M, c ν * (ν : ℂ) ^ ((v : ℂ) * Complex.I)‖ ≤
        ∑ μ ∈ Finset.Icc (-(K : ℤ)) K,
          (if μ = 0 then 1 else 1 / (Real.pi * |(μ : ℝ)|)) *
            ‖∑ ν ∈ Finset.Icc A B, c ν * (ν : ℂ) ^ (((v + Real.pi * μ / 2 : ℝ) : ℂ) * Complex.I)‖ +
          CP * (B : ℝ) ^ 2 / K)
    (T t : ℝ) (hT : 1018 ≤ T) (ht1 : T / 2 ≤ t) (ht2 : t ≤ 3 * T)
    (hgood : 0 < RSInt.rsFrac t ∧ Real.cos (2 * π * RSInt.rsFrac t) ≠ 0) :
    ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤
      8 * (∑ p ∈ Pof T, 2 * kap p.2) ^ 3 *
          (∑ p ∈ Pof T, 2 * kap p.2 * ‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4) +
        8 * (64 * CP * (Jof T + 1) + 3) ^ 4 := by
  have h1 := zeta_pointwise CP hCP hP T t hT ht1 ht2 hgood
  have hw : ∀ p ∈ Pof T, 0 ≤ 2 * kap p.2 := fun p _ => by
    have := kap_nonneg p.2; positivity
  have h2 := power_mean (Pof T) (fun p => 2 * kap p.2)
    (fun p => ‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖) hw (fun _ _ => norm_nonneg _)
  beta_reduce at h2
  have hX : 0 ≤ ∑ p ∈ Pof T, 2 * kap p.2 * ‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ :=
    Finset.sum_nonneg fun p hp => mul_nonneg (hw p hp) (norm_nonneg _)
  have hE : (0 : ℝ) ≤ 64 * CP * (Jof T + 1) + 3 := by positivity
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 4
  have h4 := four_le _ _ hX hE
  linarith

/-! ## Continuity, integrability, the Gaussian cover -/
lemma one_le_log (T : ℝ) (hT : 3 ≤ T) : 1 ≤ Real.log T := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma Q_cont (A : ℕ) (u : ℝ) : Continuous (fun t : ℝ => Q A (u - t)) := by
  unfold Q
  apply continuous_finsetSum
  intro ν hν
  have hν0 : (ν : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.1 hν).1
    exact_mod_cast (by omega : ν ≠ 0)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hν0))

lemma Mol_cont (T : ℝ) : Continuous (fun t : ℝ => Mol T (1 / 2 + (t : ℂ) * I)) := by
  unfold Mol
  apply continuous_finsetSum
  intro m hm
  have hm0 : (m : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.1 hm).1
    exact_mod_cast (by omega : m ≠ 0)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hm0))

lemma Q_norm_le (A : ℕ) (v : ℝ) : ‖Q A v‖ ≤ 2 * A := by
  unfold Q
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ ν ∈ Finset.Icc 1 (2 * A), ‖((V ((ν : ℝ) / A) : ℝ) : ℂ) *
      (ν : ℂ) ^ (-(1 / 2 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ 1 := by
    intro ν hν
    have hν1 : 0 < ν := (Finset.mem_Icc.1 hν).1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (V_nonneg _),
      Complex.norm_natCast_cpow_of_pos hν1]
    have hre : (-(1 / 2 : ℂ) + (v : ℂ) * Complex.I).re = -(1 / 2 : ℝ) := by simp
    have h1 : (ν : ℝ) ^ (-(1 / 2 : ℂ) + (v : ℂ) * Complex.I).re ≤ 1 := by
      rw [hre]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hν1) (by norm_num)
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (V_le_one _) h1 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, Nat.card_Icc]
  simp

lemma Mol_norm_le (T t : ℝ) : ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ≤ yT T := by
  unfold Mol
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ m ∈ Finset.Icc 1 (yT T), ‖(ArithmeticFunction.moebius m : ℂ) *
      (m : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))‖ ≤ 1 := by
    intro m hm
    have hm1 : 0 < m := (Finset.mem_Icc.1 hm).1
    rw [norm_mul, Complex.norm_intCast, Complex.norm_natCast_cpow_of_pos hm1]
    have hre : (-(1 / 2 + (t : ℂ) * I)).re = -(1 / 2 : ℝ) := by simp
    have h1 : (m : ℝ) ^ (-(1 / 2 + (t : ℂ) * I)).re ≤ 1 := by
      rw [hre]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by norm_num)
    have h2 : |((ArithmeticFunction.moebius m : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h2 h1 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, Nat.card_Icc]
  simp

lemma gauss_integrable (Δ t₀ : ℝ) (hΔ : 0 < Δ) :
    Integrable (fun t : ℝ => Real.exp (-((t - t₀) / Δ) ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / Δ ^ 2) (by positivity)).comp_sub_right t₀
  refine h.congr (Eventually.of_forall fun t => ?_)
  show Real.exp (-(1 / Δ ^ 2) * (t - t₀) ^ 2) = Real.exp (-((t - t₀) / Δ) ^ 2)
  congr 1
  field_simp

lemma IG_integrable (T : ℝ) (A : ℕ) (t₀ u : ℝ) (hΔ : 0 < Delta T) :
    Integrable (fun t : ℝ => Real.exp (-((t - t₀) / Delta T) ^ 2) * ‖Q A (u - t)‖ ^ 4 *
      ‖Mol T (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4) := by
  have hg := (gauss_integrable (Delta T) t₀ hΔ).mul_const ((2 * A : ℝ) ^ 4 * (yT T : ℝ) ^ 4)
  refine hg.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact Continuous.aestronglyMeasurable
      (((Real.continuous_exp.comp (by fun_prop)).mul
        ((continuous_norm.comp (Q_cont A u)).pow 4)).mul
          ((continuous_norm.comp (Mol_cont T)).pow 4))
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (Q_norm_le A _) 4)
      (pow_le_pow_left₀ (norm_nonneg _) (Mol_norm_le T _) 4) (by positivity) (by positivity)

lemma Delta_pos (T : ℝ) (hT : 3 ≤ T) : 0 < Delta T :=
  div_pos (by linarith) (by linarith [one_le_log T hT])

lemma log_mul_Delta (T : ℝ) (hT : 3 ≤ T) : 3 * Real.log T * Delta T = 3 * T := by
  have := one_le_log T hT
  unfold Delta
  field_simp

lemma gauss_cover (T t : ℝ) (hT : 3 ≤ T) (ht1 : T / 2 ≤ t) (ht2 : t ≤ 3 * T) :
    1 ≤ Real.exp 1 * ∑ i ∈ Finset.range (⌊3 * Real.log T⌋₊ + 1),
      Real.exp (-((t - (T / 2 + i * Delta T)) / Delta T) ^ 2) := by
  have hΔ := Delta_pos T hT
  have hx0 : 0 ≤ (t - T / 2) / Delta T := div_nonneg (by linarith) hΔ.le
  have hx3 : (t - T / 2) / Delta T ≤ 3 * Real.log T := by
    rw [div_le_iff₀ hΔ, log_mul_Delta T hT]; linarith
  have hi : ⌊(t - T / 2) / Delta T⌋₊ ∈ Finset.range (⌊3 * Real.log T⌋₊ + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.floor_mono hx3))
  have h1 : (⌊(t - T / 2) / Delta T⌋₊ : ℝ) ≤ (t - T / 2) / Delta T := Nat.floor_le hx0
  have h2 : (t - T / 2) / Delta T < ⌊(t - T / 2) / Delta T⌋₊ + 1 := Nat.lt_floor_add_one _
  have hterm : Real.exp (-1) ≤
      Real.exp (-((t - (T / 2 + ⌊(t - T / 2) / Delta T⌋₊ * Delta T)) / Delta T) ^ 2) := by
    apply Real.exp_le_exp.2
    have e : (t - (T / 2 + ⌊(t - T / 2) / Delta T⌋₊ * Delta T)) / Delta T =
        (t - T / 2) / Delta T - ⌊(t - T / 2) / Delta T⌋₊ := by
      field_simp; ring
    rw [e]; nlinarith
  have hs := Finset.single_le_sum (f := fun i : ℕ =>
    Real.exp (-((t - (T / 2 + i * Delta T)) / Delta T) ^ 2)) (fun i _ => (Real.exp_pos _).le) hi
  calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hterm.trans hs) (Real.exp_pos _).le

/-- The moment of one smooth block over `[T/2, 3T]`, from Proposition G. -/
lemma block_integral (CG A₀ TG : ℝ)
    (hG : ∀ T : ℝ, TG ≤ T → ∀ (j : ℕ) (t₀ u : ℝ), (2 : ℝ) ^ j ≤ 4 * Real.sqrt T →
      T / 2 ≤ t₀ → t₀ ≤ 4 * T → |u| ≤ 2 * T ^ (3 / 4 : ℝ) →
      IG T (2 ^ j) t₀ u ≤ CG * Delta T * Real.log T ^ A₀)
    (T : ℝ) (hT : TG ≤ T) (hT3 : 3 ≤ T) (j : ℕ) (u : ℝ) (hj : (2 : ℝ) ^ j ≤ 4 * Real.sqrt T)
    (hu : |u| ≤ 2 * T ^ (3 / 4 : ℝ)) :
    ∫ t in (T / 2)..(3 * T), ‖Q (2 ^ j) (u - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 ≤
      Real.exp 1 * ((3 * Real.log T + 1) * (CG * Delta T * Real.log T ^ A₀)) := by
  have hl := one_le_log T hT3
  have hΔ := Delta_pos T hT3
  have hint : ∀ i : ℕ, Integrable (fun t : ℝ =>
      Real.exp (-((t - (T / 2 + i * Delta T)) / Delta T) ^ 2) * ‖Q (2 ^ j) (u - t)‖ ^ 4 *
        ‖Mol T (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4) := fun i => IG_integrable T (2 ^ j) _ u hΔ
  have hIG : ∀ i ∈ Finset.range (⌊3 * Real.log T⌋₊ + 1),
      ∫ t in Set.Ioc (T / 2) (3 * T),
        Real.exp (-((t - (T / 2 + i * Delta T)) / Delta T) ^ 2) * ‖Q (2 ^ j) (u - t)‖ ^ 4 *
          ‖Mol T (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4 ≤ CG * Delta T * Real.log T ^ A₀ := by
    intro i hi
    have hi' : (i : ℝ) ≤ 3 * Real.log T :=
      (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).trans
        (Nat.floor_le (by positivity))
    have hiΔ : i * Delta T ≤ 3 * T := by
      rw [← log_mul_Delta T hT3]
      exact mul_le_mul_of_nonneg_right hi' hΔ.le
    have hi0 : 0 ≤ i * Delta T := mul_nonneg (Nat.cast_nonneg i) hΔ.le
    refine (setIntegral_le_integral (hint i) (Eventually.of_forall fun t => by positivity)).trans ?_
    exact hG T hT j (T / 2 + i * Delta T) u hj (by linarith) (by linarith) hu
  have hB0 : 0 ≤ CG * Delta T * Real.log T ^ A₀ :=
    le_trans (setIntegral_nonneg measurableSet_Ioc (fun t _ => by positivity))
      (hIG 0 (Finset.mem_range.2 (Nat.succ_pos _)))
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hfc : Continuous (fun t : ℝ => ‖Q (2 ^ j) (u - t)‖ ^ 4 *
      ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) :=
    ((continuous_norm.comp (Q_cont _ u)).pow 4).mul ((continuous_norm.comp (Mol_cont T)).pow 4)
  calc ∫ t in Set.Ioc (T / 2) (3 * T), ‖Q (2 ^ j) (u - t)‖ ^ 4 *
        ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4
      ≤ ∫ t in Set.Ioc (T / 2) (3 * T), Real.exp 1 *
          ∑ i ∈ Finset.range (⌊3 * Real.log T⌋₊ + 1),
            Real.exp (-((t - (T / 2 + i * Delta T)) / Delta T) ^ 2) * ‖Q (2 ^ j) (u - t)‖ ^ 4 *
              ‖Mol T (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4 := by
        apply setIntegral_mono_on (hfc.intervalIntegrable _ _).1
          ((integrable_finsetSum _ (fun i _ => hint i)).const_mul _).integrableOn
          measurableSet_Ioc
        intro t ht
        have hc := gauss_cover T t hT3 ht.1.le ht.2
        have hf : 0 ≤ ‖Q (2 ^ j) (u - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 := by
          positivity
        have := mul_le_mul_of_nonneg_right hc hf
        rw [one_mul] at this
        refine this.trans (le_of_eq ?_)
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = Real.exp 1 * ∑ i ∈ Finset.range (⌊3 * Real.log T⌋₊ + 1),
          ∫ t in Set.Ioc (T / 2) (3 * T),
            Real.exp (-((t - (T / 2 + i * Delta T)) / Delta T) ^ 2) * ‖Q (2 ^ j) (u - t)‖ ^ 4 *
              ‖Mol T (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4 := by
        rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hint i).integrableOn)]
    _ ≤ Real.exp 1 * ∑ _i ∈ Finset.range (⌊3 * Real.log T⌋₊ + 1),
          (CG * Delta T * Real.log T ^ A₀) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hIG) (Real.exp_pos _).le
    _ ≤ Real.exp 1 * ((3 * Real.log T + 1) * (CG * Delta T * Real.log T ^ A₀)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ hB0
        push_cast
        linarith [Nat.floor_le (show (0 : ℝ) ≤ 3 * Real.log T by positivity)]

/-! ## The fourth moment of the mollifier -/
lemma Mol4_eq (T t : ℝ) :
    ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 =
      ‖∑ n ∈ Finset.Icc 1 (Lof T), (((beta (yT T) n : ℤ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ))) *
        (n : ℂ) ^ (I * t)‖ ^ 2 := by
  have h1 : ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 = ‖Mol T (1 / 2 + (t : ℂ) * I) ^ 2‖ ^ 2 := by
    rw [norm_pow]; ring
  have h2 : ∑ ℓ ∈ Finset.Icc 1 (Lof T), ((beta (yT T) ℓ : ℤ) : ℂ) *
        (ℓ : ℂ) ^ (-(1 / 2 + (t : ℂ) * I)) =
      (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 (Lof T),
        (((beta (yT T) n : ℤ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ))) * (n : ℂ) ^ (I * t)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
    have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hc : (starRingEnd ℂ) ((n : ℂ) ^ (I * t)) = (n : ℂ) ^ (-((t : ℂ) * I)) := by
      rw [← conj_natCast_cpow n hn0 t, Complex.conj_conj]
    have he : (-(1 / 2 + (t : ℂ) * I)) = -(1 / 2 : ℂ) + -((t : ℂ) * I) := by ring
    rw [map_mul, map_mul, map_intCast, hc, cpow_neg_half, Complex.conj_ofReal, he,
      Complex.cpow_add _ _ hn0', cpow_neg_half]
    ring
  rw [h1, Mol_sq, h2, RCLike.norm_conj]

lemma Lof_bounds (T : ℝ) (hT : 16 ≤ T) : (1 : ℝ) ≤ (Lof T : ℝ) ∧ (Lof T : ℝ) ^ 2 ≤ 16 * T := by
  have hw1 : (1 : ℝ) ≤ T ^ (1 / 100 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hw4 : (T ^ (1 / 100 : ℝ)) ^ 4 ≤ T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc T ^ ((1 / 100 : ℝ) * ((4 : ℕ) : ℝ)) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = T := Real.rpow_one T
  have hy1 : 1 ≤ yT T := Nat.le_floor (by push_cast; linarith)
  have hy : (yT T : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
  have hy1' : (1 : ℝ) ≤ yT T := by exact_mod_cast hy1
  constructor
  · unfold Lof; push_cast; nlinarith
  · unfold Lof; push_cast
    have := pow_le_pow_left₀ (by positivity) hy 4
    calc ((yT T : ℝ) ^ 2) ^ 2 = (yT T : ℝ) ^ 4 := by ring
      _ ≤ (2 * T ^ (1 / 100 : ℝ)) ^ 4 := this
      _ = 16 * (T ^ (1 / 100 : ℝ)) ^ 4 := by ring
      _ ≤ 16 * T := by linarith

lemma Mol_moment (T : ℝ) (hT : 16 ≤ T) :
    ∫ t in (T / 2)..(3 * T), ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 ≤ 5427 * T * Real.log T ^ 4 := by
  simp_rw [Mol4_eq]
  have hs : ∀ n ∈ Finset.Icc 1 (Lof T), 1 ≤ n ∧ n ≤ Lof T := fun n hn => Finset.mem_Icc.1 hn
  have hmv := (ArtinPrimitiveRoots.dirichlet_mean_value (Finset.Icc 1 (Lof T)) (Lof T) hs
    (fun n => ((beta (yT T) n : ℤ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ)))).1 (T / 2) (3 * T)
    (by linarith)
  have hcoef : ∑ n ∈ Finset.Icc 1 (Lof T),
      ‖((beta (yT T) n : ℤ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ))‖ ^ 2 ≤
        (1 + Real.log (Lof T)) ^ 4 := by
    refine (Finset.sum_le_sum fun n hn => ?_).trans (sum_dv_pow_div_le 2 (Lof T))
    have hn1 : 0 < n := (Finset.mem_Icc.1 hn).1
    rw [norm_mul, Complex.norm_intCast, Complex.norm_natCast_cpow_of_pos hn1, mul_pow]
    have hre : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by simp
    rw [hre]
    have h1 : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
      rw [Real.rpow_neg_one]
    rw [h1, div_eq_mul_one_div (dv n ^ 2)]
    have h2 : |((beta (yT T) n : ℤ) : ℝ)| ^ 2 ≤ dv n ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_beta_le _ _) 2
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  obtain ⟨hL1, hL2⟩ := Lof_bounds T hT
  have hl := one_le_log T (by linarith)
  have hL0 : (0 : ℝ) < (Lof T : ℝ) := by linarith
  have hlogL : Real.log (Lof T) ≤ (Lof T : ℝ) - 1 := Real.log_le_sub_one_of_pos hL0
  have hlogL0 : 0 ≤ Real.log (Lof T) := Real.log_nonneg hL1
  have hlogL2 : Real.log (Lof T) ≤ 2 * Real.log T := by
    have h1 : (Lof T : ℝ) ≤ T ^ 2 := by nlinarith
    have h2 := Real.log_le_log hL0 h1
    rw [Real.log_pow] at h2
    exact_mod_cast h2
  have hfac : 3 * T - T / 2 + 4 * (Lof T : ℝ) * (1 + Real.log (Lof T)) ≤ 67 * T := by
    nlinarith
  have hfac0 : 0 ≤ 3 * T - T / 2 + 4 * (Lof T : ℝ) * (1 + Real.log (Lof T)) := by
    have : 0 ≤ 4 * (Lof T : ℝ) * (1 + Real.log (Lof T)) := by positivity
    linarith
  have hc4 : (1 + Real.log (Lof T)) ^ 4 ≤ (3 * Real.log T) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  calc _ ≤ _ := hmv
    _ ≤ (67 * T) * (3 * Real.log T) ^ 4 :=
        mul_le_mul hfac (hcoef.trans hc4) (Finset.sum_nonneg fun _ _ => by positivity)
          (by linarith)
    _ = 5427 * T * Real.log T ^ 4 := by ring

/-! ## Assembly -/
lemma J_le (T : ℝ) (hT : 16 ≤ T) : ((Jof T : ℕ) : ℝ) + 1 ≤ 3 * Real.log T := by
  have hl := one_le_log T (by linarith)
  have h1 := floor_sqrt_pos T (by linarith)
  have h2 : 2 ^ Nat.log 2 ⌊Real.sqrt T⌋₊ ≤ ⌊Real.sqrt T⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have h3 : ((⌊Real.sqrt T⌋₊ : ℕ) : ℝ) ≤ Real.sqrt T := Nat.floor_le (Real.sqrt_nonneg T)
  have h4 : (2 : ℝ) ^ Nat.log 2 ⌊Real.sqrt T⌋₊ ≤ Real.sqrt T :=
    le_trans (by exact_mod_cast h2) h3
  have h5 := Real.log_le_log (by positivity) h4
  rw [Real.log_pow, Real.log_sqrt (by linarith)] at h5
  have h6 := Real.log_two_gt_d9
  have hm : (0 : ℝ) ≤ (Nat.log 2 ⌊Real.sqrt T⌋₊ : ℝ) := Nat.cast_nonneg _
  unfold Jof
  push_cast
  nlinarith

lemma Wt_le (T : ℝ) (hT : 16 ≤ T) : ∑ p ∈ Pof T, 2 * kap p.2 ≤ 36 * Real.log T ^ 2 := by
  have hl := one_le_log T (by linarith)
  have hJ := J_le T hT
  have hK := K_pos T (by linarith)
  have hK1 : (1 : ℝ) ≤ (Kof T : ℝ) := by exact_mod_cast hK
  have hKT : (Kof T : ℝ) ≤ T := by
    refine (Nat.floor_le (by positivity)).trans ?_
    calc T ^ (3 / 4 : ℝ) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = T := Real.rpow_one T
  have hlogK : Real.log (Kof T) ≤ Real.log T := Real.log_le_log (by linarith) hKT
  have hks := kap_sum_le (Kof T)
  have hks0 : 0 ≤ ∑ μ ∈ Finset.Icc (-(Kof T : ℤ)) (Kof T), kap μ :=
    Finset.sum_nonneg fun μ _ => kap_nonneg μ
  unfold Pof
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  have h6 : ∑ μ ∈ Finset.Icc (-(Kof T : ℤ)) (Kof T), kap μ ≤ 6 * Real.log T := by linarith
  have h7 := mul_le_mul hJ h6 hks0 (by positivity)
  calc _ ≤ 2 * ((3 * Real.log T) * (6 * Real.log T)) := by linarith
    _ = 36 * Real.log T ^ 2 := by ring

lemma shift_ok (T : ℝ) (hT : 16 ≤ T) (p : ℕ × ℤ) (hp : p ∈ Pof T) :
    (2 : ℝ) ^ p.1 ≤ 4 * Real.sqrt T ∧ |π * (p.2 : ℝ) / 2| ≤ 2 * T ^ (3 / 4 : ℝ) := by
  unfold Pof at hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp
  constructor
  · have h1 : (2 : ℝ) ^ p.1 ≤ 2 ^ Jof T :=
      pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.1 hp.1)
    have h2 := two_pow_J_le T (by linarith)
    have h3 := Real.sqrt_nonneg T
    linarith
  · have hK : (Kof T : ℝ) ≤ T ^ (3 / 4 : ℝ) := Nat.floor_le (by positivity)
    have h1 : |(p.2 : ℝ)| ≤ (Kof T : ℝ) := by
      rw [abs_le]
      constructor
      · exact_mod_cast hp.2.1
      · exact_mod_cast hp.2.2
    have hpi := Real.pi_pos
    have hpi4 := Real.pi_lt_four
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
    have h0 := abs_nonneg (p.2 : ℝ)
    have h2 : π * |(p.2 : ℝ)| ≤ 4 * T ^ (3 / 4 : ℝ) :=
      mul_le_mul hpi4.le (h1.trans hK) h0 (by norm_num)
    linarith

lemma main_bound (CG A₀ TG : ℝ)
    (hG : ∀ T : ℝ, TG ≤ T → ∀ (j : ℕ) (t₀ u : ℝ), (2 : ℝ) ^ j ≤ 4 * Real.sqrt T →
      T / 2 ≤ t₀ → t₀ ≤ 4 * T → |u| ≤ 2 * T ^ (3 / 4 : ℝ) →
      IG T (2 ^ j) t₀ u ≤ CG * Delta T * Real.log T ^ A₀)
    (CP : ℝ) (hCP : 0 < CP)
    (hP : ∀ (A B L M K : ℕ) (c : ℕ → ℂ) (v : ℝ),
      1 ≤ A → B ≤ 20 * A → A ≤ L → M ≤ B → 1 ≤ K → (∀ ν, ‖c ν‖ ≤ 1) →
      ‖∑ ν ∈ Finset.Icc L M, c ν * (ν : ℂ) ^ ((v : ℂ) * Complex.I)‖ ≤
        ∑ μ ∈ Finset.Icc (-(K : ℤ)) K,
          (if μ = 0 then 1 else 1 / (Real.pi * |(μ : ℝ)|)) *
            ‖∑ ν ∈ Finset.Icc A B, c ν * (ν : ℂ) ^ (((v + Real.pi * μ / 2 : ℝ) : ℂ) * Complex.I)‖ +
          CP * (B : ℝ) ^ 2 / K)
    (T : ℝ) (hTG : TG ≤ T) (hT : 1018 ≤ T) :
    ∫ t in (T / 2)..(3 * T),
        ‖Mol T (1 / 2 + (t : ℂ) * I) * riemannZeta (1 / 2 + (t : ℂ) * I)‖ ^ 4 ≤
      (96 * 36 ^ 4 * |CG| + 8 * 5427 * (192 * CP + 3) ^ 4) * T *
        Real.log T ^ (8 + |A₀|) := by
  have hl := one_le_log T (by linarith)
  have hl0 : 0 < Real.log T := by linarith
  have hΔ := Delta_pos T (by linarith)
  have hTT : T / 2 ≤ 3 * T := by linarith
  have hw : ∀ p ∈ Pof T, 0 ≤ 2 * kap p.2 := fun p _ => by
    have := kap_nonneg p.2; positivity
  have hWt0 : 0 ≤ ∑ p ∈ Pof T, 2 * kap p.2 := Finset.sum_nonneg hw
  have hWle := Wt_le T (by linarith)
  have hJ := J_le T (by linarith)
  have hE0 : (0 : ℝ) ≤ 64 * CP * (Jof T + 1) + 3 := by positivity
  have hEle : 64 * CP * ((Jof T : ℝ) + 1) + 3 ≤ (192 * CP + 3) * Real.log T := by nlinarith
  have hmc : Continuous (fun t : ℝ => ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) :=
    (continuous_norm.comp (Mol_cont T)).pow 4
  have hqc : ∀ p : ℕ × ℤ, Continuous (fun t : ℝ => ‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 *
      ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) := fun p =>
    ((continuous_norm.comp (Q_cont _ _)).pow 4).mul hmc
  have hsc : Continuous (fun t : ℝ => ∑ p ∈ Pof T, 2 * kap p.2 *
      (‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4)) :=
    continuous_finsetSum _ fun p _ => continuous_const.mul (hqc p)
  have hqc' : ∀ p : ℕ × ℤ, Continuous (fun t : ℝ => 2 * kap p.2 *
      (‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4)) := fun p =>
    continuous_const.mul (hqc p)
  have hc1 : Continuous (fun t : ℝ => 8 * (∑ p ∈ Pof T, 2 * kap p.2) ^ 3 *
      (∑ p ∈ Pof T, 2 * kap p.2 *
        (‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4))) :=
    continuous_const.mul hsc
  have hc2 : Continuous (fun t : ℝ => 8 * (64 * CP * ((Jof T : ℝ) + 1) + 3) ^ 4 *
      ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) := continuous_const.mul hmc
  have hc12 : Continuous (fun t : ℝ => 8 * (∑ p ∈ Pof T, 2 * kap p.2) ^ 3 *
      (∑ p ∈ Pof T, 2 * kap p.2 *
        (‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4)) +
      8 * (64 * CP * ((Jof T : ℝ) + 1) + 3) ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) :=
    hc1.add hc2
  have hlc : Continuous (fun t : ℝ =>
      ‖Mol T (1 / 2 + (t : ℂ) * I) * riemannZeta (1 / 2 + (t : ℂ) * I)‖ ^ 4) :=
    (continuous_norm.comp ((Mol_cont T).mul zeta_cont)).pow 4
  -- the pointwise bound, integrated
  have step1 : ∫ t in (T / 2)..(3 * T),
        ‖Mol T (1 / 2 + (t : ℂ) * I) * riemannZeta (1 / 2 + (t : ℂ) * I)‖ ^ 4 ≤
      ∫ t in (T / 2)..(3 * T), (8 * (∑ p ∈ Pof T, 2 * kap p.2) ^ 3 *
          (∑ p ∈ Pof T, 2 * kap p.2 *
            (‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4)) +
        8 * (64 * CP * (Jof T + 1) + 3) ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) := by
    apply intervalIntegral.integral_mono_ae_restrict hTT (hlc.intervalIntegrable _ _)
      (hc12.intervalIntegrable _ _)
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (bad_countable.ae_notMem volume)] with t ht hb
    have ht509 : 509 ≤ t := by linarith [ht.1]
    have hgood : 0 < RSInt.rsFrac t ∧ Real.cos (2 * π * RSInt.rsFrac t) ≠ 0 := by
      by_contra hc
      exact hb ⟨ht509, hc⟩
    have h := zeta4_pointwise CP hCP.le hP T t hT ht.1 ht.2 hgood
    have hm : 0 ≤ ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 := by positivity
    have h' := mul_le_mul_of_nonneg_left h hm
    have e : ∑ p ∈ Pof T, 2 * kap p.2 *
        (‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) =
        (∑ p ∈ Pof T, 2 * kap p.2 * ‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4) *
          ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [norm_mul, mul_pow]
    refine h'.trans (le_of_eq ?_)
    rw [e]; ring
  -- each block
  have hR0 : 0 < Real.log T ^ |A₀| := Real.rpow_pos_of_pos hl0 _
  have hR1 : 1 ≤ Real.log T ^ |A₀| := Real.one_le_rpow hl (abs_nonneg _)
  have hblock : ∀ p ∈ Pof T, ∫ t in (T / 2)..(3 * T), ‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 *
      ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 ≤ 12 * |CG| * T * Real.log T ^ |A₀| := by
    intro p hp
    obtain ⟨h1, h2⟩ := shift_ok T (by linarith) p hp
    have hb := block_integral CG A₀ TG hG T hTG (by linarith) p.1 (π * p.2 / 2) h1 h2
    have hB : CG * Delta T * Real.log T ^ A₀ ≤ |CG| * Delta T * Real.log T ^ |A₀| := by
      have hr : Real.log T ^ A₀ ≤ Real.log T ^ |A₀| :=
        Real.rpow_le_rpow_of_exponent_le hl (le_abs_self _)
      have hr0 : 0 ≤ Real.log T ^ A₀ := (Real.rpow_pos_of_pos hl0 _).le
      calc CG * Delta T * Real.log T ^ A₀ ≤ |CG| * Delta T * Real.log T ^ A₀ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self _) hΔ.le) hr0
        _ ≤ |CG| * Delta T * Real.log T ^ |A₀| :=
            mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) hΔ.le)
    have hB0 : 0 ≤ |CG| * Delta T * Real.log T ^ |A₀| :=
      mul_nonneg (mul_nonneg (abs_nonneg _) hΔ.le) hR0.le
    have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hΔe : 4 * Real.log T * (|CG| * Delta T * Real.log T ^ |A₀|) =
        4 * |CG| * T * Real.log T ^ |A₀| := by
      unfold Delta; field_simp
    calc _ ≤ _ := hb
      _ ≤ Real.exp 1 * ((3 * Real.log T + 1) * (|CG| * Delta T * Real.log T ^ |A₀|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (by linarith))
            (Real.exp_pos _).le
      _ ≤ Real.exp 1 * (4 * Real.log T * (|CG| * Delta T * Real.log T ^ |A₀|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hB0)
            (Real.exp_pos _).le
      _ ≤ 3 * (4 * Real.log T * (|CG| * Delta T * Real.log T ^ |A₀|)) :=
          mul_le_mul_of_nonneg_right he3 (mul_nonneg (by linarith) hB0)
      _ = 12 * |CG| * T * Real.log T ^ |A₀| := by rw [hΔe]; ring
  have hMol := Mol_moment T (by linarith)
  have hMol0 : 0 ≤ ∫ t in (T / 2)..(3 * T), ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 :=
    intervalIntegral.integral_nonneg hTT (fun _ _ => by positivity)
  -- the integral of the majorant
  have step2 : ∫ t in (T / 2)..(3 * T), (8 * (∑ p ∈ Pof T, 2 * kap p.2) ^ 3 *
          (∑ p ∈ Pof T, 2 * kap p.2 *
            (‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4)) +
        8 * (64 * CP * (Jof T + 1) + 3) ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) ≤
      8 * (∑ p ∈ Pof T, 2 * kap p.2) ^ 3 *
          ((∑ p ∈ Pof T, 2 * kap p.2) * (12 * |CG| * T * Real.log T ^ |A₀|)) +
        8 * (64 * CP * (Jof T + 1) + 3) ^ 4 *
          ∫ t in (T / 2)..(3 * T), ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4 := by
    rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum
        (fun p _ => (hqc' p).intervalIntegrable _ _)]
    have : ∑ p ∈ Pof T, ∫ t in (T / 2)..(3 * T), 2 * kap p.2 *
        (‖Q (2 ^ p.1) (π * p.2 / 2 - t)‖ ^ 4 * ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) ≤
        (∑ p ∈ Pof T, 2 * kap p.2) * (12 * |CG| * T * Real.log T ^ |A₀|) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun p hp => ?_
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hblock p hp) (hw p hp)
    have h8 : 0 ≤ 8 * (∑ p ∈ Pof T, 2 * kap p.2) ^ 3 := by positivity
    linarith [mul_le_mul_of_nonneg_left this h8]
  -- numerics
  have hW4 : (∑ p ∈ Pof T, 2 * kap p.2) ^ 4 ≤ (36 * Real.log T ^ 2) ^ 4 :=
    pow_le_pow_left₀ hWt0 hWle 4
  have hE4 : (64 * CP * ((Jof T : ℝ) + 1) + 3) ^ 4 ≤ ((192 * CP + 3) * Real.log T) ^ 4 :=
    pow_le_pow_left₀ hE0 hEle 4
  have hG0 : 0 ≤ 12 * |CG| * T * Real.log T ^ |A₀| := by positivity
  have hterm1 : 8 * (∑ p ∈ Pof T, 2 * kap p.2) ^ 3 *
      ((∑ p ∈ Pof T, 2 * kap p.2) * (12 * |CG| * T * Real.log T ^ |A₀|)) ≤
      8 * (36 * Real.log T ^ 2) ^ 4 * (12 * |CG| * T * Real.log T ^ |A₀|) := by
    have := mul_le_mul_of_nonneg_right hW4 hG0
    nlinarith
  have hterm2 : 8 * (64 * CP * ((Jof T : ℝ) + 1) + 3) ^ 4 *
      (∫ t in (T / 2)..(3 * T), ‖Mol T (1 / 2 + (t : ℂ) * I)‖ ^ 4) ≤
      8 * ((192 * CP + 3) * Real.log T) ^ 4 * (5427 * T * Real.log T ^ 4) := by
    have := mul_le_mul hE4 hMol hMol0 (by positivity)
    linarith
  have hpow : Real.log T ^ (8 + |A₀|) = Real.log T ^ (8 : ℕ) * Real.log T ^ |A₀| := by
    rw [Real.rpow_add hl0, ← Real.rpow_natCast]
    norm_num
  have hX0 : 0 ≤ 8 * 5427 * (192 * CP + 3) ^ 4 * T * Real.log T ^ (8 : ℕ) := by positivity
  have hXR := le_mul_of_one_le_right hX0 hR1
  rw [hpow]
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ 8 * (36 * Real.log T ^ 2) ^ 4 * (12 * |CG| * T * Real.log T ^ |A₀|) +
          8 * ((192 * CP + 3) * Real.log T) ^ 4 * (5427 * T * Real.log T ^ 4) :=
        add_le_add hterm1 hterm2
    _ = 96 * 36 ^ 4 * |CG| * T * (Real.log T ^ (8 : ℕ) * Real.log T ^ |A₀|) +
          8 * 5427 * (192 * CP + 3) ^ 4 * T * Real.log T ^ (8 : ℕ) := by ring
    _ ≤ 96 * 36 ^ 4 * |CG| * T * (Real.log T ^ (8 : ℕ) * Real.log T ^ |A₀|) +
          8 * 5427 * (192 * CP + 3) ^ 4 * T * Real.log T ^ (8 : ℕ) * Real.log T ^ |A₀| := by
        linarith
    _ = _ := by ring

theorem target_of_propG (hG : PropG) :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      ∫ t in T / 2..3 * T,
          ‖M (1 / 2 + (t : ℂ) * Complex.I) * riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4 ≤
        C * T * Real.log T ^ A := by
  obtain ⟨CG, A₀, TG, hG⟩ := hG
  obtain ⟨CP, hCP, hP⟩ := GuthMaynard.norm_window_sum_le_perron
  refine ⟨8 + |A₀|, 96 * 36 ^ 4 * |CG| + 8 * 5427 * (192 * CP + 3) ^ 4, max TG 1018,
    fun T hT => ?_⟩
  exact main_bound CG A₀ TG hG CP hCP hP T (le_of_max_le_left hT) (le_of_max_le_right hT)

end
end GuthMaynard.Twisted.PartR
end

section
set_option autoImplicit false
namespace GuthMaynard.Twisted
open Finset
noncomputable section
/-! ## Part R: the reduction to Proposition G -/
alias target_of_propG := GuthMaynard.Twisted.PartR.target_of_propG

/-! ## Assembly -/
theorem main_dev :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      ∫ t in T / 2..3 * T,
          ‖M (1 / 2 + (t : ℂ) * Complex.I) * riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4 ≤
        C * T * Real.log T ^ A :=
  target_of_propG propG

end
end GuthMaynard.Twisted
end

section
set_option autoImplicit false
open GuthMaynard
open GuthMaynard.Twisted
open Finset
noncomputable section
theorem solution :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      ∫ t in T / 2..3 * T,
          ‖M (1 / 2 + (t : ℂ) * Complex.I) * riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4 ≤
        C * T * Real.log T ^ A := by
  exact GuthMaynard.Twisted.main_dev
end
end
