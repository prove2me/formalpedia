-- Prove2me | solution 1 for GuthMaynard.energy_le_of_large_values_of_two_thirds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:09:36.955149+00:00
-- url     : https://prove2.me/submissions/d7a351c5-f8b0-4ecc-a74e-792f5d826996

import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_heath_brown_large_values
import Mathlib

section
section
/-!
# Basic definitions

This module contains the definitions mentioned in the blueprint's Basic notation chapter
(`notation-chapter`).

When a blueprint convention already has a standard Mathlib representation,
prefer using that representation directly, for example:
-the notation `e(θ)` is `𝐞 θ` after `open scoped FourierTransform`;
-for indicator functions, use `Set.indicator`;
-for suprema and infima, including those of empty sets, use Mathlib's `sSup` and `sInf`;
-for finite cardinalities use `Finset.card`;
-/


namespace Expdb

end Expdb

end
end

section
section
/-!
# A normalized smooth bump and its Fourier transform

This module collects the concrete bump function used in the proof of the `L²` integral
estimate of the blueprint's Basic Fourier estimates chapter (`l2-chapter`), together with its
Fourier transform and the orthonormal family formed by its translates.

The bump `bump` is a fixed smooth, nonnegative, compactly supported function with
`‖bump‖_{L²} = 1` and support in `[-1/4, 1/4]`. Its translates by `1`-separated shifts are
therefore orthonormal, which is what the `L²` estimate uses.

These declarations are auxiliary to `Expdb.Fourier.L2Integral` and are collected in the
namespace `Expdb.L2Bump`.
-/


open MeasureTheory Real Complex Filter Topology BigOperators
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

namespace Expdb.L2Bump

/-! ## A normalized smooth bump -/

/-! ## Plancherel and decay of the bump's Fourier transform -/

/-! ## Weighted Plancherel identity -/

end Expdb.L2Bump

end

end
end

section
section
/-!
# `L²` integral estimate

This module formalizes the `L²` integral estimate from the blueprint's Basic Fourier estimates
chapter (`l2-chapter`).
It proves both the blueprint's equality with a bounded error coefficient
and the corresponding absolute-error bound.
-/


open MeasureTheory Real Complex Filter Topology BigOperators
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

namespace Expdb

open L2Bump

/-! ### The exponential sum -/

/-- The exponential sum with coefficients `a` and frequencies `ξ`, evaluated at `t`. -/
def expSum {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ r, a r * 𝐞 (ξ r * t)

/-- An exponential sum is continuous in its evaluation point. -/
@[fun_prop]
lemma expSum_continuous {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) :
    Continuous (expSum a ξ) := by
  unfold expSum
  fun_prop

/-! ### Local `L²` bound -/

/-! ### Smoothing identity -/

/-! ### Decay of the smoothing error -/

/-! ### Integrated smoothing-error bound -/

/-! ### `L²` integral estimate lemma -/

end Expdb

end

end
end

section
section
namespace GuthMaynard.S1

open MeasureTheory Set

lemma abs_intervalIntegral_le {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) {a b t t0 : ℝ}
    (hab : a ≤ b) (ht : t ∈ Set.Icc a b) (ht0 : t0 ∈ Set.Icc a b) :
    |∫ s in t..t0, h s| ≤ ∫ s in a..b, h s := by
  rcases le_total t t0 with hle | hle
  · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hle (fun x _ => h0 x))]
    exact intervalIntegral.integral_mono_interval ht.1 hle ht0.2
      (Filter.Eventually.of_forall h0) (hc.intervalIntegrable _ _)
  · rw [intervalIntegral.integral_symm, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg hle (fun x _ => h0 x))]
    exact intervalIntegral.integral_mono_interval ht0.1 hle ht.2
      (Filter.Eventually.of_forall h0) (hc.intervalIntegrable _ _)

/-- Pointwise Gallagher/Sobolev inequality on a unit window. -/
lemma sq_le_window {F F' : ℝ → ℂ} (hF : ∀ t, HasDerivAt F (F' t) t) (hFc : Continuous F)
    (hF'c : Continuous F') (t0 : ℝ) :
    ‖F t0‖ ^ 2 ≤ ∫ s in (t0 - 1/2)..(t0 + 1/2), (‖F s‖ ^ 2 + 2 * ‖F s‖ * ‖F' s‖) := by
  set g : ℝ → ℝ := fun t => ‖F t‖ ^ 2 with hg
  set h : ℝ → ℝ := fun t => 2 * ‖F t‖ * ‖F' t‖ with hh
  have hgd : ∀ t, HasDerivAt g (2 * inner ℝ (F t) (F' t)) t := fun t => (hF t).norm_sq
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hhc : Continuous h := by rw [hh]; fun_prop
  have hg'c : Continuous fun t => 2 * (inner ℝ (F t) (F' t) : ℝ) := by fun_prop
  have hle : ∀ t, |2 * (inner ℝ (F t) (F' t) : ℝ)| ≤ h t := by
    intro t
    rw [hh]; simp only
    rw [abs_mul, abs_two]
    have := abs_real_inner_le_norm (F t) (F' t)
    nlinarith [this]
  have h0 : ∀ t, 0 ≤ h t := fun t => by rw [hh]; positivity
  have hab : t0 - 1/2 ≤ t0 + 1/2 := by linarith
  have hpt : ∀ t ∈ Set.Icc (t0 - 1/2) (t0 + 1/2),
      g t0 ≤ g t + ∫ s in (t0 - 1/2)..(t0 + 1/2), h s := by
    intro t ht
    have h1 : g t0 - g t = ∫ s in t..t0, 2 * (inner ℝ (F s) (F' s) : ℝ) :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hgd s)
        (hg'c.intervalIntegrable _ _)).symm
    have h2 : |∫ s in t..t0, 2 * (inner ℝ (F s) (F' s) : ℝ)| ≤ |∫ s in t..t0, h s| := by
      have key : ∀ {x y : ℝ}, x ≤ y → |∫ s in x..y, 2 * (inner ℝ (F s) (F' s) : ℝ)| ≤
          ∫ s in x..y, h s := by
        intro x y hxy
        refine (intervalIntegral.abs_integral_le_integral_abs hxy).trans ?_
        exact intervalIntegral.integral_mono_on hxy
          (hg'c.abs.intervalIntegrable _ _) (hhc.intervalIntegrable _ _) (fun s _ => hle s)
      rcases le_total t t0 with hl | hl
      · exact (key hl).trans (le_abs_self _)
      · rw [intervalIntegral.integral_symm t0 t, intervalIntegral.integral_symm t0 t, abs_neg, abs_neg]
        exact (key hl).trans (le_abs_self _)
    have h4 := abs_intervalIntegral_le hhc h0 hab ht (t0 := t0) ⟨by linarith, by linarith⟩
    have := (le_abs_self _).trans (h2.trans h4)
    linarith
  have hgi : IntervalIntegrable g volume (t0 - 1/2) (t0 + 1/2) := hgc.intervalIntegrable _ _
  have hconst : ∫ s in (t0 - 1/2)..(t0 + 1/2), g t0 = g t0 := by
    simp; ring
  calc ‖F t0‖ ^ 2 = ∫ s in (t0 - 1/2)..(t0 + 1/2), g t0 := hconst.symm
    _ ≤ ∫ s in (t0 - 1/2)..(t0 + 1/2), (g s + ∫ s in (t0 - 1/2)..(t0 + 1/2), h s) := by
        apply intervalIntegral.integral_mono_on hab (by simp)
          (hgi.add (by simp))
        intro x hx; exact hpt x hx
    _ = ∫ s in (t0 - 1/2)..(t0 + 1/2), (g s + h s) := by
        rw [intervalIntegral.integral_add hgi (by simp)]
        rw [intervalIntegral.integral_add hgi (hhc.intervalIntegrable _ _)]
        simp; ring
    _ = _ := rfl

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard.S1

open MeasureTheory Set Complex
open scoped FourierTransform

/-- The normalised dyadic exponential sum `∑ a_n (n/N)^{it}`. -/
noncomputable def E (N : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * Complex.exp (((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I * (t : ℂ))

lemma E_continuous (N : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) : Continuous (E N s a) := by
  unfold E; fun_prop

lemma E_hasDerivAt (N : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (E N s a)
      (Complex.I * E N s (fun n => a n * ((Real.log ((n : ℝ) / N) : ℝ) : ℂ)) t) t := by
  unfold E
  have : ∀ n ∈ s, HasDerivAt
      (fun t : ℝ => a n * Complex.exp (((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I * (t : ℂ)))
      (a n * (((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I *
        Complex.exp (((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I * (t : ℂ)))) t := by
    intro n _
    have h0 : HasDerivAt (fun y : ℝ => Complex.exp ((((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I) * (y : ℂ)))
        (Complex.exp ((((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) *
          ((((Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I) * 1)) t :=
      (((hasDerivAt_id t).ofReal_comp).const_mul _).cexp
    refine (h0.const_mul (a n)).congr_deriv ?_
    ring
  refine (HasDerivAt.fun_sum this).congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma norm_S_eq (N : ℕ) (hN : 1 ≤ N) (s : Finset ℕ) (hs : s ⊆ Finset.Icc N (2 * N)) (c : ℕ → ℂ)
    (t : ℝ) :
    ‖∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = ‖E N s c t‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : ∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) =
      Complex.exp (((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ)) * E N s c t := by
    unfold E
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Icc.mp (hs hn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Complex.cpow_def_of_ne_zero hnc]
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
    rw [hlog]
    have : Real.log ((n : ℝ) / N) = Real.log n - Real.log N := Real.log_div hn0.ne' hN0.ne'
    rw [this]
    have e : Complex.exp (((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ)) *
        Complex.exp (((Real.log n - Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ)) =
        Complex.exp (((Real.log n : ℝ) : ℂ) * ((t : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc c n * Complex.exp (((Real.log n : ℝ) : ℂ) * ((t : ℂ) * Complex.I))
        = c n * (Complex.exp (((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ)) *
        Complex.exp (((Real.log n - Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ))) := by rw [e]
      _ = _ := by ring
  rw [this, norm_mul]
  have : ‖Complex.exp (((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
    rw [show ((Real.log N : ℝ) : ℂ) * Complex.I * (t : ℂ) = ((Real.log N * t : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this, one_mul]

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard.S1

open Complex

/-- `n^{it}` written as an exponential. -/
noncomputable def chi (n : ℕ) (t : ℝ) : ℂ := Complex.exp (((Real.log n : ℝ) : ℂ) * Complex.I * (t : ℂ))

lemma cpow_eq_chi {n : ℕ} (hn : 0 < n) (t : ℝ) : (n : ℂ) ^ ((t : ℂ) * Complex.I) = chi n t := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hnc]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
  rw [hlog, chi]; congr 1; ring

lemma norm_chi (n : ℕ) (t : ℝ) : ‖chi n t‖ = 1 := by
  rw [chi, show ((Real.log n : ℝ) : ℂ) * Complex.I * (t : ℂ) = ((Real.log n * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma chi_neg (n : ℕ) (t : ℝ) : chi n (-t) = (starRingEnd ℂ) (chi n t) := by
  rw [chi, chi, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

lemma chi_add (n : ℕ) (a b : ℝ) : chi n (a + b) = chi n a * chi n b := by
  rw [chi, chi, chi, ← Complex.exp_add]; congr 1; push_cast; ring

lemma chi_four (n : ℕ) (a b c d : ℝ) :
    chi n (a + b - c - d) = chi n a * chi n b * (starRingEnd ℂ) (chi n c) * (starRingEnd ℂ) (chi n d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, chi_add, chi_add, chi_add, chi_neg, chi_neg]

/-- the pair correlation `R(n₁/n₂) = ∑_{t ∈ W} (n₁/n₂)^{it}` -/
noncomputable def Pn (W : Finset ℝ) (n₁ n₂ : ℕ) : ℂ :=
  ∑ t ∈ W, chi n₁ t * (starRingEnd ℂ) (chi n₂ t)

lemma sum_swap3 {α β γ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (f : α → β → γ → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ b ∈ B, ∑ c ∈ C, ∑ a ∈ A, f a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma sum_swap5 {α β γ δ ε : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (E : Finset ε) (f : α → β → γ → δ → ε → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, f a b c d e =
      ∑ d ∈ D, ∑ e ∈ E, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c d e := by
  have h1 : ∀ a b, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, f a b c d e = ∑ d ∈ D, ∑ e ∈ E, ∑ c ∈ C, f a b c d e :=
    fun a b => sum_swap3 C D E (f a b)
  simp_rw [h1]
  have h2 : ∀ a, ∑ b ∈ B, ∑ d ∈ D, ∑ e ∈ E, ∑ c ∈ C, f a b c d e =
      ∑ d ∈ D, ∑ e ∈ E, ∑ b ∈ B, ∑ c ∈ C, f a b c d e :=
    fun a => sum_swap3 B D E (fun b d e => ∑ c ∈ C, f a b c d e)
  simp_rw [h2]
  exact sum_swap3 A D E (fun a d e => ∑ b ∈ B, ∑ c ∈ C, f a b c d e)

lemma triple_eq (W : Finset ℝ) (n₁ n₂ : ℕ) (σ' : ℝ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      (chi n₁ (t₁ + t₂ - t₃ - σ') * (starRingEnd ℂ) (chi n₂ (t₁ + t₂ - t₃ - σ'))) =
    ((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
      (Pn W n₁ n₂ * Pn W n₁ n₂ * (starRingEnd ℂ) (Pn W n₁ n₂)) := by
  have hterm : ∀ t₁ t₂ t₃ : ℝ, chi n₁ (t₁ + t₂ - t₃ - σ') * (starRingEnd ℂ) (chi n₂ (t₁ + t₂ - t₃ - σ')) =
      ((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
        ((chi n₁ t₁ * (starRingEnd ℂ) (chi n₂ t₁)) * (chi n₁ t₂ * (starRingEnd ℂ) (chi n₂ t₂)) *
          (starRingEnd ℂ) (chi n₁ t₃ * (starRingEnd ℂ) (chi n₂ t₃))) := by
    intro t₁ t₂ t₃
    rw [chi_four, chi_four]
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [hterm]
  set q : ℝ → ℂ := fun t => chi n₁ t * (starRingEnd ℂ) (chi n₂ t) with hq
  set u : ℂ := (starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ' with hu
  have hP : Pn W n₁ n₂ = ∑ t ∈ W, q t := rfl
  have hcP : (starRingEnd ℂ) (Pn W n₁ n₂) = ∑ t ∈ W, (starRingEnd ℂ) (q t) := by
    rw [hP, map_sum]
  rw [hcP, hP]
  have h3 : ((∑ t ∈ W, q t) * ∑ t ∈ W, q t) * ∑ t ∈ W, (starRingEnd ℂ) (q t) =
      ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, q x * q y * (starRingEnd ℂ) (q z) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  rw [h3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]

/-- The triple sum of `|D|²` at shifted points is bounded by the third moment of `R`. -/
lemma triple_sum_le (W : Finset ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (hc : ∀ n ∈ s, ‖c n‖ ≤ 1) (σ' : ℝ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ s, c n * chi n (t₁ + t₂ - t₃ - σ')‖ ^ 2 ≤
      ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 3 := by
  have hsq : ∀ y : ℝ, (((‖∑ n ∈ s, c n * chi n y‖ ^ 2 : ℝ)) : ℂ) =
      ∑ n₁ ∈ s, ∑ n₂ ∈ s, c n₁ * (starRingEnd ℂ) (c n₂) * (chi n₁ y * (starRingEnd ℂ) (chi n₂ y)) := by
    intro y
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    rw [map_mul]; ring
  have hZ : ((∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ s, c n * chi n (t₁ + t₂ - t₃ - σ')‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ s, ∑ n₂ ∈ s, c n₁ * (starRingEnd ℂ) (c n₂) *
        (((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
        (Pn W n₁ n₂ * Pn W n₁ n₂ * (starRingEnd ℂ) (Pn W n₁ n₂))) := by
    simp only [Complex.ofReal_sum]
    simp only [hsq]
    rw [sum_swap5]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    rw [← triple_eq W n₁ n₂ σ']
    simp only [Finset.mul_sum]
  set Z := ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ s, c n * chi n (t₁ + t₂ - t₃ - σ')‖ ^ 2 with hZdef
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc Z = ‖(Z : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hZ0]
    _ = ‖∑ n₁ ∈ s, ∑ n₂ ∈ s, c n₁ * (starRingEnd ℂ) (c n₂) *
        (((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
        (Pn W n₁ n₂ * Pn W n₁ n₂ * (starRingEnd ℂ) (Pn W n₁ n₂)))‖ := by rw [hZ]
    _ ≤ ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖c n₁ * (starRingEnd ℂ) (c n₂) *
        (((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
        (Pn W n₁ n₂ * Pn W n₁ n₂ * (starRingEnd ℂ) (Pn W n₁ n₂)))‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n₁ _ => norm_sum_le _ _)
    _ ≤ ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 3 := by
        refine Finset.sum_le_sum fun n₁ h₁ => Finset.sum_le_sum fun n₂ h₂ => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj,
          Complex.norm_conj, Complex.norm_conj, norm_chi, norm_chi]
        have a1 := hc n₁ h₁
        have a2 := hc n₂ h₂
        have hP0 := norm_nonneg (Pn W n₁ n₂)
        calc ‖c n₁‖ * ‖c n₂‖ * (1 * 1 * (‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖)) ≤
            1 * 1 * (1 * 1 * (‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖)) := by gcongr
          _ = _ := by ring

lemma sum_swap4 {α β γ δ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d = ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  have h1 : ∀ a, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d = ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, f a b c d :=
    fun a => sum_swap3 B C D (f a)
  simp_rw [h1]
  exact sum_swap3 A C D (fun a c d => ∑ b ∈ B, f a b c d)

lemma chi_sub (n : ℕ) (a b : ℝ) : chi n (a - b) = chi n a * (starRingEnd ℂ) (chi n b) := by
  rw [sub_eq_add_neg, chi_add, chi_neg]

/-- Second moment of `R` equals the Heath-Brown sum. -/
lemma second_moment_eq (W : Finset ℝ) (s : Finset ℕ) :
    ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 2 = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖∑ n ∈ s, chi n (t₁ - t₂)‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  have h1 : ∀ n₁ n₂ : ℕ, ((‖Pn W n₁ n₂‖ : ℝ) : ℂ) ^ 2 =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, (chi n₁ (t₁ - t₂) * (starRingEnd ℂ) (chi n₂ (t₁ - t₂))) := by
    intro n₁ n₂
    rw [← Complex.mul_conj', Pn, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => ?_
    rw [chi_sub, chi_sub]
    simp only [map_mul, Complex.conj_conj]
    ring
  have h2 : ∀ t₁ t₂ : ℝ, ((‖∑ n ∈ s, chi n (t₁ - t₂)‖ : ℝ) : ℂ) ^ 2 =
      ∑ n₁ ∈ s, ∑ n₂ ∈ s, (chi n₁ (t₁ - t₂) * (starRingEnd ℂ) (chi n₂ (t₁ - t₂))) := by
    intro t₁ t₂
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  simp_rw [h1, h2]
  exact (sum_swap4 W W s s _).symm

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard.S1

open MeasureTheory Set

lemma card_near_le_three (W : Finset ℝ) (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) (x : ℝ) :
    (W.filter (fun t => |x - t| ≤ 1)).card ≤ 3 := by
  have : (W.filter (fun t => |x - t| ≤ 1)).card ≤ (Finset.Icc (0 : ℤ) 2).card := by
    apply Finset.card_le_card_of_injOn (fun t => ⌊t - x + 1⌋)
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at ht
      have h := abs_le.mp ht.2
      simp only [Finset.coe_Icc, Set.mem_Icc]
      constructor
      · apply Int.floor_nonneg.mpr; linarith [h.1, h.2]
      · have : ⌊t - x + 1⌋ < 3 := by
          rw [Int.floor_lt]; push_cast; linarith [h.1, h.2]
        omega
    · intro t ht t' ht' h
      simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at ht ht'
      by_contra hne
      have h1 := hsep t ht.1 t' ht'.1 hne
      have a1 := Int.floor_le (t - x + 1)
      have a2 := Int.lt_floor_add_one (t - x + 1)
      have b1 := Int.floor_le (t' - x + 1)
      have b2 := Int.lt_floor_add_one (t' - x + 1)
      have h' : ⌊t - x + 1⌋ = ⌊t' - x + 1⌋ := h
      rw [h'] at a1 a2
      have : |t - t'| < 1 := by
        rw [abs_lt]; constructor <;> linarith
      linarith
  simpa using this

/-- the Dirichlet polynomial with coefficients `c` on `s`, in exponential form -/
noncomputable def Sc (s : Finset ℕ) (c : ℕ → ℂ) (u : ℝ) : ℂ := ∑ n ∈ s, c n * chi n u

lemma Sc_continuous (s : Finset ℕ) (c : ℕ → ℂ) : Continuous (Sc s c) := by
  unfold Sc chi; fun_prop

lemma norm_Sc (N : ℕ) (hN : 1 ≤ N) (s : Finset ℕ) (hs : s ⊆ Finset.Icc N (2 * N)) (c : ℕ → ℂ)
    (u : ℝ) : ‖Sc s c u‖ = ‖E N s c u‖ := by
  rw [← norm_S_eq N hN s hs c u]
  unfold Sc
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have := (Finset.mem_Icc.mp (hs hn)).1
  rw [cpow_eq_chi (by omega)]

lemma window_Sc (N : ℕ) (hN : 1 ≤ N) (s : Finset ℕ) (hs : s ⊆ Finset.Icc N (2 * N)) (c : ℕ → ℂ)
    (t : ℝ) :
    ‖Sc s c t‖ ^ 2 ≤ ∫ u in (t - 1/2)..(t + 1/2),
      (2 * ‖Sc s c u‖ ^ 2 + ‖Sc s (fun n => c n * ((Real.log ((n : ℝ) / N) : ℝ) : ℂ)) u‖ ^ 2) := by
  set c' : ℕ → ℂ := fun n => c n * ((Real.log ((n : ℝ) / N) : ℝ) : ℂ) with hc'
  set F := E N s c
  set F' : ℝ → ℂ := fun t => Complex.I * E N s c' t with hF'
  have hFd : ∀ t, HasDerivAt F (F' t) t := fun t => E_hasDerivAt N s c t
  have hFc : Continuous F := E_continuous N s c
  have hF'c : Continuous F' := by rw [hF']; have := E_continuous N s c'; fun_prop
  have hnF' : ∀ x, ‖F' x‖ = ‖Sc s c' x‖ := fun x => by rw [hF', norm_mul, norm_Sc N hN s hs]; simp
  have hnF : ∀ x, ‖F x‖ = ‖Sc s c x‖ := fun x => (norm_Sc N hN s hs c x).symm
  rw [← hnF t]
  refine (sq_le_window hFd hFc hF'c t).trans ?_
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (by fun_prop : Continuous fun x => ‖F x‖ ^ 2 + 2 * ‖F x‖ * ‖F' x‖).intervalIntegrable _ _
  · have := Sc_continuous s c
    have := Sc_continuous s c'
    exact (by fun_prop : Continuous fun x => 2 * ‖Sc s c x‖ ^ 2 + ‖Sc s c' x‖ ^ 2).intervalIntegrable _ _
  · intro x _
    rw [hnF', hnF]
    nlinarith [sq_nonneg (‖Sc s c x‖ - ‖Sc s c' x‖)]

lemma log_ratio_mem {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ Finset.Icc N (2 * N)) :
    0 ≤ Real.log ((n : ℝ) / N) ∧ Real.log ((n : ℝ) / N) ≤ 1 := by
  have hn' := Finset.mem_Icc.mp hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn'.1
  have h2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn'.2
  refine ⟨Real.log_nonneg ((one_le_div hN0).mpr h1), ?_⟩
  have : Real.log ((n : ℝ) / N) ≤ Real.log 2 := Real.log_le_log (div_pos (by linarith) hN0)
    ((div_le_iff₀ hN0).mpr (by linarith))
  have h2' := Real.log_two_lt_d9
  linarith

/-- The key bound: the additive energy is controlled by the third moment of `R`. -/
lemma energy_mul_le (N : ℕ) (hN : 1 ≤ N) (σ : ℝ) (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1) (W : Finset ℝ)
    (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|)
    (hlarge : ∀ t ∈ W, (N : ℝ) ^ σ <
      ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) :
    (GuthMaynard.energy W : ℝ) * ((N : ℝ) ^ σ) ^ 2 ≤
      27 * ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N), ‖Pn W n₁ n₂‖ ^ 3 := by
  set s := Finset.Ioc N (2 * N) with hs_def
  have hs : s ⊆ Finset.Icc N (2 * N) := Finset.Ioc_subset_Icc_self
  set b' : ℕ → ℂ := fun n => b n * ((Real.log ((n : ℝ) / N) : ℝ) : ℂ) with hb'
  have hb'1 : ∀ n ∈ s, ‖b' n‖ ≤ 1 := by
    intro n hn
    obtain ⟨h0, h1⟩ := log_ratio_mem hN (hs hn)
    simp only [hb']
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    have := hb n
    have := norm_nonneg (b n)
    nlinarith
  set K := ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 3 with hK
  set G : ℝ → ℝ := fun u => 2 * ‖Sc s b u‖ ^ 2 + ‖Sc s b' u‖ ^ 2 with hG
  have hGc : Continuous G := by
    have := Sc_continuous s b
    have := Sc_continuous s b'
    rw [hG]; fun_prop
  have hG0 : ∀ u, 0 ≤ G u := fun u => by rw [hG]; positivity
  -- pointwise bound of the triple sum of G
  have hpt : ∀ σ' : ℝ, ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - σ') ≤ 3 * K := by
    intro σ'
    have e1 := triple_sum_le W s b (fun n _ => hb n) σ'
    have e2 := triple_sum_le W s b' hb'1 σ'
    have : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - σ') =
        2 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ s, b n * chi n (t₁ + t₂ - t₃ - σ')‖ ^ 2 +
        ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ s, b' n * chi n (t₁ + t₂ - t₃ - σ')‖ ^ 2 := by
      simp only [hG, Sc, Finset.sum_add_distrib, Finset.mul_sum]
    rw [this]; linarith
  -- H(y)
  set H : ℝ → ℝ := fun y => ∫ x in (y - 3/2)..(y + 3/2), G x with hH
  have hH0 : ∀ y, 0 ≤ H y := fun y =>
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => hG0 x)
  have hHeq : ∀ y, H y = ∫ x in (-3/2 : ℝ)..(3/2), G (y - x) := by
    intro y
    rw [intervalIntegral.integral_comp_sub_left (fun x => G x) y]
    simp only [hH]
    congr 1 <;> ring
  have hsum_H : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, H (t₁ + t₂ - t₃) ≤ 9 * K := by
    simp_rw [hHeq]
    have hc3 : ∀ t₁ t₂ t₃ : ℝ, Continuous fun x : ℝ => G (t₁ + t₂ - t₃ - x) := fun t₁ t₂ t₃ =>
      hGc.comp (continuous_const.sub continuous_id)
    have e3 : ∀ t₁ t₂ : ℝ, ∑ t₃ ∈ W, ∫ x in (-3/2 : ℝ)..(3/2), G (t₁ + t₂ - t₃ - x) =
        ∫ x in (-3/2 : ℝ)..(3/2), ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - x) := fun t₁ t₂ =>
      (intervalIntegral.integral_finset_sum (fun t₃ _ => (hc3 t₁ t₂ t₃).intervalIntegrable _ _)).symm
    have e2 : ∀ t₁ : ℝ, ∑ t₂ ∈ W, ∫ x in (-3/2 : ℝ)..(3/2), ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - x) =
        ∫ x in (-3/2 : ℝ)..(3/2), ∑ t₂ ∈ W, ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - x) := fun t₁ =>
      (intervalIntegral.integral_finset_sum (fun t₂ _ =>
        (continuous_finset_sum _ fun t₃ _ => hc3 t₁ t₂ t₃).intervalIntegrable _ _)).symm
    have e1 : ∑ t₁ ∈ W, ∫ x in (-3/2 : ℝ)..(3/2), ∑ t₂ ∈ W, ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - x) =
        ∫ x in (-3/2 : ℝ)..(3/2), ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - x) :=
      (intervalIntegral.integral_finset_sum (fun t₁ _ =>
        (continuous_finset_sum _ fun t₂ _ => continuous_finset_sum _ fun t₃ _ =>
          hc3 t₁ t₂ t₃).intervalIntegrable _ _)).symm
    have e0 : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∫ x in (-3/2 : ℝ)..(3/2), G (t₁ + t₂ - t₃ - x) =
        ∫ x in (-3/2 : ℝ)..(3/2), ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - x) := by
      rw [← e1]
      refine Finset.sum_congr rfl fun t₁ _ => ?_
      rw [← e2]
      exact Finset.sum_congr rfl fun t₂ _ => e3 t₁ t₂
    rw [e0]
    calc ∫ x in (-3/2 : ℝ)..(3/2), ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, G (t₁ + t₂ - t₃ - x)
        ≤ ∫ x in (-3/2 : ℝ)..(3/2), 3 * K := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · exact (continuous_finset_sum _ fun t₁ _ => continuous_finset_sum _ fun t₂ _ =>
              continuous_finset_sum _ fun t₃ _ => hc3 t₁ t₂ t₃).intervalIntegrable _ _
          · exact intervalIntegrable_const
          · intro x _; exact hpt x
      _ = 9 * K := by simp; ring
  have hlow : ∀ t ∈ W, ((N : ℝ) ^ σ) ^ 2 ≤ ‖Sc s b t‖ ^ 2 := by
    intro t ht
    have h1 := hlarge t ht
    have h2 : ‖∑ n ∈ s, b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = ‖Sc s b t‖ := by
      unfold Sc
      congr 1
      refine Finset.sum_congr rfl fun n hn => ?_
      have := (Finset.mem_Icc.mp (hs hn)).1
      rw [cpow_eq_chi (by omega)]
    rw [h2] at h1
    have h0 : 0 ≤ (N : ℝ) ^ σ := by positivity
    nlinarith
  -- bound on the inner sums over `t₄`
  have hinner : ∀ t₁ t₂ t₃ : ℝ,
      ∑ t₄ ∈ W.filter (fun t₄ => |t₁ + t₂ - t₃ - t₄| ≤ 1), ‖Sc s b t₄‖ ^ 2 ≤ 3 * H (t₁ + t₂ - t₃) := by
    intro t₁ t₂ t₃
    have hcard := card_near_le_three W hsep (t₁ + t₂ - t₃)
    have hterm : ∀ t₄ ∈ W.filter (fun t₄ => |t₁ + t₂ - t₃ - t₄| ≤ 1),
        ‖Sc s b t₄‖ ^ 2 ≤ H (t₁ + t₂ - t₃) := by
      intro t₄ ht₄
      have hc := (Finset.mem_filter.mp ht₄).2
      have hab := abs_le.mp hc
      refine (window_Sc N hN s hs b t₄).trans ?_
      have : ∫ u in (t₄ - 1/2)..(t₄ + 1/2), (2 * ‖Sc s b u‖ ^ 2 + ‖Sc s b' u‖ ^ 2) ≤ H (t₁ + t₂ - t₃) := by
        simp only [hH]
        exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Filter.Eventually.of_forall hG0) (hGc.intervalIntegrable _ _)
      exact this
    calc ∑ t₄ ∈ W.filter (fun t₄ => |t₁ + t₂ - t₃ - t₄| ≤ 1), ‖Sc s b t₄‖ ^ 2
        ≤ ∑ t₄ ∈ W.filter (fun t₄ => |t₁ + t₂ - t₃ - t₄| ≤ 1), H (t₁ + t₂ - t₃) :=
          Finset.sum_le_sum hterm
      _ = (W.filter (fun t₄ => |t₁ + t₂ - t₃ - t₄| ≤ 1)).card * H (t₁ + t₂ - t₃) := by simp
      _ ≤ 3 * H (t₁ + t₂ - t₃) := by
          apply mul_le_mul_of_nonneg_right _ (hH0 _)
          exact_mod_cast hcard
  unfold GuthMaynard.energy
  have hq : (((W ×ˢ W ×ˢ W ×ˢ W).filter fun p : ℝ × ℝ × ℝ × ℝ => |p.1 + p.2.1 - p.2.2.1 - p.2.2.2| ≤ 1).card : ℝ) *
      ((N : ℝ) ^ σ) ^ 2 ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ∑ t₄ ∈ W.filter (fun t₄ => |t₁ + t₂ - t₃ - t₄| ≤ 1), ‖Sc s b t₄‖ ^ 2 := by
    have e : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ∑ t₄ ∈ W.filter (fun t₄ => |t₁ + t₂ - t₃ - t₄| ≤ 1), ‖Sc s b t₄‖ ^ 2 =
        ∑ p ∈ (W ×ˢ W ×ˢ W ×ˢ W).filter (fun p : ℝ × ℝ × ℝ × ℝ => |p.1 + p.2.1 - p.2.2.1 - p.2.2.2| ≤ 1),
          ‖Sc s b p.2.2.2‖ ^ 2 := by
      rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun t₁ _ => ?_
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun t₂ _ => ?_
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun t₃ _ => ?_
      rw [Finset.sum_filter]
    rw [e]
    calc _ = ∑ p ∈ (W ×ˢ W ×ˢ W ×ˢ W).filter (fun p : ℝ × ℝ × ℝ × ℝ => |p.1 + p.2.1 - p.2.2.1 - p.2.2.2| ≤ 1),
            ((N : ℝ) ^ σ) ^ 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).1
        simp only [Finset.mem_product] at hp'
        exact hlow _ hp'.2.2.2
  refine hq.trans ?_
  calc _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, 3 * H (t₁ + t₂ - t₃) :=
        Finset.sum_le_sum fun t₁ _ => Finset.sum_le_sum fun t₂ _ => Finset.sum_le_sum fun t₃ _ =>
          hinner t₁ t₂ t₃
    _ = 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, H (t₁ + t₂ - t₃) := by
        simp only [Finset.mul_sum]
    _ ≤ 3 * (9 * K) := by linarith
    _ = 27 * K := by ring

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard

open S1

lemma term3 (x N T : ℝ) (hx : 0 ≤ x) (hT : 0 < T) (hN : T ^ (2 / 3 : ℝ) ≤ N) :
    x ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N ≤ x ^ 2 * N + x * N ^ 2 := by
  have hT23 : 0 < T ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hT _
  have hN0 : 0 ≤ N := hT23.le.trans hN
  rcases le_or_gt (T ^ (2 / 3 : ℝ)) x with h | h
  · have hxpos : 0 < x := lt_of_lt_of_le hT23 h
    have h1 : T ^ (1 / 2 : ℝ) ≤ x ^ (3 / 4 : ℝ) := by
      calc T ^ (1 / 2 : ℝ) = (T ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
            rw [← Real.rpow_mul hT.le]; norm_num
        _ ≤ x ^ (3 / 4 : ℝ) := Real.rpow_le_rpow hT23.le h (by norm_num)
    have h2 : x ^ (5 / 4 : ℝ) * x ^ (3 / 4 : ℝ) = x ^ 2 := by
      rw [← Real.rpow_add hxpos]; norm_num
    have h3 : x ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) ≤ x ^ 2 := by
      calc _ ≤ x ^ (5 / 4 : ℝ) * x ^ (3 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx _)
        _ = x ^ 2 := h2
    have : x ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N ≤ x ^ 2 * N := mul_le_mul_of_nonneg_right h3 hN0
    nlinarith [mul_nonneg hx (sq_nonneg N)]
  · have h1 : x ^ (1 / 4 : ℝ) ≤ T ^ (1 / 6 : ℝ) := by
      calc x ^ (1 / 4 : ℝ) ≤ (T ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow hx h.le (by norm_num)
        _ = T ^ (1 / 6 : ℝ) := by rw [← Real.rpow_mul hT.le]; norm_num
    have h2 : T ^ (1 / 6 : ℝ) * T ^ (1 / 2 : ℝ) = T ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hT]; norm_num
    have h3 : x ^ (5 / 4 : ℝ) = x * x ^ (1 / 4 : ℝ) := by
      rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one]
    have h4 : x ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) ≤ N := by
      calc _ ≤ T ^ (1 / 6 : ℝ) * T ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hT.le _)
        _ = T ^ (2 / 3 : ℝ) := h2
        _ ≤ N := hN
    calc x ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N = x * (x ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) * N := by
          rw [h3]; ring
      _ ≤ x * N * N := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hx (sq_nonneg N), sq_nonneg x, mul_nonneg (sq_nonneg x) hN0]

theorem chk_energy_le_of_large_values_of_two_thirds :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (2 / 3 : ℝ)) T → ∀ σ : ℝ, 1 / 2 < σ → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ, IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      (∀ t ∈ W, (N : ℝ) ^ σ <
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (energy W : ℝ) ≤ (W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ + ε) +
        (W.card : ℝ) ^ 2 * (N : ℝ) ^ (2 - 2 * σ + ε) := by
  intro ε hε
  obtain ⟨δ, hδ, T₁, hHB⟩ := heath_brown_large_values (ε / 3) (by positivity)
  refine ⟨max T₁ (max 2 ((54 : ℝ) ^ (3 / ε))), ?_⟩
  intro T hT N hN σ hσ b hb W hsep hWT hlarge
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT2 : 2 ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT54 : (54 : ℝ) ^ (3 / ε) ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hT0 : 0 < T := by linarith
  have hTe : (54 : ℝ) ≤ T ^ (ε / 3) := by
    calc (54 : ℝ) = ((54 : ℝ) ^ (3 / ε)) ^ (ε / 3) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ T ^ (ε / 3) := Real.rpow_le_rpow (by positivity) hT54 (by positivity)
  obtain ⟨hNlo, hNhi⟩ := hN
  have hT23 : 1 ≤ T ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hN1r : (1 : ℝ) ≤ N := hT23.trans hNlo
  have hN1 : 1 ≤ N := by exact_mod_cast hN1r
  have hN0 : (0 : ℝ) < N := by linarith
  set x : ℝ := (W.card : ℝ) with hx
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  -- step 1
  have h1 := energy_mul_le N hN1 σ b hb W hsep hlarge
  -- step 2: K ≤ x * (second moment)
  set s := Finset.Ioc N (2 * N) with hs_def
  have hPn : ∀ n₁ n₂, ‖Pn W n₁ n₂‖ ≤ x := by
    intro n₁ n₂
    calc ‖Pn W n₁ n₂‖ ≤ ∑ t ∈ W, ‖chi n₁ t * (starRingEnd ℂ) (chi n₂ t)‖ := norm_sum_le _ _
      _ = x := by
        simp [norm_mul, norm_chi, Complex.norm_conj, hx]
  have hK : ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 3 ≤
      x * ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n₂ _ => ?_
    have := hPn n₁ n₂
    have h0 := norm_nonneg (Pn W n₁ n₂)
    calc ‖Pn W n₁ n₂‖ ^ 3 = ‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖ ^ 2 := by ring
      _ ≤ x * ‖Pn W n₁ n₂‖ ^ 2 := by gcongr
  -- step 3: Heath-Brown
  have hHB' := hHB T hT1 N hN1 (fun n => if N < n then (1 : ℂ) else 0)
    (fun n => by
      have : (1 : ℝ) ≤ T ^ δ := Real.one_le_rpow (by linarith) hδ.le
      split_ifs <;> simp <;> linarith) W 0 hsep
    (fun t ht => by have := hWT t ht; simpa using this)
  have hsecond : ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 2 ≤
      T ^ (ε / 3) * (x ^ 2 * N + x * (N : ℝ) ^ 2 + x ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) := by
    rw [second_moment_eq]
    refine le_trans (le_of_eq ?_) hHB'
    refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => ?_
    congr 2
    have : ∀ n ∈ Finset.Icc N (2 * N), (if N < n then (1 : ℂ) else 0) * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * Complex.I) =
        if n ∈ s then chi n (t₁ - t₂) else 0 := by
      intro n hnI
      have hnI' := Finset.mem_Icc.mp hnI
      by_cases hn : N < n
      · have : n ∈ s := by simp [hs_def, Finset.mem_Ioc]; omega
        rw [if_pos hn, if_pos this, one_mul, cpow_eq_chi (by omega)]
      · have : n ∉ s := by simp [hs_def, Finset.mem_Ioc]; omega
        rw [if_neg hn, if_neg this, zero_mul]
    rw [Finset.sum_congr rfl this]
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [hs_def, Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
    omega
  have h3 := term3 x N T hx0 hT0 hNlo
  -- combine
  have hNσ : 0 < (N : ℝ) ^ (2 * σ) := by positivity
  have hpow : ((N : ℝ) ^ σ) ^ 2 = (N : ℝ) ^ (2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  rw [hpow] at h1
  have hTe0 : 0 < T ^ (ε / 3) := by positivity
  have hB : ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 2 ≤
      T ^ (ε / 3) * (2 * (x ^ 2 * N) + 2 * (x * (N : ℝ) ^ 2)) := by
    refine hsecond.trans ?_
    apply mul_le_mul_of_nonneg_left _ hTe0.le
    linarith
  have hE : (energy W : ℝ) * (N : ℝ) ^ (2 * σ) ≤ 54 * T ^ (ε / 3) * (x ^ 3 * N + x ^ 2 * (N : ℝ) ^ 2) := by
    calc (energy W : ℝ) * (N : ℝ) ^ (2 * σ) ≤ 27 * ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 3 := h1
      _ ≤ 27 * (x * ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 2) := by gcongr
      _ ≤ 27 * (x * (T ^ (ε / 3) * (2 * (x ^ 2 * N) + 2 * (x * (N : ℝ) ^ 2)))) := by gcongr
      _ = _ := by ring
  have hNe : 54 * T ^ (ε / 3) ≤ (N : ℝ) ^ ε := by
    calc 54 * T ^ (ε / 3) ≤ T ^ (ε / 3) * T ^ (ε / 3) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hTe hTe0.le
      _ = (T ^ (2 / 3 : ℝ)) ^ ε := by
          rw [← Real.rpow_add hT0, ← Real.rpow_mul hT0.le]; congr 1; ring
      _ ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hNlo hε.le
  have hexp1 : (N : ℝ) ^ (1 - 2 * σ + ε) * (N : ℝ) ^ (2 * σ) = N * (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hN0]
    have : (1 - 2 * σ + ε + 2 * σ) = 1 + ε := by ring
    rw [this, Real.rpow_add hN0, Real.rpow_one]
  have hexp2 : (N : ℝ) ^ (2 - 2 * σ + ε) * (N : ℝ) ^ (2 * σ) = (N : ℝ) ^ 2 * (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hN0]
    have : (2 - 2 * σ + ε + 2 * σ) = (2 : ℕ) + ε := by push_cast; ring
    rw [this, Real.rpow_add hN0, Real.rpow_natCast]
  refine le_of_mul_le_mul_right ?_ hNσ
  calc (energy W : ℝ) * (N : ℝ) ^ (2 * σ) ≤ 54 * T ^ (ε / 3) * (x ^ 3 * N + x ^ 2 * (N : ℝ) ^ 2) := hE
    _ ≤ (N : ℝ) ^ ε * (x ^ 3 * N + x ^ 2 * (N : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_right hNe; positivity
    _ = (x ^ 3 * (N : ℝ) ^ (1 - 2 * σ + ε) + x ^ 2 * (N : ℝ) ^ (2 - 2 * σ + ε)) * (N : ℝ) ^ (2 * σ) := by
        rw [add_mul, mul_assoc, mul_assoc, hexp1, hexp2]; ring

alias energy_le_of_large_values_of_two_thirds_dev := chk_energy_le_of_large_values_of_two_thirds

end GuthMaynard

end
end

section
open GuthMaynard

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (2 / 3 : ℝ)) T → ∀ σ : ℝ, 1 / 2 < σ → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ, IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      (∀ t ∈ W, (N : ℝ) ^ σ <
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (energy W : ℝ) ≤ (W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ + ε) +
        (W.card : ℝ) ^ 2 * (N : ℝ) ^ (2 - 2 * σ + ε) := by
  apply GuthMaynard.energy_le_of_large_values_of_two_thirds_dev <;> assumption

end
