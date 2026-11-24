-- Prove2me | solution 1 for HermitekLEAN.phi_polar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:52.407874+00:00
-- url     : https://prove2.me/submissions/26d8ce6c-5fe2-4640-bead-e60e0b7c6610

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private lemma fourier_one_pow (n : ℕ) (t : Circle) :
    ((fourier (1 : ℤ) t : ℂ) ^ n) = fourier (n : ℤ) t := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, ← fourier_add]
      norm_num
private lemma circlePoint_pow (r : ℝ) (t : Circle) (n : ℕ) :
    (circlePoint r t : ℂ) ^ n = ((r ^ n : ℝ) : ℂ) * fourier (n : ℤ) t := by
  change (((r : ℂ) * (fourier (1 : ℤ) t : ℂ)) ^ n) =
    ((r ^ n : ℝ) : ℂ) * fourier (n : ℤ) t
  rw [mul_pow, fourier_one_pow]
  norm_cast
private lemma star_circlePoint_pow (r : ℝ) (t : Circle) (m : ℕ) :
    star (circlePoint r t) ^ m = ((r ^ m : ℝ) : ℂ) * fourier (-(m : ℤ)) t := by
  have hstar : star (circlePoint r t) = (r : ℂ) * fourier (-1 : ℤ) t := by
    change (starRingEnd ℂ) (circlePoint r t) = _
    unfold circlePoint HermiteLEAN.circlePoint
    rw [map_mul, Complex.conj_ofReal]; congr 1
    exact (fourier_neg (n := 1) (x := t)).symm
  rw [hstar, mul_pow]; congr 1; · push_cast; rfl
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, ← fourier_add]; congr 1; push_cast; ring_nf
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k n : ℕ} {r : ℝ},
      0 < r →
        ∀ t : Circle,
          Phi k n (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                ((qkn k n r : ℂ) * fourier (n : ℤ) t) := by
  intro k n r hr t
  simp only [Phi, qkn, circleLeadingFactor]
  set S := Finset.range (min k n + 1)
  have hterm : ∀ j ∈ S,
      ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
        (circlePoint r t) ^ (n - j) * star (circlePoint r t) ^ (k - j) =
      ((r ^ k : ℝ) : ℂ) * (fourier (-(k : ℤ)) t : ℂ) * (fourier ((n : ℤ)) t : ℂ) *
        (((-1 : ℝ) ^ j * (Nat.choose k j : ℝ) *
          ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
          r ^ ((n : ℤ) - 2 * (j : ℤ)) : ℝ) : ℂ) := by
    intro j hj
    have hjk : j ≤ k := by simp [S] at hj; omega
    have hjn : j ≤ n := by simp [S] at hj; omega
    rw [circlePoint_pow, star_circlePoint_pow]
    have hf : (fourier ((n - j : ℕ) : ℤ) t : ℂ) * fourier (-(k - j : ℕ) : ℤ) t =
        (fourier (-(k : ℤ)) t : ℂ) * fourier ((n : ℤ)) t := by
      rw [← fourier_add, ← fourier_add]; congr 1
      have h1 : ((n - j : ℕ) : ℤ) = (n : ℤ) - (j : ℤ) := by omega
      have h2 : ((k - j : ℕ) : ℤ) = (k : ℤ) - (j : ℤ) := by omega
      rw [h1, h2]; ring_nf
    have hrpow : ((r ^ (n - j) : ℝ) : ℂ) * ((r ^ (k - j) : ℝ) : ℂ) =
        ((r ^ k : ℝ) : ℂ) * ((r ^ ((n : ℤ) - 2 * (j : ℤ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]; congr 1
      rw [← pow_add, show n - j + (k - j) = n + k - 2 * j from by omega]
      rw [← zpow_natCast r (n + k - 2 * j), ← zpow_natCast r k,
        ← zpow_add₀ (ne_of_gt hr)]
      congr 1; rw [Nat.cast_sub (by omega : 2 * j ≤ n + k)]; push_cast; ring
    calc _ = ((-1 : ℂ) ^ j * (Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ))) *
          (((r ^ (n - j) : ℝ) : ℂ) * ((r ^ (k - j) : ℝ) : ℂ)) *
          ((fourier ((n - j : ℕ) : ℤ) t : ℂ) *
            fourier (-(k - j : ℕ) : ℤ) t) := by ring
      _ = ((-1 : ℂ) ^ j * (Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ))) *
          (((r ^ k : ℝ) : ℂ) * ((r ^ ((n : ℤ) - 2 * (j : ℤ)) : ℝ) : ℂ)) *
          ((fourier (-(k : ℤ)) t : ℂ) *
            fourier ((n : ℤ)) t) := by rw [hrpow, hf]
      _ = _ := by push_cast; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    Real.sqrt_mul (Nat.cast_nonneg _)]
  simp_rw [← Complex.ofReal_sum S]
  push_cast; ring
end HermitekLEAN
