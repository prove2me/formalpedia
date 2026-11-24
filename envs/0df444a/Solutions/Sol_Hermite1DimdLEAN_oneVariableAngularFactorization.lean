-- Prove2me | solution 1 for Hermite1DimdLEAN.oneVariableAngularFactorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:00.414887+00:00
-- url     : https://prove2.me/submissions/1c1d003d-9116-4ae7-976d-3850e0591d13

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma oneVariableAngularFactorization_termwise
    (r t : ℝ) (k n j : ℕ) (hjk : j ≤ k) (hjn : j ≤ n) :
    (r : ℂ) ^ (k - j) *
      ((r : ℂ) ^ (n - j) *
        (Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              (Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) *
                ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))))) =
    Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
      ((Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
          ((-1 : ℂ) ^ j * ((↑r : ℂ) ^ (n + k - j * 2) * ((↑√↑k.factorial)⁻¹ *
              (↑√↑n.factorial)⁻¹))))) := by
  have hrpow :
      (r : ℂ) ^ (k - j) * (r : ℂ) ^ (n - j) =
        (r : ℂ) ^ (n + k - j * 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hphase :
      Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
          Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) =
        Complex.exp (Complex.I * (↑t * (↑n - ↑k))) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub hjn, Nat.cast_sub hjk]
    ring
  calc
    (r : ℂ) ^ (k - j) *
        ((r : ℂ) ^ (n - j) *
          (Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
            ((Nat.choose k j : ℂ) *
              ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
                (Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) *
                  ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))))) =
      ((r : ℂ) ^ (k - j) * (r : ℂ) ^ (n - j)) *
        ((Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
            Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j)) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))) := by ring
    _ =
      (↑r : ℂ) ^ (n + k - j * 2) *
        (Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))) := by rw [hrpow, hphase]
    _ =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        ((Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
            ((-1 : ℂ) ^ j * ((↑r : ℂ) ^ (n + k - j * 2) * ((↑√↑k.factorial)⁻¹ *
                (↑√↑n.factorial)⁻¹))))) := by ring
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    (k n : ℕ) :
    ∃ radial : Polynomial ℝ,
      ∀ r t : ℝ,
        oneDimPhi k n ((r : ℂ) * Complex.exp (Complex.I * t)) =
          Complex.exp (Complex.I * ((((n : ℤ) - (k : ℤ)) : ℂ) * t)) *
            radial.eval₂ (algebraMap ℝ ℂ) r := by
  let radial : Polynomial ℝ :=
    Finset.sum (Finset.range (min k n + 1)) fun j =>
      Polynomial.monomial (n + k - j * 2)
        (((Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) *
          (((-1 : ℝ) ^ j) *
            (((Real.sqrt (Nat.factorial k : ℝ))⁻¹) *
              ((Real.sqrt (Nat.factorial n : ℝ))⁻¹))))
  refine ⟨radial, ?_⟩
  intro r t
  have hnorm :
      (1 / (↑(Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)) =
        ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
          (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹ : ℂ) := by
    have hnormR :
        (1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) =
          (Real.sqrt (Nat.factorial k : ℝ))⁻¹ *
            (Real.sqrt (Nat.factorial n : ℝ))⁻¹ := by
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ Nat.factorial k by positivity)]
      field_simp
        [Real.sqrt_ne_zero'.2
          (by exact_mod_cast Nat.factorial_pos k : (0 : ℝ) < Nat.factorial k),
         Real.sqrt_ne_zero'.2
          (by exact_mod_cast Nat.factorial_pos n : (0 : ℝ) < Nat.factorial n)]
    exact_mod_cast hnormR
  have hstar_z :
      star ((r : ℂ) * Complex.exp (Complex.I * t)) =
        (r : ℂ) * Complex.exp (-(Complex.I * t)) := by
    rw [Complex.star_def, map_mul, ← Complex.exp_conj]
    simp
  have hphaseCast :
      Complex.exp (Complex.I * ((((n : ℤ) - (k : ℤ)) : ℂ) * t)) =
        Complex.exp (Complex.I * (↑t * (↑n - ↑k))) := by
    congr 1
    push_cast
    ring
  unfold oneDimPhi
  rw [hphaseCast, hnorm, Finset.mul_sum]
  have hsum :
      Finset.sum (Finset.range (min k n + 1))
        (fun j =>
          ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
              (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹) *
            (((-1 : ℂ) ^ j * ↑(Nat.choose k j) *
                  (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)))) *
              (((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (n - j) *
                star ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (k - j)))) =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        Finset.sum (Finset.range (min k n + 1))
          (fun j =>
            ↑(Nat.choose k j) *
              (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)) *
                ((-1 : ℂ) ^ j *
                  ((r : ℂ) ^ (n + k - j * 2) *
                    ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                      (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹))))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range, Nat.lt_add_one_iff, le_min_iff] at hj
    obtain ⟨hjk, hjn⟩ := hj
    rw [hstar_z, mul_pow, mul_pow]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      oneVariableAngularFactorization_termwise r t k n j hjk hjn
  have hsum' :
      Finset.sum (Finset.range (min k n + 1))
        (fun i =>
          ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹) *
              ((-1 : ℂ) ^ i * ↑(Nat.choose k i) *
                    (↑(Nat.factorial n) / ↑(Nat.factorial (n - i))) *
                  ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (n - i) *
                star ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (k - i))) =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        Finset.sum (Finset.range (min k n + 1))
          (fun j =>
            ↑(Nat.choose k j) *
              (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)) *
                ((-1 : ℂ) ^ j *
                  ((r : ℂ) ^ (n + k - j * 2) *
                    ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                      (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹))))) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  rw [hsum']
  congr 1
  simp [radial, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    mul_assoc, mul_left_comm, mul_comm]
end Hermite1DimdLEAN
