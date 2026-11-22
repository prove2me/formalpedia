-- Prove2me | solution 1 for LamLitt.isSolutionOfAlgebraicODE_smul_rescale
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:17:09.162887+00:00
-- url     : https://prove2.me/submissions/12c9a1f8-051c-4bb9-a9e5-eb75096f0ee6

import Definitions.Def_LamLitt_Defs
import Mathlib

set_option autoImplicit false

open PowerSeries

namespace LamLittAuxR

theorem derivative_rescale (b : ℚ) (h : PowerSeries ℚ) :
    derivative ℚ (rescale b h) = b • rescale b (derivative ℚ h) := by
  ext k
  simp only [coeff_derivative, coeff_rescale, map_smul, smul_eq_mul, pow_succ]
  ring

theorem iterate_derivative_smul_rescale (a b : ℚ) (f : PowerSeries ℚ) (i : ℕ) :
    (derivative ℚ)^[i] (a • rescale b f) =
      (a * b ^ i) • rescale b ((derivative ℚ)^[i] f) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', Derivation.map_smul,
      derivative_rescale, smul_smul]
    congr 1; ring

theorem rescale_aeval {σ : Type*} (b : ℚ) (pt : σ → PowerSeries ℚ) (r : MvPolynomial σ ℚ) :
    rescale b (MvPolynomial.aeval pt r) = MvPolynomial.aeval (fun j => rescale b (pt j)) r := by
  have h := MvPolynomial.comp_aeval (R := ℚ) pt ((rescale b).toRatAlgHom)
  exact congrArg (fun φ => φ r) h

theorem constantCoeff_aeval {σ : Type*} (pt : σ → PowerSeries ℚ) (r : MvPolynomial σ ℚ) :
    constantCoeff (MvPolynomial.aeval pt r) = MvPolynomial.eval (constantCoeff ∘ pt) r := by
  have h := MvPolynomial.comp_aeval (R := ℚ) pt
    ((constantCoeff (R := ℚ)).toRatAlgHom)
  have h2 : constantCoeff (MvPolynomial.aeval pt r)
      = MvPolynomial.aeval (fun i => constantCoeff (pt i)) r := congrArg (fun φ => φ r) h
  rw [h2, MvPolynomial.aeval_eq_eval]
  rfl

/-- the scaling vector -/
noncomputable def lam (n : ℕ) (a b : ℚ) : Fin (n + 1) → ℚ :=
  Fin.cases b (fun i : Fin n => (a * b ^ i.val)⁻¹)

/-- the substitution `X j ↦ lam j * X j` -/
noncomputable def sub (n : ℕ) (a b : ℚ) (r : MvPolynomial (Fin (n + 1)) ℚ) :
    MvPolynomial (Fin (n + 1)) ℚ :=
  MvPolynomial.bind₁ (fun j => MvPolynomial.C (lam n a b j) * MvPolynomial.X j) r

theorem key {n : ℕ} (f : PowerSeries ℚ) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (r : MvPolynomial (Fin (n + 1)) ℚ) :
    MvPolynomial.aeval
        (Fin.cases X (fun i : Fin n ↦ (derivative ℚ)^[i.val] (a • rescale b f)) :
          Fin (n + 1) → PowerSeries ℚ) (sub n a b r)
      = rescale b (MvPolynomial.aeval
        (Fin.cases X (fun i : Fin n ↦ (derivative ℚ)^[i.val] f) :
          Fin (n + 1) → PowerSeries ℚ) r) := by
  rw [rescale_aeval, sub, MvPolynomial.aeval_bind₁]
  refine congrArg (fun v => MvPolynomial.aeval v r) (funext fun j => ?_)
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [lam, rescale_X]
  · have hne : a * b ^ i.val ≠ 0 := mul_ne_zero ha (pow_ne_zero _ hb)
    simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, lam, Fin.cases_succ,
      iterate_derivative_smul_rescale]
    rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hne, one_smul]

end LamLittAuxR

open LamLitt PowerSeries in
theorem solution {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ g' : MvRatFunc (Fin (n + 1)) ℚ,
      IsSolutionOfAlgebraicODE n (a • PowerSeries.rescale b f) g' := by
  obtain ⟨p, q, -, hq, hpq⟩ := hODE
  refine ⟨algebraMap _ _ (MvPolynomial.C (a * b ^ n) * LamLittAuxR.sub n a b p) /
    algebraMap _ _ (LamLittAuxR.sub n a b q),
    MvPolynomial.C (a * b ^ n) * LamLittAuxR.sub n a b p, LamLittAuxR.sub n a b q, rfl, ?_, ?_⟩
  · rw [← LamLittAuxR.constantCoeff_aeval, LamLittAuxR.key f a b ha hb,
      ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply, LamLittAuxR.constantCoeff_aeval]
    exact hq
  · rw [_root_.map_mul (MvPolynomial.aeval _) (MvPolynomial.C _) _, MvPolynomial.aeval_C,
      LamLittAuxR.key f a b ha hb, LamLittAuxR.key f a b ha hb, ← hpq, (rescale b).map_mul,
      LamLittAuxR.iterate_derivative_smul_rescale, ← Algebra.smul_def, smul_mul_assoc]
