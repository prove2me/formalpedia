-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.derivation_ratFuncFormalDerivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:26:52.431593+00:00
-- url     : https://prove2.me/submissions/076b2a04-a10c-4077-970b-747e14085135

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivation

open Polynomial

namespace S105DR

variable {K : Type} [Field K]

local notation "ι" => algebraMap K[X] (RatFunc K)

noncomputable def D (x : RatFunc K) : RatFunc K :=
  ι (derivative x.num * x.denom - x.num * derivative x.denom) / ι x.denom ^ 2

theorem D_eq (p q : K[X]) (hq : q ≠ 0) :
    D (ι p / ι q) = ι (derivative p * q - p * derivative q) / ι q ^ 2 := by
  set x := ι p / ι q with hx
  have hd := RatFunc.denom_ne_zero x
  have e1 : p * x.denom = x.num * q := by
    apply RatFunc.algebraMap_injective K
    have := RatFunc.num_div_denom x
    rw [hx] at this
    rw [map_mul, map_mul]
    rw [div_eq_div_iff (RatFunc.algebraMap_ne_zero hd) (RatFunc.algebraMap_ne_zero hq)] at this
    linear_combination -this
  have e2 := congrArg derivative e1
  simp only [derivative_mul] at e2
  unfold D
  rw [div_eq_div_iff (pow_ne_zero _ (RatFunc.algebraMap_ne_zero hd))
    (pow_ne_zero _ (RatFunc.algebraMap_ne_zero hq))]
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul]
  congr 1
  linear_combination -(q * x.denom) * e2 + (derivative q * x.denom + q * derivative x.denom) * e1

theorem rep (x : RatFunc K) : ∃ p q : K[X], q ≠ 0 ∧ x = ι p / ι q :=
  ⟨x.num, x.denom, RatFunc.denom_ne_zero x, (RatFunc.num_div_denom x).symm⟩

theorem D_add (x y : RatFunc K) : D (x + y) = D x + D y := by
  obtain ⟨p, q, hq, rfl⟩ := rep x
  obtain ⟨r, s, hs, rfl⟩ := rep y
  have hq' := RatFunc.algebraMap_ne_zero hq
  have hs' := RatFunc.algebraMap_ne_zero hs
  have : ι p / ι q + ι r / ι s = ι (p * s + r * q) / ι (q * s) := by
    rw [map_add, map_mul, map_mul, map_mul]; field_simp
  rw [this, D_eq _ _ (mul_ne_zero hq hs), D_eq _ _ hq, D_eq _ _ hs]
  simp only [derivative_mul, map_add, map_mul, map_sub]
  field_simp; ring

theorem D_mul (x y : RatFunc K) : D (x * y) = x * D y + y * D x := by
  obtain ⟨p, q, hq, rfl⟩ := rep x
  obtain ⟨r, s, hs, rfl⟩ := rep y
  have hq' := RatFunc.algebraMap_ne_zero hq
  have hs' := RatFunc.algebraMap_ne_zero hs
  have : ι p / ι q * (ι r / ι s) = ι (p * r) / ι (q * s) := by
    rw [map_mul, map_mul]; field_simp
  rw [this, D_eq _ _ (mul_ne_zero hq hs), D_eq _ _ hq, D_eq _ _ hs]
  simp only [derivative_mul, map_add, map_mul, map_sub]
  field_simp; ring

theorem D_smul (c : K) (x : RatFunc K) : D (c • x) = c • D x := by
  obtain ⟨p, q, hq, rfl⟩ := rep x
  have hq' := RatFunc.algebraMap_ne_zero hq
  have : c • (ι p / ι q) = ι (C c * p) / ι q := by
    rw [Algebra.smul_def, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]; ring
  rw [this, D_eq _ _ hq, D_eq _ _ hq, Algebra.smul_def]
  simp only [derivative_mul, derivative_C, map_add, map_mul, map_sub, RatFunc.algebraMap_C, map_zero, RatFunc.algebraMap_eq_C]
  field_simp; ring

theorem D_alg (p : K[X]) : D (ι p) = ι (derivative p) := by
  have := D_eq p 1 one_ne_zero
  simpa using this

noncomputable def δ : Derivation K (RatFunc K) (RatFunc K) :=
  Derivation.mk' { toFun := D, map_add' := D_add, map_smul' := D_smul }
    (fun x y => by simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]; exact D_mul x y)

end S105DR

theorem solution (K : Type) [Field K] :
    ∃ δ : Derivation K (RatFunc K) (RatFunc K),
      ∀ p : Polynomial K,
        δ (algebraMap (Polynomial K) (RatFunc K) p) =
          algebraMap (Polynomial K) (RatFunc K) p.derivative :=
  ⟨S105DR.δ, fun p => S105DR.D_alg p⟩
