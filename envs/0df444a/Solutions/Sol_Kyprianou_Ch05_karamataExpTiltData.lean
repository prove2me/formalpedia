-- Prove2me | solution 1 for Kyprianou.Ch05.karamataExpTiltData
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T01:14:20.185558+00:00
-- url     : https://prove2.me/submissions/0a873345-51ec-4cdb-bb06-20bc60267b89

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Theorems.Thm_Kyprianou_Ch05_karamataExpTiltMomentENN
import Theorems.Thm_Kyprianou_Ch05_karamataExpTiltSupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The compact tilted image has finite mass and integrable powers. -/
theorem solution (M : Measure Real) (hs : M (Iio 0) = 0)
    (hfin : ∀ t : Real, 0 < t → positiveLaplace M t ≠ ⊤) :
    let N := ((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z)))
    N univ ≠ ⊤ ∧ (∀ᵐ z ∂N, z ∈ Icc (0 : Real) 1) ∧
      (∀ n : Nat, Integrable (fun z : Real => z^n) N) ∧
      (∀ n : Nat, (∫ z : Real, z^n ∂N) =
        (positiveLaplace M ((n : Real)+1)).toReal) := by
  let N := ((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z)))
  have he := karamataExpTiltMomentENN M 0
  simp only [pow_zero,Nat.cast_zero,zero_add,lintegral_const,one_mul] at he
  have hf : N univ ≠ ⊤ := by
    change N univ = positiveLaplace M 1 at he
    rw [he]
    exact hfin 1 zero_lt_one
  haveI : IsFiniteMeasure N := ⟨lt_top_iff_ne_top.mpr hf⟩
  have hS : ∀ᵐ z ∂N, z ∈ Icc (0 : Real) 1 := karamataExpTiltSupport M hs
  refine ⟨hf,hS,?_,?_⟩
  · intro n
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hS] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hz.1 _)]
    exact pow_le_one₀ hz.1 hz.2
  · intro n
    have hn : 0 ≤ᵐ[N] (fun z : Real => z^n) := hS.mono (fun z hz => pow_nonneg hz.1 _)
    rw [integral_eq_lintegral_of_nonneg_ae hn (by fun_prop)]
    congr 1
    calc
      _ = ∫⁻ z : Real, (ENNReal.ofReal z)^n ∂N := by
        apply lintegral_congr_ae
        filter_upwards [hS] with z hz
        -- FIX (WillR 4ef2d915 CE line 43): `ENNReal.ofReal_pow` takes the
        -- nonnegativity hypothesis first, then the exponent `n` explicitly;
        -- the bare `ENNReal.ofReal_pow hz.1` still expected `∀ n : ℕ, ...`.
        exact ENNReal.ofReal_pow hz.1 n
      _ = _ := karamataExpTiltMomentENN M n
