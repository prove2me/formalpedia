-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_core_ratio_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T14:17:07.706214+00:00
-- url     : https://prove2.me/submissions/df552abf-fe9b-4c68-b36b-56378f3fa982

import Definitions.Def_HodgeComputerFourPlusTwoWormholeBridge
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open MvPolynomial

abbrev R4 : Type := MvPolynomial (Fin 4) ℂ

theorem solution
    {K : Type} [Field K] [CharZero K]
    [Algebra R4 K]
    [IsFractionRing R4 K] :
    ∃ (a s t P : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        a = algebraMap R4 K (X 0) ∧
        t = algebraMap R4 K (X 2) / a ∧
        s = algebraMap R4 K (X 3) / algebraMap R4 K (X 2) ∧
        a ^ 6 * P = algebraMap R4 K core ∧
        a ^ 6 * t ^ 3 = algebraMap R4 K coreSource := by
  let ι : R4 →+* K := algebraMap R4 K
  have hinj : Function.Injective ι := IsFractionRing.injective R4 K
  have hX0 : (X (0 : Fin 4) : R4) ≠ 0 := by
    intro h
    have := congr_arg (eval (fun _ : Fin 4 => (1 : ℂ))) h
    simp [eval_X] at this
  have hX2 : (X (2 : Fin 4) : R4) ≠ 0 := by
    intro h
    have := congr_arg (eval (fun _ : Fin 4 => (1 : ℂ))) h
    simp [eval_X] at this
  have haX : ι (X 0) ≠ 0 := fun h => hX0 (hinj (by simpa using h))
  have hιX2 : ι (X 2) ≠ 0 := fun h => hX2 (hinj (by simpa using h))
  let a : K := ι (X 0)
  let t : K := ι (X 2) / a
  let s : K := ι (X 3) / ι (X 2)
  let P : K := ι core / a ^ 6
  refine ⟨a, s, t, P, haX, ?ht, rfl, rfl, rfl, ?hP, ?hSrc⟩
  · -- t ≠ 0
    intro ht
    have : ι (X 2) = 0 := by
      simpa [t, a, div_eq_zero_iff, haX] using ht
    exact hιX2 this
  · -- a^6 * P = ι(core)
    change a ^ 6 * (ι core / a ^ 6) = ι core
    exact mul_div_cancel₀ (ι core) (pow_ne_zero 6 haX)
  · -- a^6 * t^3 = ι(coreSource)
    change a ^ 6 * (ι (X 2) / a) ^ 3 = ι coreSource
    have hstep : a ^ 6 * (ι (X 2) / a) ^ 3 = a ^ 3 * ι (X 2) ^ 3 := by
      field_simp [haX]
    rw [hstep]
    -- a = ι(X 0), so a^3 * ι(X 2)^3 = ι(X 0^3 * X 2^3) = ι(coreSource)
    simp [a, coreSource, map_mul, map_pow]
