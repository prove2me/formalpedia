-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeIntegralNormEtale.integral_norm_fibres_finite_etale
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T06:10:34.105925+00:00
-- url     : https://prove2.me/submissions/64cae20c-82b6-417d-acdf-81d9ef912864

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite etale fibres of the SAME selected integral norm
extensions at every prime away from 104 and nineteen. The group law and
multiplication by nineteen are those of the selected local Picard model.
Named downstream consumer: good-prime unramified Kummer conditions.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormFinite_integral_norms_finite
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormEtale_integral_norms_etale
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalScalarInputs
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralScalarNineteen
open Order13LocalIntegralCoefficientMaps

theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) {T : Scheme}
    (x : T ⟶ (localPicard q hq).P) :
    (IsFinite (pullback.snd (integralPi q hq).val x) ∧
      Etale (pullback.snd (integralPi q hq).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate q hq).val x) ∧
      Etale (pullback.snd (integralPiConjugate q hq).val x)) := by
  letI : IsFinite (integralPi q hq).val := (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite q hq hne).1
  letI : IsFinite (integralPiConjugate q hq).val := (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite q hq hne).2
  letI : Etale (integralPi q hq).val := (MazurTransfer.Order13GoodPrimeIntegralNormEtale.integral_norms_etale q hq hne).1
  letI : Etale (integralPiConjugate q hq).val := (MazurTransfer.Order13GoodPrimeIntegralNormEtale.integral_norms_etale q hq hne).2
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

#print axioms solution
