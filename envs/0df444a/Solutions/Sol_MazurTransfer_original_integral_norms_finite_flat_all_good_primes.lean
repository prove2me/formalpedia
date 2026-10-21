-- Prove2me | solution 1 for MazurTransfer.original_integral_norms_finite_flat_all_good_primes
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T05:12:01.486414+00:00
-- url     : https://prove2.me/submissions/594a4c8b-5c68-4c8f-afe0-eb0da6ba2046

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete positive-scalar inputs reuse official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: finite-flat, locally finitely presented, surjective maps and arbitrary fibres of the same selected integral norms at every prime away from 104, including nineteen.
Named downstream consumer: same integral norm-kernel Hopf models and local norm-preimage torsors at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormCompositionData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralScalarNineteen_integralNorm_scalar
import Theorems.Thm_MazurTransfer_original_positive_scalar_norm_factors_finite_flat
import Theorems.Thm_MazurTransfer_original_local_picard_group_law_commutative
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.Order13GoodPrimeIntegralNormComposition
open MazurTransfer.Order13GoodPrimeIntegralScalarNineteen MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
namespace MazurTransfer.OriginalIntegralNormsFiniteFlatAllGoodPrimesBoundary20261020
end MazurTransfer.OriginalIntegralNormsFiniteFlatAllGoodPrimesBoundary20261020
namespace MazurTransfer.OriginalIntegralNormsFiniteFlatScalarIdentitiesProof20261020
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
theorem integralScalarNineteen_eq_local_schemeNsmul :
    (integralScalarNineteen q hq).val = (localLaw q hq).schemeNsmul 19 :=
  congrArg Subtype.val (integralNorm_scalar q hq 19)
theorem integralPi_comp_integralPiConjugate_eq_local_schemeNsmul :
    (integralPi q hq).val ≫ (integralPiConjugate q hq).val =
      (localLaw q hq).schemeNsmul 19 := by
  have h := congrArg Subtype.val (integralPi_comp_integralPiConjugate q hq)
  exact h.trans (integralScalarNineteen_eq_local_schemeNsmul q hq)
theorem integralPiConjugate_comp_integralPi_eq_local_schemeNsmul :
    (integralPiConjugate q hq).val ≫ (integralPi q hq).val =
      (localLaw q hq).schemeNsmul 19 := by
  have h := congrArg Subtype.val (integralPiConjugate_comp_integralPi q hq)
  exact h.trans (integralScalarNineteen_eq_local_schemeNsmul q hq)
end MazurTransfer.OriginalIntegralNormsFiniteFlatScalarIdentitiesProof20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite-flatness of the SAME selected integral norm
extensions at every prime away from 104, including nineteen, and their
fibres over arbitrary test schemes. The positive scalar proof is reused
from official Anthropic FLT, pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Named downstream consumer: exceptional nineteen flat local norm torsors.
-/

noncomputable section
open MazurTransfer.OriginalIntegralNormsFiniteFlatScalarIdentitiesProof20261020
namespace MazurTransfer.OriginalIntegralNormsFiniteFlatAllGoodPrimesProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralScalarNineteen
open Order13LocalIntegralCoefficientMaps
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

theorem integral_norms_finite_flat :
    (IsFinite (integralPi q hq).val ∧ Flat (integralPi q hq).val ∧
      LocallyOfFinitePresentation (integralPi q hq).val ∧ Surjective (integralPi q hq).val) ∧
    (IsFinite (integralPiConjugate q hq).val ∧ Flat (integralPiConjugate q hq).val ∧
      LocallyOfFinitePresentation (integralPiConjugate q hq).val ∧
        Surjective (integralPiConjugate q hq).val) := by
  exact MazurTransfer.original_positive_scalar_norm_factors_finite_flat
    (localLaw q hq) (MazurTransfer.original_local_picard_group_law_commutative q hq) (localPicard_abelian q hq)
    19 (by norm_num) (integralPi q hq) (integralPiConjugate q hq)
    (integralPi_comp_integralPiConjugate_eq_local_schemeNsmul q hq)
    (integralPiConjugate_comp_integralPi_eq_local_schemeNsmul q hq)

theorem integral_norm_fibres_finite_flat {T : Scheme}
    (x : T ⟶ (localPicard q hq).P) :
    (IsFinite (pullback.snd (integralPi q hq).val x) ∧
      Flat (pullback.snd (integralPi q hq).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPi q hq).val x) ∧
      Surjective (pullback.snd (integralPi q hq).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate q hq).val x) ∧
      Flat (pullback.snd (integralPiConjugate q hq).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPiConjugate q hq).val x) ∧
      Surjective (pullback.snd (integralPiConjugate q hq).val x)) := by
  have h := integral_norms_finite_flat q hq
  letI : IsFinite (integralPi q hq).val := h.1.1
  letI : Flat (integralPi q hq).val := h.1.2.1
  letI : LocallyOfFinitePresentation (integralPi q hq).val := h.1.2.2.1
  letI : Surjective (integralPi q hq).val := h.1.2.2.2
  letI : IsFinite (integralPiConjugate q hq).val := h.2.1
  letI : Flat (integralPiConjugate q hq).val := h.2.2.1
  letI : LocallyOfFinitePresentation (integralPiConjugate q hq).val := h.2.2.2.1
  letI : Surjective (integralPiConjugate q hq).val := h.2.2.2.2
  exact ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩⟩

end MazurTransfer.OriginalIntegralNormsFiniteFlatAllGoodPrimesProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), (IsFinite (integralPi q hq).val ∧ Flat (integralPi q hq).val ∧
      LocallyOfFinitePresentation (integralPi q hq).val ∧ Surjective (integralPi q hq).val) ∧
    (IsFinite (integralPiConjugate q hq).val ∧ Flat (integralPiConjugate q hq).val ∧
      LocallyOfFinitePresentation (integralPiConjugate q hq).val ∧
        Surjective (integralPiConjugate q hq).val)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme}
    (x : T ⟶ (localPicard q hq).P),
(IsFinite (pullback.snd (integralPi q hq).val x) ∧
      Flat (pullback.snd (integralPi q hq).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPi q hq).val x) ∧
      Surjective (pullback.snd (integralPi q hq).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate q hq).val x) ∧
      Flat (pullback.snd (integralPiConjugate q hq).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPiConjugate q hq).val x) ∧
      Surjective (pullback.snd (integralPiConjugate q hq).val x))) := by
  exact ⟨MazurTransfer.OriginalIntegralNormsFiniteFlatAllGoodPrimesProof20261020.integral_norms_finite_flat, MazurTransfer.OriginalIntegralNormsFiniteFlatAllGoodPrimesProof20261020.integral_norm_fibres_finite_flat⟩
#print axioms solution
