-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.lift_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:25.55842+00:00
-- url     : https://prove2.me/submissions/0191968c-b1d8-4e4c-a473-a2762d4d8fd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_aeval_P
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Orbit_exists_monic_map_eq_charpoly__518c0881fa8f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution (B₁ B₂ : InvAlg K) (hsep : (B₁.P * B₂.P).Separable) (Q : K.O[X])
    (hQ : Q.map (algebraMap K.O K.E) = B₁.P * B₂.P) :
    ∃ Q₁ Q₂ : K.O[X], Q = Q₁ * Q₂ ∧ Q₁.map (algebraMap K.O K.E) = B₁.P ∧ Q₂.map (algebraMap K.O K.E) = B₂.P ∧
      aeval B₁.g Q₁ = 0 ∧ aeval B₂.g Q₂ = 0 ∧ Q.Monic := by
  have hinj := IsFractionRing.injective K.O K.E
  have hm : Q.Monic := monic_of_injective hinj
    (hQ ▸ ((LinearMap.charpoly_monic _).mul (LinearMap.charpoly_monic _)))
  have i1 : IsIntegral K.O B₁.g :=
    ⟨Q, hm, by rw [← aeval_def, ← aeval_map_algebraMap K.E, hQ, map_mul, aeval_P, zero_mul]⟩
  have i2 : IsIntegral K.O B₂.g :=
    ⟨Q, hm, by rw [← aeval_def, ← aeval_map_algebraMap K.E, hQ, map_mul, aeval_P, mul_zero]⟩
  obtain ⟨Q₁, -, e₁⟩ := Orbit.exists_monic_map_eq_charpoly₂ B₁ hsep.of_mul_left i1
  obtain ⟨Q₂, -, e₂⟩ := Orbit.exists_monic_map_eq_charpoly₂ B₂ hsep.of_mul_right i2
  refine ⟨Q₁, Q₂, map_injective _ hinj (by rw [Polynomial.map_mul, e₁, e₂, hQ]), e₁, e₂, ?_, ?_, hm⟩
  · rw [← aeval_map_algebraMap K.E, e₁, aeval_P]
  · rw [← aeval_map_algebraMap K.E, e₂, aeval_P]
end GlobalTheory.UnitLemma.CayleyCase
