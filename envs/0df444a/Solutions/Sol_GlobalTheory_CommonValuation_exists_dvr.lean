-- Prove2me | solution 1 for GlobalTheory.CommonValuation.exists_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:00.769459+00:00
-- url     : https://prove2.me/submissions/118652dd-8ac6-4d45-b989-e8c5c190b937

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationIndexValuationCompat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CommonValuation
namespace GlobalTheory.CommonValuation
theorem _root_.solution (V K L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra W L)
      (_ : IsFractionRing W L) (f : V →+* W), (∀ z : V, algebraMap W L (f z) = algebraMap K L (algebraMap V K z)) ∧
      ∀ z : V, f z ∈ IsLocalRing.maximalIdeal W ↔ z ∈ IsLocalRing.maximalIdeal V := by
  let _ : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsDedekindDomain (integralClosure V L) := integralClosure.isDedekindDomain V K L
  have : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension K L
  have hinj : Function.Injective (algebraMap V (integralClosure V L)) := fun a b h =>
    IsFractionRing.injective V K ((algebraMap K L).injective (congrArg Subtype.val h))
  obtain ⟨M, -, hM, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := integralClosure V L)
    (IsLocalRing.maximalIdeal V) ⊥ (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have h0 : M ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hc
    exact IsDiscreteValuationRing.not_a_field V hc.symm
  let P : HeightOneSpectrum (integralClosure V L) := ⟨M, hM, h0⟩
  refine ⟨(P.valuation L).valuationSubring, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap V L).codRestrict (P.valuation L).valuationSubring.toSubring
      (fun z => P.valuation_le_one (K := L) (algebraMap V _ z)), fun _ => rfl, fun z => ?_⟩
  rw [Valuation.mem_maximalIdeal_iff, ← hc]
  exact P.valuation_lt_one_iff_mem (K := L) (algebraMap V _ z)
end GlobalTheory.CommonValuation
