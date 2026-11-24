-- Prove2me | solution 1 for GlobalTheory.NotIntegral.inv_small_not_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:13.777238+00:00
-- url     : https://prove2.me/submissions/937a89bf-86ad-4dc2-bab6-1d506c676071

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsIntegralResidueInvSmallInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.NotIntegral
namespace GlobalTheory.NotIntegral
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  intro K B a ha m hint
  obtain ⟨ha0, hmax, -⟩ := ha
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let f : K.E →ₐ[K.O] (B.A ⧸ m.asIdeal) := IsScalarTower.toAlgHom K.O K.E (B.A ⧸ m.asIdeal)
  have hf : Function.Injective f := (algebraMap K.E (B.A ⧸ m.asIdeal)).injective
  have hE : IsIntegral K.O (algebraMap K.O K.E a)⁻¹ := (isIntegral_algHom_iff f hf).1 hint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hE
  have hne : algebraMap K.O K.E a ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]; exact ha0
  have hab : a * b = 1 := by
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  exact (IsLocalRing.mem_maximalIdeal a).1 hmax ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩
end GlobalTheory.NotIntegral
