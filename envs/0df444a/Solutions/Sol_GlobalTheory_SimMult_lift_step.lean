-- Prove2me | solution 1 for GlobalTheory.SimMult.lift_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:12.130015+00:00
-- url     : https://prove2.me/submissions/e2ae16f4-408e-4087-ba05-e157cb0e0793

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
variable {O : Type*} [CommRing O] (σ : O →+* O)
namespace GlobalTheory.SimMult
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) {w : O} (hw : w + σ w = 1) (I : Ideal O) (ν μ : ℤ)
    (hμ : (ν : O) * μ - 1 ∈ I) (k : ℕ) (c : O) (hc : c * σ c - ν ∈ I ^ (k + 1)) :
    ∃ c', c' - c ∈ I ∧ c' * σ c' - ν ∈ I ^ (k + 2) := by
  set δ := c * σ c - ν with hδ
  have hI : δ ∈ I := Ideal.pow_le_self (by omega) hc
  have hσδ : σ δ = δ := by rw [hδ, map_sub, map_mul, hσ, map_intCast, mul_comm]
  refine ⟨c * (1 - w * δ * μ), ?_, ?_⟩
  · have : c * (1 - w * δ * μ) - c = (-c * w * μ) * δ := by ring
    rw [this]; exact I.mul_mem_left _ hI
  · have h1 : σ (c * (1 - w * δ * μ)) = σ c * (1 - σ w * δ * μ) := by
      simp only [map_mul, map_sub, map_one, hσδ, map_intCast]
    have h2 : c * (1 - w * δ * μ) * σ (c * (1 - w * δ * μ)) - ν
        = δ * (-((ν : O) * μ - 1) + (-μ + (ν + δ) * w * σ w * μ ^ 2) * δ) := by
      rw [h1]
      have h3 : c * σ c = ν + δ := by rw [hδ]; ring
      linear_combination ((1 - w * δ * μ) * (1 - σ w * δ * μ)) * h3 - (ν + δ) * δ * μ * hw
    rw [h2, pow_succ I (k + 1)]
    exact Ideal.mul_mem_mul hc (I.add_mem (I.neg_mem hμ) (I.mul_mem_left _ hI))
end GlobalTheory.SimMult
