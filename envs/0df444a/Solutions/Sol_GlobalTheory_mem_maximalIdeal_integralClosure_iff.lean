-- Prove2me | solution 1 for GlobalTheory.mem_maximalIdeal_integralClosure_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:20:24.631488+00:00
-- url     : https://prove2.me/submissions/d1b53d56-3642-4b2c-8561-88265d649f10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {p K}
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
namespace GlobalTheory
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (x : integralClosure ℤ_[p] K) :
    x ∈ maximalIdeal (integralClosure ℤ_[p] K) ↔ ‖((x : K) : PadicAlgCl p)‖ < 1 := by
  have hle := fun y : integralClosure ℤ_[p] K => (mem_integralClosure_padicInt_iff K y).mp y.2
  rw [mem_maximalIdeal, mem_nonunits_iff, ← not_le]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y, hy⟩ := h.exists_right_inv
    have h1 : ‖((x : K) : PadicAlgCl p)‖ * ‖((y : K) : PadicAlgCl p)‖ = 1 := by
      rw [← norm_mul]
      have : ((x : K) : PadicAlgCl p) * ((y : K) : PadicAlgCl p) = 1 := by
        exact_mod_cast congrArg (fun z : integralClosure ℤ_[p] K => ((z : K) : PadicAlgCl p)) hy
      rw [this, norm_one]
    calc 1 = _ := h1.symm
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) (hle y)
  · have h0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0] at h
      norm_num at h
    have hinv : (x : K)⁻¹ ∈ integralClosure ℤ_[p] K := by
      rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ h
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))
end GlobalTheory
