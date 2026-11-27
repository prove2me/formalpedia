-- Prove2me | solution 1 for GlobalTheory.LocLatInert.exists_unit_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:55:08.218091+00:00
-- url     : https://prove2.me/submissions/06461557-8e9c-419d-8c6f-a0396d285395

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletion
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped Matrix
open GlobalTheory GlobalTheory.LocLatInert
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.LocLatInert
theorem _root_.solution (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    (hx : ∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) :
    ∃ u : K, σ u * u = 1 ∧ Valued.v u ≤ 1 ∧ Valued.v (σ u) ≤ 1 ∧ 1 - u ≠ 0 ∧
      Valued.v (1 - u)⁻¹ ≤ 1 := by
  obtain ⟨x, hx1, hx2⟩ := hx

  have hvx : Valued.v x = 1 := by
    refine le_antisymm hx1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (σ x - x) := hx2.symm
      _ ≤ max (Valued.v (σ x)) (Valued.v x) := Valuation.map_sub _ _ _
      _ = Valued.v x := by rw [hv, max_self]
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvx; exact zero_ne_one hvx
  have hsx0 : σ x ≠ 0 := by
    intro h0; rw [← hv, h0, map_zero] at hvx; exact zero_ne_one hvx
  have hd : x - σ x ≠ 0 := by
    intro h0
    rw [← neg_sub, h0, neg_zero, map_zero] at hx2
    exact zero_ne_one hx2
  have hvd : Valued.v (x - σ x) = 1 := by rw [← neg_sub, Valuation.map_neg, hx2]

  refine ⟨σ x * x⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv₀, hσ]
    field_simp
  · rw [map_mul, map_inv₀, hv, hvx, inv_one, mul_one]
  · rw [map_mul, map_mul, map_inv₀, hσ, map_inv₀, hv, hvx, inv_one, mul_one]
  · rw [sub_ne_zero]
    intro h
    apply hd
    have : x = σ x := by
      field_simp at h
      exact h
    rw [← this, sub_self]
  · have e : (1 - σ x * x⁻¹)⁻¹ = x * (x - σ x)⁻¹ := by
      field_simp
    rw [e, map_mul, map_inv₀, hvx, hvd]
    simp
end GlobalTheory.LocLatInert
