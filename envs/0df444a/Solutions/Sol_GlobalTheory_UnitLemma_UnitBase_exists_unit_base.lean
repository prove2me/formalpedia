-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnitBase.exists_unit_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:35.359805+00:00
-- url     : https://prove2.me/submissions/2c688dda-e323-4d06-8b49-5c8a67cfe8c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
import Theorems.Thm_GlobalTheory_UnitLemma_UnitBase_exists_isUnit_add_mul_twist
import Theorems.Thm_GlobalTheory_UnitLemma_UnitBase_algebraMap_cO
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase___algebraMap_O_5df93c796371
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase___mem_adjoin_4ad2303c8cd0
import Theorems.Thm_GlobalTheory_UnitLemma_UnitBase_maximal_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.UnitBase
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by
  intro K B hg _ hint ε hε
  set R := Algebra.adjoin K.O {B.g} with hR
  have hσR : ∀ y : R, B.σ (y : B.A) ∈ R := fun y => σ_mem_adjoin B hg hint y.2
  let τ : R ≃+* R :=
    { toFun := fun y => ⟨B.σ (y : B.A), hσR y⟩
      invFun := fun y => ⟨B.σ (y : B.A), hσR y⟩
      left_inv := fun y => Subtype.ext (B.σ_σ (y : B.A))
      right_inv := fun y => Subtype.ext (B.σ_σ (y : B.A))
      map_mul' := fun x y => Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
      map_add' := fun x y => Subtype.ext (map_add B.σ (x : B.A) (y : B.A)) }
  have hτc : ∀ y : R, ((τ y : R) : B.A) = B.σ y := fun y => rfl
  have hτ : ∀ y, τ (τ y) = y := fun y => Subtype.ext (B.σ_σ (y : B.A))

  obtain ⟨ε', hε'c, hε'u, hεε, hσε⟩ : ∃ ε' : R, (ε' : B.A) = ε ∧ IsUnit ε' ∧ ε * ε = 1 ∧ B.σ ε = ε := by
    rcases hε with rfl | rfl
    · exact ⟨1, by simp, isUnit_one, by simp, by simp⟩
    · exact ⟨-1, by simp, isUnit_one.neg, by simp, by simp⟩

  let g' : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  let h' : R := τ g'
  have hgh : g' * h' = 1 := Subtype.ext hg
  have hh'u : IsUnit h' := ⟨⟨h', g', by rw [mul_comm]; exact hgh, hgh⟩, rfl⟩

  obtain ⟨x0, y0, hxy, hxy0⟩ := K.c_res
  have hcx : cO K x0 = y0 := IsFractionRing.injective K.O K.E (by rw [algebraMap_cO, hxy])
  have hx : IsUnit (τ (algebraMap K.O R x0) - algebraMap K.O R x0) := by
    have hu : IsUnit (y0 - x0) := by
      have : IsUnit (x0 - y0) := by
        by_contra hn; exact hxy0 ((IsLocalRing.mem_maximalIdeal _).2 hn)
      simpa [neg_sub] using this.neg
    have : τ (algebraMap K.O R x0) - algebraMap K.O R x0 = algebraMap K.O R (y0 - x0) := by
      apply Subtype.ext
      simp only [hτc, Subalgebra.coe_sub, Subalgebra.coe_algebraMap, σ_algebraMap_O, hcx, map_sub]
    rw [this]; exact hu.map _
  obtain ⟨y, hy⟩ := exists_isUnit_add_mul_twist τ hτ (ε' * h') (hε'u.mul hh'u) (maximal_finite B hint) _ hx
  refine ⟨Units.map (R.val : R →* B.A) hy.unit, ?_, ?_, ?_⟩
  · have hc : ((Units.map (R.val : R →* B.A) hy.unit : B.Aˣ) : B.A) = (y : B.A) + ε * B.σ B.g * B.σ y := by
      simp [Units.coe_map, IsUnit.unit_spec, hε'c, hτc, h', g', mul_assoc]
    rw [hc, map_add, map_mul, map_mul, hσε, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ (y : B.A)) * ε * ε) * hg - B.σ (y : B.A) * hεε
  · simp only [Units.coe_map]; exact (hy.unit : R).2
  · rw [← map_inv]; simp only [Units.coe_map]; exact ((hy.unit⁻¹ : Rˣ) : R).2
end GlobalTheory.UnitLemma.UnitBase
