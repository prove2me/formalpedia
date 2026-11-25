-- Prove2me | solution 1 for GlobalTheory.CMCurves.isIntegral_latticeJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:52.567137+00:00
-- url     : https://prove2.me/submissions/48074496-1178-4501-a005-565606bc2b82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_ringOfIntegers
import Theorems.Thm_P2M_GlobalTheory_g__cube_div_eq_modularJ_a1bc96193403

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
namespace GlobalTheory
namespace CMCurves
variable {K : Type} [Field K] [NumberField K]
private theorem exists_ne_zero_upperHalfPlane_lattice_eq (L : PeriodPair) : ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧
    ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  have hind := LinearIndependent.pair_iff.1 L.indep
  have h1 : L.ω₁ ≠ 0 := fun h => by simpa using hind 1 0 (by simp [h])
  have h2 : L.ω₂ ≠ 0 := fun h => by simpa using hind 0 1 (by simp [h])
  have him : (L.ω₂ / L.ω₁).im ≠ 0 := by
    intro h
    have hr : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
      rw [← div_eq_iff h1]; exact Complex.ext (by simp) (by simp [h])
    have := hind (-(L.ω₂ / L.ω₁).re) 1 (by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; linear_combination hr)
    exact one_ne_zero this.2
  rcases lt_or_gt_of_ne him with hlt | hgt
  · have hpos : 0 < (L.ω₁ / L.ω₂).im := by
      rw [← inv_div, Complex.inv_im]
      exact div_pos (neg_pos.2 hlt) (Complex.normSq_pos.2 (div_ne_zero h2 h1))
    refine ⟨L.ω₂, UpperHalfPlane.mk _ hpos, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice, UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by field_simp⟩
    · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by field_simp⟩
  · refine ⟨L.ω₁, UpperHalfPlane.mk _ hgt, h1, fun x => ?_⟩
    rw [PeriodPair.mem_lattice, UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩; exact ⟨n, m, by field_simp; ring⟩
    · rintro ⟨m, n, rfl⟩; exact ⟨n, m, by field_simp; ring⟩
end CMCurves
end GlobalTheory
end
end

set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
open GlobalTheory
open GlobalTheory.CMCurves
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.CMCurves
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (L : PeriodPair)
    (hL : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) :
    IsIntegral ℤ (latticeJ L) := by
  obtain ⟨a, τ, ha, h⟩ := exists_ne_zero_upperHalfPlane_lattice_eq L
  rw [show latticeJ L = modularJ τ from g₂_cube_div_eq_modularJ ha h]
  have key : ∀ y, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := by
    intro y
    rw [Submodule.mem_span_pair, h]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by simp [zsmul_eq_mul]⟩
    · rintro ⟨m, n, e⟩
      exact ⟨m, n, by simpa [zsmul_eq_mul] using mul_left_cancel₀ ha e⟩
  refine isIntegral_modularJ_of_ringOfIntegers hK σ (fun α x hx => ?_)
  rw [key] at hx ⊢
  simpa [mul_left_comm] using hL α _ hx
end GlobalTheory.CMCurves
