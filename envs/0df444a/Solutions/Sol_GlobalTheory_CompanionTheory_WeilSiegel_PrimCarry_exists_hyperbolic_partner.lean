-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_hyperbolic_partner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:05:13.089824+00:00
-- url     : https://prove2.me/submissions/6320e935-27b9-4a14-bbfa-dd1695db79dd

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HyperbolicPairUnitaryTransitive
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
open GlobalTheory.CompanionTheory.SW.QuasiRefl
variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}
namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
theorem _root_.solution (hτ : ∀ y, τ (τ y) = y) (h2 : IsUnit (2 : A))
    {Hi : Matrix (Fin N) (Fin N) A} (hHi : H * Hi = 1) (hH : ∀ i j, τ (H j i) = H i j)
    (y a : Fin N → A) (hyy : hform τ H y y = 0) (hay : ∑ k, a k * y k = 1) :
    ∃ y₁ : Fin N → A, hform τ H y₁ y₁ = 0 ∧ hform τ H y y₁ = 1 := by
  have hyw : hform τ H y (Hi *ᵥ (τ ∘ a)) = 1 := by
    rw [hform_eq_dot, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]
    have h : (τ ∘ y) ⬝ᵥ (τ ∘ a) = τ (∑ k, a k * y k) := by
      simp only [dotProduct, Function.comp_apply, map_sum, map_mul]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [h, hay, map_one]
  have hwy : hform τ H (Hi *ᵥ (τ ∘ a)) y = 1 := by
    rw [← hform_conj_symm hτ hH y (Hi *ᵥ (τ ∘ a)), hyw, map_one]
  have hww : τ (hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := hform_conj_symm hτ hH _ _
  have ht2 : 2 * (↑h2.unit⁻¹ : A) = 1 := h2.mul_val_inv
  have hτt : τ (↑h2.unit⁻¹ : A) = ↑h2.unit⁻¹ := by
    have h1 : τ (↑h2.unit⁻¹ : A) * 2 = 1 := by
      have h := congrArg τ ht2
      rw [map_mul, map_one, map_ofNat] at h
      rw [mul_comm]
      exact h
    calc τ (↑h2.unit⁻¹ : A) = τ (↑h2.unit⁻¹ : A) * (2 * ↑h2.unit⁻¹) := by rw [ht2, mul_one]
      _ = (τ (↑h2.unit⁻¹ : A) * 2) * ↑h2.unit⁻¹ := by ring
      _ = ↑h2.unit⁻¹ := by rw [h1, one_mul]
  have hτc : τ ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      (↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := by
    rw [map_mul, hτt, hww]
  refine ⟨Hi *ᵥ (τ ∘ a) - ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) • y, ?_, ?_⟩
  · rw [hform_sub_left, hform_sub_right, hform_sub_right, hyy, hwy, hyw, hτc]
    linear_combination (-1 : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) * ht2
  · rw [hform_sub_right, hyw, hyy, mul_zero, sub_zero]
end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
