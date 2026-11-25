-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:48.373201+00:00
-- url     : https://prove2.me/submissions/630a5245-aed3-4f18-b5b8-4fc32537b5fb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HyperbolicPairUnitaryTransitive
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_hform_add_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_hform_add_snd
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_hform_sub_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_hform_sub_snd
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_hform_unitary
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_carry
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_exists_hyperbolic_partner
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
namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) →
    (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) →
    ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) →
    ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 →
    hform τ H y y = 0 → ∑ k, a k * y k = 1 →
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  intro A _ τ hτ h2 hcar N H Hi hHi hH e f y a hee hff hef hyy hay
  obtain ⟨y₁, hy₁, hyy₁⟩ := exists_hyperbolic_partner hτ h2 hHi hH y a hyy hay
  have hfe : hform τ H f e = 1 := by rw [← hform_conj_symm hτ hH e f, hef, map_one]
  have hy₁y : hform τ H y₁ y = 1 := by rw [← hform_conj_symm hτ hH y y₁, hyy₁, map_one]
  have hx1 : hform τ H (e + f) (e + f) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    norm_num
  have hy1 : hform τ H (y + y₁) (y + y₁) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    norm_num
  obtain ⟨g₁, hg₁, hg₁x, -⟩ := carry hτ hcar hH (e + f) (y + y₁) (by rw [hx1, hy1]) (by rw [hx1]; exact h2)
  have hvv : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) = -2 := by
    rw [hform_unitary hg₁, hform_sub_fst, hform_sub_snd, hform_sub_snd, hee, hef, hfe, hff]
    ring
  have hyy' : hform τ H (y - y₁) (y - y₁) = -2 := by
    rw [hform_sub_fst, hform_sub_snd, hform_sub_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have h2' : IsUnit (-2 : A) := h2.neg
  obtain ⟨g₂, hg₂, hg₂v, hfix⟩ := carry hτ hcar hH ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y - y₁)
    (by rw [hvv, hyy']) (by rw [hvv]; exact h2')
  have hperp1 : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y + y₁) = 0 := by
    rw [← hg₁x, hform_unitary hg₁, hform_sub_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    ring
  have hperp2 : hform τ H (y - y₁) (y + y₁) = 0 := by
    rw [hform_sub_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have hfix' := hfix (y + y₁) hperp1 hperp2
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  have hsum : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e + f) = y + y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁x, hfix']
  have hdiff : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e - f) = y - y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₂v]
  have key : (2 : A) • (((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ e) = (2 : A) • y := by
    have h : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ ((e + f) + (e - f)) = (y + y₁) + (y - y₁) := by
      rw [Matrix.mulVec_add, hsum, hdiff]
    have he : (e + f) + (e - f) = (2 : A) • e := by
      rw [two_smul]
      abel
    have hy : (y + y₁) + (y - y₁) = (2 : A) • y := by
      rw [two_smul]
      abel
    rw [he, Matrix.mulVec_smul, hy] at h
    exact h
  have h3 := congrArg (fun z => (↑h2.unit⁻¹ : A) • z) key
  simp only [smul_smul, h2.val_inv_mul, one_smul] at h3
  exact h3
end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
