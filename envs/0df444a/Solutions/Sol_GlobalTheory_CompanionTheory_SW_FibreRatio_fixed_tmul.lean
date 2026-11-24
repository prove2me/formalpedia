-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreRatio.fixed_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:29:34.588629+00:00
-- url     : https://prove2.me/submissions/4e15911a-4f3b-46d0-86f9-0ae0891eb6fa

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_exists_imag
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_sigR_tmul
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_sigR_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreRatio
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [Field R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.FibreRatio
theorem _root_.solution (h : IsCMExt F E σ) (y : R ⊗[F] E) (hy : sigR R σ y = y) :
    ∃ r : R, y = r ⊗ₜ[F] (1 : E) := by
  obtain ⟨w, hw, hspan⟩ := exists_imag h
  have hdec : ∀ y : R ⊗[F] E, ∃ r t : R, y = r ⊗ₜ[F] (1 : E) + t ⊗ₜ[F] w := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul r e =>
      obtain ⟨a, c, rfl⟩ := hspan e
      refine ⟨a • r, c • r, ?_⟩
      rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨r, t, rfl⟩ := hx
      obtain ⟨r', t', rfl⟩ := hy
      refine ⟨r + r', t + t', ?_⟩
      rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel
  obtain ⟨r, t, rfl⟩ := hdec y
  refine ⟨r, ?_⟩
  have h1 : sigR R σ (t ⊗ₜ[F] w) = -(t ⊗ₜ[F] w) := by
    rw [sigR_tmul, hw, TensorProduct.tmul_neg]
  have h0 : sigR R σ (r ⊗ₜ[F] (1 : E)) = r ⊗ₜ[F] (1 : E) := by
    rw [sigR_tmul, map_one]
  rw [map_add, h0, h1] at hy
  have h2 : (2 : F) • (t ⊗ₜ[F] w) = 0 := by
    have : t ⊗ₜ[F] w = -(t ⊗ₜ[F] w) := (add_left_cancel hy).symm
    rw [two_smul]
    nth_rw 1 [this]
    abel
  have h3 : t ⊗ₜ[F] w = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [h3, add_zero]
end GlobalTheory.CompanionTheory.SW.FibreRatio
