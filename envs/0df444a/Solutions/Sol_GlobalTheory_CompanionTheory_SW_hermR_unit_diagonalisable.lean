-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.hermR_unit_diagonalisable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:25.873173+00:00
-- url     : https://prove2.me/submissions/3fbc2455-d77d-4f3e-a4d0-cc719318b5cb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnitStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHermitianDiagonalizationUnits
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_T_hermitian_unit_form_diagonalizes
import Theorems.Thm_GlobalTheory_T_hermitian_unit_form_represents_unit
import Theorems.Thm_GlobalTheory_T_tensor_involution_algebra_properties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (d : Fin n → Rˣ), IsUnit g.det ∧ (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * g := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ n S hS
  obtain ⟨hart, -, h2, hinv, hδ, hfix, hunit⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hσ R
  haveI : IsArtinianRing (R ⊗[F] E) := hart
  haveI : Finite (MaximalSpectrum (R ⊗[F] E)) := inferInstance
  have hrep := GlobalTheory.T.hermitian_unit_form_represents_unit (R ⊗[F] E) (sigR R σ) hinv h2 hδ
  obtain ⟨g, d, hg, hd, hgd⟩ :=
    GlobalTheory.T.hermitian_unit_form_diagonalizes (R ⊗[F] E) (sigR R σ) hinv hrep n (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S.2 hS
  choose r hr using fun i => hfix (d i) (hd i).2
  have hru : ∀ i, IsUnit (r i) := fun i => (hunit (r i)).1 (hr i ▸ (hd i).1)
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hdiag : Matrix.diagonal (fun i => (((hru i).unit : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) = Matrix.diagonal d := by
    congr 1
    funext i
    simp [hr i]
  refine ⟨g⁻¹, fun i => (hru i).unit, Matrix.isUnit_nonsing_inv_det g hg, ?_⟩
  rw [hdiag, ← hgd]
  have hc : cT (sigR R σ) g⁻¹ * cT (sigR R σ) g = 1 := by
    rw [← cT_mul, hgi, cT_one]
  calc (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))
      = (cT (sigR R σ) g⁻¹ * cT (sigR R σ) g) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g * g⁻¹) := by
        rw [hc, hgi, one_mul, mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW
