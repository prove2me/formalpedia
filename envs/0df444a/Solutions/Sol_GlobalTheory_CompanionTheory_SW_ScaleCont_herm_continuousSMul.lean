-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ScaleCont.herm_continuousSMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:50:35.641188+00:00
-- url     : https://prove2.me/submissions/5b539684-9590-427b-8902-a284b3432362

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousActionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresSupportStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ScaleCont_continuous_inv_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ScaleCont
variable {K : Type} [CommRing K] {n M : ℕ}
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace GlobalTheory.CompanionTheory.SW.ScaleCont
theorem _root_.solution (s : K →+* K) (hs : Continuous s)
    (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    @ContinuousSMul (GL (Fin n) K) H (hermAction s H hmem).toSMul _ _ := by
  letI := hermAction s H hmem
  refine ⟨?_⟩
  have hq : Continuous fun p : GL (Fin n) K × H =>
      ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := continuous_inv_val.comp continuous_fst
  have hS : Continuous fun p : GL (Fin n) K × H => (p.2 : Matrix (Fin n) (Fin n) K) :=
    continuous_subtype_val.comp continuous_snd
  have hc : Continuous fun p : GL (Fin n) K × H =>
      cT s ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simp only [cT]
    exact (hq.matrix_map hs).matrix_transpose
  exact ((hc.matrix_mul hS).matrix_mul hq).subtype_mk _
end GlobalTheory.CompanionTheory.SW.ScaleCont
