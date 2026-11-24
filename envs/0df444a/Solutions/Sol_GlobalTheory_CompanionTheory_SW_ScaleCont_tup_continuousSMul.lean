-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ScaleCont.tup_continuousSMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:18.831267+00:00
-- url     : https://prove2.me/submissions/1f46fb05-3696-442a-bcd4-895df7955f44

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
theorem _root_.solution :
    @ContinuousSMul (GL (Fin n) K) (Fin n → Fin M → K) (tupAction (K := K)).toSMul _ _ := by
  letI := tupAction (K := K) (n := n) (M := M)
  refine ⟨?_⟩
  show Continuous fun p : GL (Fin n) K × (Fin n → Fin M → K) =>
    tupR p.2 ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [tupR]
  refine continuous_finset_sum _ fun c _ => ?_
  refine Continuous.mul ?_ ?_
  · exact (continuous_apply i).comp ((continuous_apply c).comp continuous_snd)
  · exact (continuous_apply a).comp ((continuous_apply c).comp (continuous_inv_val.comp continuous_fst))
end GlobalTheory.CompanionTheory.SW.ScaleCont
