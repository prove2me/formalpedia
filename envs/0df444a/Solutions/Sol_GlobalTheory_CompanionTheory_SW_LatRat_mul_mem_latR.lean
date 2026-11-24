-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.mul_mem_latR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:50:28.56864+00:00
-- url     : https://prove2.me/submissions/f88e8591-4ccf-4afe-bb98-6be0403dd851

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_repr_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.LatRat
theorem _root_.solution {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {e : E}
    (he : Good b v e) {y : Fv F v ⊗[F] E} (hy : y ∈ latR b v) : y * inclR (Fv F v) e ∈ latR b v := by
  intro l
  rw [repr_mul]
  exact sum_mem fun k _ => mul_mem (hy k) (he k l)
end GlobalTheory.CompanionTheory.SW.LatRat
