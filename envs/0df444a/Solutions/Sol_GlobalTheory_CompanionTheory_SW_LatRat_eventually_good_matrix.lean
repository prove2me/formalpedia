-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.eventually_good_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:52:05.82726+00:00
-- url     : https://prove2.me/submissions/11e25e05-bf1e-4d41-9b60-ef02d0dffe0a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_eventually_good

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
theorem _root_.solution {d m : ℕ} (b : Module.Basis (Fin d) F E) (g : Matrix (Fin m) (Fin m) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Good b v (g i j) :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_good b _
end GlobalTheory.CompanionTheory.SW.LatRat
