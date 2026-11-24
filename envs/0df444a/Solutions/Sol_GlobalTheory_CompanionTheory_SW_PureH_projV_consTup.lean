-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PureH.projV_consTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:51.074906+00:00
-- url     : https://prove2.me/submissions/eb7ed239-806f-4800-9768-fc2b32b3f831

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_map_consTup

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PureH
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PureH
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (consTup X) = consTup (projV v X) :=
  map_consTup (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) (map_zero _) (map_one _) X
end GlobalTheory.CompanionTheory.SW.PureH
