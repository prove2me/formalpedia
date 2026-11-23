-- Prove2me | solution 1 for GlobalTheory.NormCompat.valued_locUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:32.147996+00:00
-- url     : https://prove2.me/submissions/3bb78269-d92a-4a48-8581-29c974b00ec1

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ProdLocalValuesGlobalOverPlacesAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.NormCompat
namespace GlobalTheory.NormCompat
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : Fˣ) :
    Valued.v ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = v.valuation F (b : F) := by
  show Valued.v ((b : F) : v.adicCompletion F) = _
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
end GlobalTheory.NormCompat
