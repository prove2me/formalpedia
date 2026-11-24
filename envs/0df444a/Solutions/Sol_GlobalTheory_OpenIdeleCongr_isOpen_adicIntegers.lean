-- Prove2me | solution 1 for GlobalTheory.OpenIdeleCongr.isOpen_adicIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:16:13.902999+00:00
-- url     : https://prove2.me/submissions/8c79c746-1397-4362-ae12-0ee5db13ef71

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenIdeleSubgroupContainsCongruenceUnits

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
open GlobalTheory GlobalTheory.OpenIdeleCongr
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.OpenIdeleCongr
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  Valued.isOpen_valuationSubring _
end GlobalTheory.OpenIdeleCongr
