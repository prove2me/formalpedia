-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.isClosedEmbedding_adeleMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:31:59.932485+00:00
-- url     : https://prove2.me/submissions/ccf45d2c-cf4d-4f30-9e91-610edb86cbaf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleRetraction_adeleMap
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_adeleRetraction
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_adeleMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution : IsClosedEmbedding (adeleMap K L) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 L) L) := inferInstanceAs (T2Space
    (Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]))
  haveI : T2Space (InfiniteAdeleRing L) :=
    inferInstanceAs (T2Space ((w : NumberField.InfinitePlace L) → w.Completion))
  haveI : T2Space 𝔸[L] := inferInstanceAs (T2Space (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))
  Function.LeftInverse.isClosedEmbedding (f := adeleRetraction K L) adeleRetraction_adeleMap
    continuous_adeleRetraction continuous_adeleMap
end GroundTheory.Global.AdeleBaseChange
