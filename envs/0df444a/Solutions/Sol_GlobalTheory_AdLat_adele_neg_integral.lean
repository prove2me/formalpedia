-- Prove2me | solution 1 for GlobalTheory.AdLat.adele_neg_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:14.892799+00:00
-- url     : https://prove2.me/submissions/830016a8-0ac9-43a1-9a8b-72c330429e9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution {a : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) :
    (-a) v ∈ v.adicCompletionIntegers F := by
  have : (-a) v = -a v := RestrictedProduct.neg_apply _ a v
  rw [this]; exact neg_mem ha
end GlobalTheory.AdLat
