-- Prove2me | solution 1 for GlobalTheory.AdLat.adele_add_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:45.621739+00:00
-- url     : https://prove2.me/submissions/c4408aaf-9110-49b5-88c5-fabf3bd6fa9b

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
theorem _root_.solution {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a + b) v ∈ v.adicCompletionIntegers F := by
  have : (a + b) v = a v + b v := RestrictedProduct.add_apply _ a b v
  rw [this]; exact add_mem ha hb
end GlobalTheory.AdLat
