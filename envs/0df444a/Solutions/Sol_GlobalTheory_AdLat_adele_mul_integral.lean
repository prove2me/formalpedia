-- Prove2me | solution 1 for GlobalTheory.AdLat.adele_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:13.918814+00:00
-- url     : https://prove2.me/submissions/b95fa2cd-9d63-4277-9f9b-14d74daaa226

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
    (a * b) v ∈ v.adicCompletionIntegers F := by
  have : (a * b) v = a v * b v := RestrictedProduct.mul_apply _ a b v
  rw [this]; exact mul_mem ha hb
end GlobalTheory.AdLat
