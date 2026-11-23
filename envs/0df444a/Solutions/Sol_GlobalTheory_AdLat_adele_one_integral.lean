-- Prove2me | solution 1 for GlobalTheory.AdLat.adele_one_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:23.824079+00:00
-- url     : https://prove2.me/submissions/b923bcae-7511-4fce-ba72-99bf47481e65

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := RestrictedProduct.one_apply _ _
  rw [this]; exact one_mem _
end GlobalTheory.AdLat
