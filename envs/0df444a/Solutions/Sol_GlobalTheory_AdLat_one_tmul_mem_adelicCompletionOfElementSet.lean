-- Prove2me | solution 1 for GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:45.083655+00:00
-- url     : https://prove2.me/submissions/240e5507-bdc4-414e-825f-f53a26334bb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Theorems.Thm_GlobalTheory_AdLat_adele_one_integral
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral

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
theorem _root_.solution {J : Set E} {x : E} (hx : x ∈ J) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F J :=
  tmul_mem_adelicCompletion_of_integral F (adele_one_integral F) hx
end GlobalTheory.AdLat
