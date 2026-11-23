-- Prove2me | solution 1 for GlobalTheory.WeilCont.pureA_adeleJoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:06.803223+00:00
-- url     : https://prove2.me/submissions/5709f1dc-d080-465c-bb00-7de006958031

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsContOnOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical
open GlobalTheory GlobalTheory.WeilCont
variable (F : Type) [Field F] [NumberField F] {κ : Type}
namespace GlobalTheory.WeilCont
theorem _root_.solution (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (adeleJoin F x y) = f x * g y := by
  simp [GlobalTheory.WeilM.pureA, adeleJoin]
end GlobalTheory.WeilCont
