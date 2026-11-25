-- Prove2me | solution 1 for GlobalTheory.linearIndependent_ringHom_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:31.540892+00:00
-- url     : https://prove2.me/submissions/5a7156bd-870b-435f-aa14-401799b8b924

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LinearIndependentRingHomCompIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A F : Type} [CommRing A] [Field F] (φ : A →+* F)
    (hφ : Function.Injective φ) {ι μ : Type} [Finite μ] (c : ι → μ → A) :
    LinearIndependent F (fun i m => φ (c i m)) ↔ LinearIndependent A c := by
  letI : Algebra A F := φ.toAlgebra
  haveI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).2 hφ
  exact linearIndependent_algebraMap_comp_iff (R := A) (S := F) (v := c)
end GlobalTheory
