-- Prove2me | solution 1 for GlobalTheory.finrank_span_ringHom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:16.873749+00:00
-- url     : https://prove2.me/submissions/5ac78933-955b-4b3f-9216-043a8187840c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LinearIndependentRingHomCompIff
import Theorems.Thm_GlobalTheory_finrank_span_ringHom_comp_le

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
theorem _root_.solution {A F F' : Type} [CommRing A] [Field F] [Field F']
    (φ : A →+* F) (ψ : A →+* F') (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    {ι μ : Type} [Finite ι] [Finite μ] (c : ι → μ → A) :
    Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) =
      Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) :=
  le_antisymm (finrank_span_ringHom_comp_le φ ψ hφ hψ c)
    (finrank_span_ringHom_comp_le ψ φ hψ hφ c)
end GlobalTheory
