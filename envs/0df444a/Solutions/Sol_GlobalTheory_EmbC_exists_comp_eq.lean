-- Prove2me | solution 1 for GlobalTheory.EmbC.exists_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:20.660938+00:00
-- url     : https://prove2.me/submissions/ba5b45a1-983f-4e69-8430-c59bbbfc5595

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MkTensorLe
import Theorems.Thm_GlobalTheory_EmbC_exists_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbC
open Cardinal TensorProduct
namespace GlobalTheory.EmbC
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (f f' : R →+* ℂ)
    (hf : Function.Injective f) (hf' : Function.Injective f') :
    ∃ σ σ' : ℂ →+* ℂ, σ.comp f = σ'.comp f' :=
  @exists_emb R ℂ ℂ _ _ _ _ _ f.toAlgebra f'.toAlgebra Cardinal.mk_complex Cardinal.mk_complex hf hf'
end GlobalTheory.EmbC
