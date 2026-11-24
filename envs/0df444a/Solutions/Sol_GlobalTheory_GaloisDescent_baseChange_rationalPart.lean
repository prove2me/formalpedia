-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.baseChange_rationalPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:43:32.003546+00:00
-- url     : https://prove2.me/submissions/87569f0c-093c-4910-9273-9aaa56efe467

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_span_image_comap_eq
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
import Theorems.Thm_GlobalTheory_GaloisDescent_baseChange_eq_span_image
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul
attribute [local simp] GlobalTheory.GaloisDescent.mem_rationalPart
attribute [local simp] GlobalTheory.GaloisDescent.rationalPart_baseChange

set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (W : Submodule L (L ⊗[K] V)) (hW : ∀ g, ∀ w ∈ W, (s g).toLinearMap.rTensor V w ∈ W) :
    (rationalPart K W).baseChange L = W := by
  rw [baseChange_eq_span_image]
  exact span_image_comap_eq (TensorProduct.isBaseChange K V L) (fun g => (s g).toRingHom) hs
    (fun g => ((s g).toLinearMap.rTensor V).toAddMonoidHom)
    (fun g a v => by simp [smul_tmul']) W hW
end GlobalTheory.GaloisDescent
