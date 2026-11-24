-- Prove2me | solution 1 for GlobalTheory.posDef_realExt_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:42:21.029876+00:00
-- url     : https://prove2.me/submissions/6bfed07d-bac3-4b1c-924d-42d7f8f86628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_posDef_of_tendsto_comp
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_GlobalTheory_span_range_one_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution [Module.Finite ℤ X] (Q : QuadraticMap ℤ X ℝ)
    (h : Tendsto Q cofinite atTop) : (realExt Q).PosDef :=
  posDef_of_tendsto_comp (TensorProduct.mk ℤ ℝ X 1).toAddMonoidHom span_range_one_tmul _
    (h.congr fun x => by simp)
end GlobalTheory
