-- Prove2me | solution 1 for GlobalTheory.DetFactor.map_diagGL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:31.576451+00:00
-- url     : https://prove2.me/submissions/e8844a4a-db8c-4028-a5cc-4adf6b041b9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
import Theorems.Thm_GlobalTheory_DetFactor_toGL_val
import Theorems.Thm_GlobalTheory_DetFactor_map_diagGL_perm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DetFactor.toGL_val

set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory.DetFactor
theorem _root_.solution (c : GL (Fin (m + 1)) k →* ℂˣ) (d : Fin (m + 1) → kˣ) :
    c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0) (∏ i, d i) := by
  have hs : ∀ i (x : kˣ), c (diagGL (m + 1) (Pi.mulSingle i x)) = c (diagGL (m + 1) (Pi.mulSingle 0 x)) := by
    intro i x
    rw [← map_diagGL_perm c (Equiv.swap 0 i) (Pi.mulSingle i x)]
    congr 2
    funext a
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have e : c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))) (∏ i, Pi.mulSingle i (d i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod, map_prod]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply]
  exact Finset.prod_congr rfl (fun i _ => hs i (d i))
end GlobalTheory.DetFactor
