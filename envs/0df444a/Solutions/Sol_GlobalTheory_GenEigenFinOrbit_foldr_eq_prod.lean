-- Prove2me | solution 1 for GlobalTheory.GenEigenFinOrbit.foldr_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:19.33016+00:00
-- url     : https://prove2.me/submissions/d0db99db-78a8-48b6-9d06-2f580b0ce121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.GenEigenFinOrbit
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.GenEigenFinOrbit
theorem _root_.solution (χ : End ℂ V → ℂ) (zs : List (End ℂ V)) (v : V) :
    zs.foldr (fun z f => z f - χ z • f) v =
      (zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ z))).prod v := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp [ih, Module.End.mul_apply]
end GlobalTheory.GenEigenFinOrbit
