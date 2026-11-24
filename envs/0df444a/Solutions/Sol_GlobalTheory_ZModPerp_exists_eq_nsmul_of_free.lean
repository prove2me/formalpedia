-- Prove2me | solution 1 for GlobalTheory.ZModPerp.exists_eq_nsmul_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:09.189919+00:00
-- url     : https://prove2.me/submissions/ede1bb26-2165-4632-bcae-3d81afbd0c99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod
import Theorems.Thm_GlobalTheory_ZModPerp_exists_eq_nsmul_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory GlobalTheory.ZModPerp
namespace GlobalTheory.ZModPerp
theorem _root_.solution {n r N : ℕ} [NeZero n] (h : r * N = n) {M : Type*}
    [AddCommGroup M] [Module (ZMod n) M] [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M]
    (y : M) (hy : N • y = 0) : ∃ z : M, y = r • z := by
  let b := Module.Free.chooseBasis (ZMod n) M
  choose z hz using fun i => exists_eq_nsmul_zmod h (b.equivFun y i) (by
    rw [← Pi.smul_apply, ← map_nsmul, hy, map_zero, Pi.zero_apply])
  refine ⟨b.equivFun.symm z, b.equivFun.injective ?_⟩
  rw [map_nsmul, LinearEquiv.apply_symm_apply]
  exact funext hz
end GlobalTheory.ZModPerp
