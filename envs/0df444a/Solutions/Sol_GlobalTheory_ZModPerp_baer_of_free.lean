-- Prove2me | solution 1 for GlobalTheory.ZModPerp.baer_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:30.715376+00:00
-- url     : https://prove2.me/submissions/36ab9aa6-7172-4e1b-bc51-5d0529cf9891

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod
import Theorems.Thm_GlobalTheory_ZModPerp_baer_zmod

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
theorem _root_.solution {n : ℕ} [NeZero n] (M : Type*) [AddCommGroup M] [Module (ZMod n) M]
    [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M] : Module.Baer (ZMod n) M := by
  let b := Module.Free.chooseBasis (ZMod n) M
  refine Module.Baer.of_equiv b.equivFun.symm fun I g => ?_
  choose l hl using fun i => baer_zmod n I ((LinearMap.proj i).comp g)
  exact ⟨LinearMap.pi l, fun x hx => funext fun i => hl i x hx⟩
end GlobalTheory.ZModPerp
