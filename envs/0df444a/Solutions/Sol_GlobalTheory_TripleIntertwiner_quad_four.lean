-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.quad_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:40.793439+00:00
-- url     : https://prove2.me/submissions/b2f4b83f-8934-40d5-afcb-dbad0c185882

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution {M G : Type*} [AddCommGroup M] [AddCommGroup G] (β : M →+ M →+ G) (a b c d : ℤ)
    (x y z w : M) :
    β (a • x - b • y - c • z - d • w) (a • x - b • y - c • z - d • w) +
      β (b • x + a • y - d • z + c • w) (b • x + a • y - d • z + c • w) +
      β (c • x + d • y + a • z - b • w) (c • x + d • y + a • z - b • w) +
      β (d • x - c • y + b • z + a • w) (d • x - c • y + b • z + a • w) =
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (β x x + β y y + β z z + β w w) := by
  simp only [map_add, map_sub, map_zsmul, AddMonoidHom.add_apply,
      AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply]
  module
end GlobalTheory.TripleIntertwiner
