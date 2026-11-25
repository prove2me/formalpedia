-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.map_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:47.957158+00:00
-- url     : https://prove2.me/submissions/643982a7-1e71-48b2-a2c2-0ec665ded3d7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger MulAction
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {Γ : Type*} [Group Γ] {H : Subgroup Γ} [H.FiniteIndex] {B C : Type*} [CommGroup B]
    [CommGroup C] (φ : H →* B) (f : B →* C) (g : Γ) : f (φ.transfer g) = (f.comp φ).transfer g := by
  classical
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers g) (Γ ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, map_prod]
  rfl
end GroundTheory.LocalField.Abstract
