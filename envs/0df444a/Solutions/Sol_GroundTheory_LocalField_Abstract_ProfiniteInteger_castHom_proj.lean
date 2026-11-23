-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.castHom_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:29.424598+00:00
-- url     : https://prove2.me/submissions/f364f09c-0c29-4658-9760-53cdb031b5ce

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger

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
open GroundTheory.LocalField.Abstract.ProfiniteInteger
namespace GroundTheory.LocalField.Abstract.ProfiniteInteger
theorem _root_.solution {m n : ℕ+} (h : (m : ℕ) ∣ n) (x : ℤ̂) :
    ZMod.castHom h (ZMod m) (proj n x) = proj m x :=
  mem_profiniteIntegers.1 x.2 m n h
end GroundTheory.LocalField.Abstract.ProfiniteInteger
