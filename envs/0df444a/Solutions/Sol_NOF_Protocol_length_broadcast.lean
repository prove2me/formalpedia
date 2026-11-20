-- Prove2me | solution 1 for NOF.Protocol.length_broadcast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:14:35.80218+00:00
-- url     : https://prove2.me/submissions/e0ead133-04a4-409f-b8a0-1a046be93ddf

module
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Defs
public import Definitions.Def_ChandraFurstLipton_NOFModel
public import Theorems.Thm_NOF_Protocol_broadcast_zero
public import Theorems.Thm_NOF_Protocol_broadcast_succ
attribute [local simp] NOF.Protocol.broadcast_zero

set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {d : ℕ} [Fintype ι]
variable {F : (ZMod d → G) → Bool} {P : Protocol G d} {a : ZMod d → ZMod d → G} {v : ZMod d → G}
  {B : List Bool} {t : ℕ}
open NOF.Protocol
namespace NOF.Protocol
theorem _root_.solution (P : Protocol G d) (x : ZMod d → G) : ∀ t, (broadcast P x t).length = t
  | 0 => rfl
  | t + 1 => by simpa [broadcast_succ] using solution _ _ _
end NOF.Protocol
