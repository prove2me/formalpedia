-- Prove2me | solution 1 for NOF.Protocol.broadcast_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:14:10.874999+00:00
-- url     : https://prove2.me/submissions/4f712bb6-8816-4a0b-bc4a-a11ac3b7c6ba

module
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Defs
public import Definitions.Def_ChandraFurstLipton_NOFModel

set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {d : ℕ} [Fintype ι]
variable {F : (ZMod d → G) → Bool} {P : Protocol G d} {a : ZMod d → ZMod d → G} {v : ZMod d → G}
  {B : List Bool} {t : ℕ}
open NOF.Protocol
namespace NOF.Protocol
theorem _root_.solution (P : Protocol G d) (x : ZMod d → G) (t : ℕ) :
    broadcast P x (t + 1)
      = P.nextBit t (forget (t : ZMod d) x) (broadcast P x t) :: broadcast P x t := rfl
end NOF.Protocol
