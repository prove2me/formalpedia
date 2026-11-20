-- Prove2me | solution 1 for NOF.Protocol.le_complexity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:15:08.991064+00:00
-- url     : https://prove2.me/submissions/9da41816-c442-40f8-be6b-6583ac9649f6

module
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Defs
public import Definitions.Def_ChandraFurstLipton_NOFModel
public import Theorems.Thm_NOF_Protocol_broadcast_zero
public import Theorems.Thm_NOF_Protocol_length_broadcast
attribute [local simp] NOF.Protocol.broadcast_zero
attribute [local simp] NOF.Protocol.length_broadcast

set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {d : ℕ} [Fintype ι]
variable {F : (ZMod d → G) → Bool} {P : Protocol G d} {a : ZMod d → ZMod d → G} {v : ZMod d → G}
  {B : List Bool} {t : ℕ}
open NOF.Protocol
namespace NOF.Protocol
theorem _root_.solution : t ≤ Protocol.complexity P F ↔ ∀ r : ℕ, P.IsValid F r → t ≤ r := by
  simp [complexity, ENat.natCast_le_natCast]
end NOF.Protocol
