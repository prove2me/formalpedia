-- Prove2me | solution 1 for NOF.le_funComplexity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:15:52.524451+00:00
-- url     : https://prove2.me/submissions/a5eb767c-6181-4f64-adb1-aec9dfd688f7

module
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Defs
public import Definitions.Def_ChandraFurstLipton_NOFModel
public import Theorems.Thm_NOF_Protocol_broadcast_zero
public import Theorems.Thm_NOF_Protocol_length_broadcast
public import Theorems.Thm_NOF_Protocol_le_complexity
attribute [local simp] NOF.Protocol.broadcast_zero
attribute [local simp] NOF.Protocol.length_broadcast
attribute [local simp] NOF.Protocol.le_complexity

set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {d : ℕ} [Fintype ι]
variable {F : (ZMod d → G) → Bool} {P : Protocol G d} {a : ZMod d → ZMod d → G} {v : ZMod d → G}
  {B : List Bool} {t : ℕ}
namespace NOF
theorem _root_.solution : t ≤ funComplexity F ↔ ∀ P : Protocol G d, t ≤ P.complexity F := by
  simp [funComplexity]
end NOF
