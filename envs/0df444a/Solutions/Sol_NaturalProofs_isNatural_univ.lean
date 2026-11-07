-- Prove2me | solution 1 for NaturalProofs.isNatural_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:33.077136+00:00
-- url     : https://prove2.me/submissions/80a3dfcd-f81c-453c-aa63-5d1f2c6674e3

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_Sanity

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
namespace NaturalProofs
theorem _root_.solution : IsNatural (fun _ => Set.univ) := by
  classical
  refine ⟨fun _ => Set.univ, fun _ => le_rfl, ⟨0, 0, fun n _ => ⟨⟨[], .const true⟩, ?_, ?_⟩⟩,
    ⟨0, 0, fun n _ => ?_⟩⟩
  · simp [Circuit.size]
  · intro f
    simp [Circuit.eval, Wire.eval]
  · simp
end NaturalProofs
