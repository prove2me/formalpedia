-- Prove2me | solution 1 for NaturalProofs.usefulAgainstPPoly_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:43.986995+00:00
-- url     : https://prove2.me/submissions/69f51826-eeac-48e5-a606-715f943cad0a

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_Sanity

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
namespace NaturalProofs
theorem _root_.solution : UsefulAgainstPPoly (fun _ => ∅) :=
  fun _ => ⟨0, fun _ _ f hf => by simp at hf⟩
end NaturalProofs
