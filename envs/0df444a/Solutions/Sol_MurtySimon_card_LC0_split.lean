-- Prove2me | solution 1 for MurtySimon.card_LC0_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:35.272128+00:00
-- url     : https://prove2.me/submissions/178d16c5-908c-4280-8265-ff59ec13fd89

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution (M : Finset (Sym2 V)) (C : (aux G ∅).ConnectedComponent) :
    #((LC0 C).filter (· ∉ M)) + #((LC0 C).filter (· ∈ M)) = cA G ∅ C := by
  rw [add_comm]; exact card_filter_add_card_filter_not _
end MurtySimon
