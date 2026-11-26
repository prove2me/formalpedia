-- Prove2me | solution 1 for MurtySimon.IsDiameterTwoCritical.isCritical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:24.139801+00:00
-- url     : https://prove2.me/submissions/844120fe-f24c-4907-b37f-b62cccaef448

module
public import Mathlib
public import Definitions.Def_MurtySimon_Defs
public import Theorems.Thm_MurtySimon_ediam_le_two_iff

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open SimpleGraph
variable {V : Type*}
namespace MurtySimon
namespace IsDiameterTwoCritical
theorem _root_.solution {G : SimpleGraph V} (h : IsDiameterTwoCritical G) :
    IsCritical G := by
  refine ⟨(ediam_le_two_iff G).1 h.1.le, fun e he hd => ?_⟩
  have := (ediam_le_two_iff _).2 hd
  exact absurd (h.2 e he) (not_lt.2 this)
end IsDiameterTwoCritical
end MurtySimon
