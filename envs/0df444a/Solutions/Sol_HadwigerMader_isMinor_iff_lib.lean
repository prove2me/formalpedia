-- Prove2me | solution 1 for HadwigerMader.isMinor_iff_lib
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:55.735076+00:00
-- url     : https://prove2.me/submissions/e4c18253-250e-45a2-8a7f-947a02f08815

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}
namespace HadwigerMader
theorem _root_.solution {V W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) :
    IsMinor H G ↔ CliqueMinors.IsMinor H G := by
  constructor
  · rintro ⟨M⟩
    exact ⟨⟨M.branch, M.branch_nonempty, M.branch_connected, M.branch_disjoint,
      M.branch_adjacent⟩⟩
  · rintro ⟨M⟩
    exact ⟨⟨M.branch, M.branch_nonempty, M.branch_connected, M.branch_disjoint,
      M.branch_adjacent⟩⟩
end HadwigerMader
