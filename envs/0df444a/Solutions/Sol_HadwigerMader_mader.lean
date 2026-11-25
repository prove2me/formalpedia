-- Prove2me | solution 1 for HadwigerMader.mader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:47.856819+00:00
-- url     : https://prove2.me/submissions/ed81bf39-b686-4ecd-ae10-81919ceef802

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_HadwigerMader_isMinor_iff_lib
public import Theorems.Thm_CliqueMinors_mader


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}
namespace HadwigerMader
theorem _root_.solution [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : 2 ^ r * Fintype.card V ≤ 8 * G.edgeFinset.card) :
    IsMinor (⊤ : SimpleGraph (Fin r)) G :=
  (isMinor_iff_lib _ G).2 (CliqueMinors.mader G r h)
end HadwigerMader
