-- Prove2me | solution 1 for HadwigerMader.isMinor_K5_of_card_edgeFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:29.411613+00:00
-- url     : https://prove2.me/submissions/1f4c8eab-534a-40bb-9a25-33330f747857

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_HadwigerMader_isMinor_iff_lib
public import Theorems.Thm_CliqueMinors_isMinor_K5_of_card_edgeFinset


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}
namespace HadwigerMader
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : 3 * Fintype.card V ≤ G.edgeFinset.card + 5) :
    IsMinor (⊤ : SimpleGraph (Fin 5)) G := by
  classical
  refine (isMinor_iff_lib _ G).2 (CliqueMinors.isMinor_K5_of_card_edgeFinset G hn ?_)
  convert h using 2
  congr 1
  ext e
  simp
end HadwigerMader
