-- Prove2me | solution 1 for HadwigerMader.card_edgeFinset_le_of_not_isMinor_K5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:29.721621+00:00
-- url     : https://prove2.me/submissions/d03aa9b0-3f6c-4fc7-97b8-fb81b0028607

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_HadwigerMader_isMinor_K5_of_card_edgeFinset
public import Theorems.Thm_CliqueMinors_isMinor_K5_of_card_edgeFinset


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}
namespace HadwigerMader
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  by_contra hlt
  exact h (isMinor_K5_of_card_edgeFinset G hn (by omega))
end HadwigerMader
