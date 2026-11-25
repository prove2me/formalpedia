-- Prove2me | solution 1 for HadwigerMader.card_edgeFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:37.842636+00:00
-- url     : https://prove2.me/submissions/c906e194-6339-4a20-a546-874c28393709

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
public import Theorems.Thm_HadwigerMader_isMinor_iff_lib
public import Theorems.Thm_CliqueMinors_card_edgeFinset_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}
namespace HadwigerMader
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V :=
  CliqueMinors.card_edgeFinset_le G hn (fun h' => h ((isMinor_iff_lib _ G).2 h'))
end HadwigerMader
