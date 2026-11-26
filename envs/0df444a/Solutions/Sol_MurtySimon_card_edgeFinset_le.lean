-- Prove2me | solution 1 for MurtySimon.card_edgeFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:26:32.85469+00:00
-- url     : https://prove2.me/submissions/5ce3198e-7073-43e4-9657-3dcba38a761e

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_two_mul_card_le
public import Theorems.Thm_MurtySimon_choose_two_add_half
public import Theorems.Thm_MurtySimon_two_mul_card_le_aux
public import Theorems.Thm_MurtySimon_exists_maximal_extension


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (hG : IsDiameterTwoCritical G) :
    #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by
  obtain ⟨M, -, hM⟩ := exists_maximal_extension (G := G) (N := ∅) ⟨by simp, by simp⟩
  have h1 := two_mul_card_le_aux hG hM
  have h2 := two_mul_card_le hM.1
  have h3 := choose_two_add_half (Fintype.card V)
  omega
end MurtySimon
