-- Prove2me | solution 1 for GlobalTheory.DI.prodL_eq_zero_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:12:39.40327+00:00
-- url     : https://prove2.me/submissions/5516d219-c203-4b4f-bbc7-8035f52c9e3e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAntisymmetrizedCupProductVanishAboveDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) (t : Finset ι)
    (ht : vs.length + 1 < t.card) : prodL f h vs t = 0 := by
  induction vs generalizing t with
  | nil =>
    simp only [prodL, List.foldr_nil, oneC]
    simp only [List.length_nil] at ht
    rw [if_neg (by omega)]
  | cons v vs ih =>
    change Lop f h v (prodL f h vs) t = 0
    simp only [List.length_cons] at ht
    unfold Lop
    split_ifs with h1 h2
    · have e1 := ih t (by omega)
      have e2 := ih (t.erase (t.min' h1))
        (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega)
      rw [e1, e2, mul_zero, smul_zero, smul_zero, add_zero]
    · have e1 := ih t (by omega)
      rw [e1, mul_zero, smul_zero, add_zero]
    · rfl
end GlobalTheory.DI
