-- Prove2me | solution 1 for GlobalTheory.SumRefinement.finsum_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:50:04.410496+00:00
-- url     : https://prove2.me/submissions/0990c1bb-86f9-4ffb-9452-ae11a4eb52be

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SumRefinement
namespace GlobalTheory.SumRefinement
theorem _root_.solution {X F : Type} [Finite F] (g : X → ℂ) (hg : (Function.support g).Finite) :
    ∑ᶠ p : X × F, g p.1 = (Nat.card F : ℂ) * ∑ᶠ x, g x := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ) _ ?_,
    finsum_eq_sum_of_support_subset (s := hg.toFinset) _ (by simp),
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro p hp
    simp only [Function.mem_support] at hp
    simp [hp]
end GlobalTheory.SumRefinement
