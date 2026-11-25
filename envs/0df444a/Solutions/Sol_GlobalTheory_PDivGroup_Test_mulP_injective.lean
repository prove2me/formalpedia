-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.mulP_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:59:49.588738+00:00
-- url     : https://prove2.me/submissions/1aff597f-c5a9-4313-a35e-8732beb2d8fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Theorems.Thm_GlobalTheory_CartierDual_map_injective_of_surjective
import Theorems.Thm_GlobalTheory_CartierDual_map_map_bidual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
namespace _root_.GlobalTheory.PDivGroup.Test
theorem _root_.solution (G : _root_.GlobalTheory.PDivGroup p O) (n : ℕ) :
    Function.Injective (G.mulP n) := by
  intro x y hxy
  have hinj := _root_.GlobalTheory.CartierDual.map_injective_of_surjective (G.dual_mulP_surjective n)
  have hx := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) x
  have hy := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) y
  rw [hxy, ← hy] at hx
  exact (_root_.GlobalTheory.CartierDual.bidual O (G.A n)).injective (hinj hx)
end _root_.GlobalTheory.PDivGroup.Test
end GlobalTheory.PDivGroup.Test
