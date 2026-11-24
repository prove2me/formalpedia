-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosGr.dd_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:27.921929+00:00
-- url     : https://prove2.me/submissions/ecafb241-0211-4be2-9c13-b45ffc403c3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]
namespace GlobalTheory.KeyKa.KosGr
theorem _root_.solution (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j) (r : ℕ) (c c' : Finset (Fin g) → ∀ j, V j)
    (I : Finset (Fin g)) (j : ℕ)
    (h : ∀ i : Fin g, i.val < r → i ∉ I → c (insert i I) (j + 1) = c' (insert i I) (j + 1)) :
    dd x r c I j = dd x r c' I j := by
  unfold dd
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h i hi.1 hi.2]
  · rfl
end GlobalTheory.KeyKa.KosGr
