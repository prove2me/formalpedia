-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.mixed_bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:08:02.836072+00:00
-- url     : https://prove2.me/submissions/71afc895-4e52-490a-85e7-a00590760d61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
namespace GlobalTheory.Sandwich.Model
theorem _root_.solution (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ) (S : Finset (Fin h))
    (x : Fin h → O) (i : Fin h) : (mixed ε h S).bb x i = if i ∈ S then x i else 0 := by
  simp only [Datum.bb, mixed, diagonal_map (map_zero _), toLin'_apply, mulVec_diagonal]
  split_ifs <;> simp [hμ]
end GlobalTheory.Sandwich.Model
