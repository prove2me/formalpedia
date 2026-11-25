-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.mixed_al
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:07:47.887389+00:00
-- url     : https://prove2.me/submissions/7e6f5d5e-baa5-4b8c-8b63-d82213867e25

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
    (x : Fin h → O) (i : Fin h) : (mixed ε h S).al x i = if i ∈ S then 0 else x i := by
  simp only [Datum.al, mixed, diagonal_map (map_zero _), toLin'_apply, mulVec_diagonal]
  split_ifs <;> simp [hμ]
end GlobalTheory.Sandwich.Model
