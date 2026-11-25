-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.mem_mixed_Lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:27:08.916531+00:00
-- url     : https://prove2.me/submissions/ec0682be-7f6a-4d95-b5d2-a564e362fd26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
import Theorems.Thm_GlobalTheory_Sandwich_Model_mixed_bb

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
theorem _root_.solution (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ)
    (S : Finset (Fin h)) (x : Fin h → O) : x ∈ (mixed ε h S).Lie ↔ ∀ i ∉ S, x i = 0 := by
  rw [Datum.Lie, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩ i hi; simp [mixed_bb ε hμ, hi]
  · intro H; refine ⟨x, funext fun i => ?_⟩
    rw [mixed_bb ε hμ]; split_ifs with hi
    · rfl
    · exact (H i hi).symm
end GlobalTheory.Sandwich.Model
