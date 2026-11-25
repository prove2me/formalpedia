-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.mem_mixed_Fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:37.335453+00:00
-- url     : https://prove2.me/submissions/afa9b153-6797-4b08-b7d9-b9c1f63ed085

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
    (S : Finset (Fin h)) (x : Fin h → O) : x ∈ (mixed ε h S).Fil ↔ ∀ i ∈ S, x i = 0 := by
  rw [Datum.Fil, LinearMap.mem_ker, funext_iff]
  simp only [mixed_bb ε hμ]
  constructor
  · intro H i hi; simpa [hi] using H i
  · intro H i; split_ifs with hi
    · exact H i hi
    · rfl
end GlobalTheory.Sandwich.Model
