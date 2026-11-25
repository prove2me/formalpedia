-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.mem_mixed_Tsub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:27.0078+00:00
-- url     : https://prove2.me/submissions/b395024a-434e-4aa8-a800-c42d3cadadf9

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
theorem _root_.solution (ε : PreTilt O p) (h : ℕ) (S : Finset (Fin h)) (i : Fin h) (x : Fin h → O) :
    x ∈ (mixed ε h S).Tsub ((padicToO p O).comp (Pi.evalRingHom _ i)) ↔ ∀ j ≠ i, x j = 0 := by
  simp only [Datum.Tsub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, mixed,
    toLin'_apply, funext_iff]
  constructor
  · intro H j hj
    have := H (Pi.single j 1) j
    simpa [diagonal_map (map_zero _), mulVec_diagonal, Pi.single_apply, hj.symm] using this
  · intro H a j
    by_cases hj : j = i
    · subst hj; simp [diagonal_map (map_zero _), mulVec_diagonal]
    · simp [diagonal_map (map_zero _), mulVec_diagonal, H j hj]
end GlobalTheory.Sandwich.Model
