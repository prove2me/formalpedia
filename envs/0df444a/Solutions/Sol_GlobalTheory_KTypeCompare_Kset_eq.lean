-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.Kset_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:30.554273+00:00
-- url     : https://prove2.me/submissions/e188ca02-7e78-48be-abd0-a1018efb71b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
namespace GlobalTheory.KTypeCompare
theorem _root_.solution (ε : Fin n → Bool) : PI.UpqRep.Kset ε = HarishChandraRootData.grpK ε := by
  ext g
  simp only [PI.UpqRep.Kset, HarishChandraRootData.grpK, Set.mem_ofPred_eq, PI.UpqRep.Jm]
  refine and_congr_right fun _ => ?_
  rw [← Matrix.ext_iff]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  constructor
  · intro h a b hab
    have h' := h a b
    cases ha : ε a <;> cases hb : ε b
    · exact absurd (ha.trans hb.symm) hab
    · simp [ha, hb] at h'
      first | exact h' | linear_combination (1 / 2 : ℂ) * h' | linear_combination (-1 / 2 : ℂ) * h'
    · simp [ha, hb] at h'
      first | exact h' | linear_combination (1 / 2 : ℂ) * h' | linear_combination (-1 / 2 : ℂ) * h'
    · exact absurd (ha.trans hb.symm) hab
  · intro h a b
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab, zero_mul, mul_zero]
end GlobalTheory.KTypeCompare
