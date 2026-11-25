-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.torus_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:33.961087+00:00
-- url     : https://prove2.me/submissions/f51d8a1f-ce9f-4655-be64-07c7b59c86ab

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
theorem _root_.solution (ε : Fin n → Bool) (θ : Fin n → ℝ) : HarishChandraRootData.torus θ ∈ HarishChandraRootData.grpK ε := by
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, HarishChandraRootData.torus, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal, Complex.conj_I]
  · have hne : a ≠ b := fun h => hab (h ▸ rfl)
    simp [HarishChandraRootData.torus, Matrix.diagonal_apply_ne _ hne]
end GlobalTheory.KTypeCompare
