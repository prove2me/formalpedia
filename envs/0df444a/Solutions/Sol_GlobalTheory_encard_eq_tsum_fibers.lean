-- Prove2me | solution 1 for GlobalTheory.encard_eq_tsum_fibers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:36.082727+00:00
-- url     : https://prove2.me/submissions/c97626c6-d135-4199-8e05-f458e1694b89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiber

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
open GlobalTheory
open MulAction
namespace GlobalTheory
theorem _root_.solution {L Q : Type} (F : Set L) (q : L → Q) :
    (F.encard : ℝ≥0∞) = ∑' o : Q, (({z | z ∈ F ∧ q z = o}).encard : ℝ≥0∞) := by
  classical
  have h1 : ∑' _ : F, (1 : ℝ≥0∞) = ∑' _ : (Σ o : Q, {z : F // q z = o}), (1 : ℝ≥0∞) :=
    ((Equiv.sigmaFiberEquiv (fun z : F => q z)).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
  rw [← ENNReal.tsum_set_one F, h1, ENNReal.tsum_sigma']
  refine tsum_congr fun o => ?_
  simp only [ENNReal.tsum_one]
  congr 1
  exact ENat.card_congr
    { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end GlobalTheory
