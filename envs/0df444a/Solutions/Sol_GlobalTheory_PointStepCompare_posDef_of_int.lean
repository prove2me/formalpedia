-- Prove2me | solution 1 for GlobalTheory.PointStepCompare.posDef_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:15.545412+00:00
-- url     : https://prove2.me/submissions/52333d5a-4926-42bd-87ed-3c43fb5f1af3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos
import Theorems.Thm_GlobalTheory_PointStepCompare_posSemidef_of_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PointStepCompare
open NumberField Matrix
open scoped MatrixOrder
namespace GlobalTheory.PointStepCompare
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) :
    M.det ≠ 0 ∧ (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hd : M.det ≠ 0 := fun h => by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [h0] using hp v hv
  have h1 : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    refine posSemidef_of_int (by ext i j; simp [hs i j]) fun x => ?_
    have : (fun i => (x i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (x i : ℝ)) =
        ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ) := by simp [dotProduct, mulVec]
    rw [this]
    by_cases hx : x = 0
    · simp [hx]
    · exact_mod_cast (hp x hx).le
  refine ⟨hd, h1.posDef_iff_det_ne_zero.2 ?_⟩
  rw [← Int.cast_det]
  exact_mod_cast hd
end GlobalTheory.PointStepCompare
