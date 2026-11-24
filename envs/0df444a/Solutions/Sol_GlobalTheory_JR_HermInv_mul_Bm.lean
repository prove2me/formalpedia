-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mul_Bm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:48.436441+00:00
-- url     : https://prove2.me/submissions/38348a66-9830-464d-8a03-353cbd100484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ} {K : Type} [CommRing K]
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (Y : Gl r K) (q : Fin r → K) (hq : Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ q)) :
    Y.1 * Bm Y = Bm Y * companion q := by
  ext i j
  have hL : (Y.1 * Bm Y) i j = (Y.1 ^ ((j : ℕ) + 1) *ᵥ Y.2.1) i := by
    rw [pow_succ', ← mulVec_mulVec]
    simp [mul_apply, Bm, mulVec, dotProduct]
  rw [hL]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [hj, hq]
    simp [mul_apply, companion, hj, mulVec, dotProduct]
  · rw [mul_apply, Finset.sum_eq_single ⟨(j : ℕ) + 1, by omega⟩]
    · simp [companion, hj, Bm]
    · intro l _ hl
      have : ¬ ((l : ℕ) = (j : ℕ) + 1) := fun h => hl (Fin.ext h)
      simp [companion, hj, this]
    · simp
end GlobalTheory.JR.HermInv
