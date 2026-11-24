-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.HC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:23.735734+00:00
-- url     : https://prove2.me/submissions/550bc0ab-6f61-4bb5-9e90-f47ee175caa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_sec_rec

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
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution {K : Type} [CommRing K] (a : Inv r K) (i j : Fin r) :
    (hankel a * companion a.1) i j = mom (sec a) ((i : ℕ) + j + 1) := by
  by_cases hj : (j : ℕ) + 1 = r
  · rw [add_assoc, hj, sec_rec]
    simp [mul_apply, companion, hj, hankel, dotProduct]
  · rw [mul_apply, Finset.sum_eq_single ⟨(j : ℕ) + 1, by omega⟩]
    · simp [companion, hj, hankel, add_assoc]
    · intro l _ hl
      have : ¬ ((l : ℕ) = (j : ℕ) + 1) := fun h => hl (Fin.ext h)
      simp [companion, hj, this]
    · simp
end GlobalTheory.JR.HermInv
