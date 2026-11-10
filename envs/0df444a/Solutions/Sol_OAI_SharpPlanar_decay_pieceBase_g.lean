-- Prove2me | solution 1 for OAI.SharpPlanar.decay_pieceBase_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:21:15.928198+00:00
-- url     : https://prove2.me/submissions/e2474a4c-bb7a-4a89-ac9d-5cca8bf9894e

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_dampingCap_pos_g
import Theorems.Thm_OAI_SharpPlanar_pi_fine_g
import Theorems.Thm_OAI_SharpPlanar_pieceBase_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis

lemma decay_pieceBase_g_oai (j : Fin 6) (n : ℕ) :
    Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*n) ≤ pieceBase j^n := by
  have he : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩) ≤ pieceBase j :=
    (Real.exp_le_exp.mpr (by nlinarith [pi_fine_g,(dampingCap_pos_g ⟨j.val+1,by omega⟩)])).trans
      (pieceBase_contains_g j)
  rw [mul_comm _ (n:ℝ),Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he n

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.decay_pieceBase_g_oai := @OAI.SharpPlanar.decay_pieceBase_g_oai
