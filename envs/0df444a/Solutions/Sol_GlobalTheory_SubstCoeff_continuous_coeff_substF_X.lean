-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.continuous_coeff_substF_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:03.402372+00:00
-- url     : https://prove2.me/submissions/49b1e7e5-c831-4ec9-b9c1-8b4e253e5151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Theorems.Thm_GlobalTheory_CompactHowe_substF_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.SubstCoeff
variable {σ : Type}
variable {ι : Type} {N n : ℕ}
namespace GlobalTheory.SubstCoeff
theorem _root_.solution (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    Continuous fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) =>
      coeff m (GlobalTheory.CompactHowe.substF p.1 p.2 (X q)) := by
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  refine Continuous.mul (Continuous.mul ?_ ?_) continuous_const
  · exact ((continuous_apply q.1).comp continuous_fst).matrix_elem a q.2.1
  · exact ((continuous_apply q.1).comp continuous_snd).matrix_elem b q.2.2
end GlobalTheory.SubstCoeff
