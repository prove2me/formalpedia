-- Prove2me | solution 1 for GlobalTheory.FlagHook.Degree.signed_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:10.37859+00:00
-- url     : https://prove2.me/submissions/c2c81c36-93be-4621-8ef4-5144c1b6f1a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
noncomputable section
open GlobalTheory GlobalTheory.FlagHook GlobalTheory.FlagHook.Degree
namespace GlobalTheory.FlagHook.Degree
theorem _root_.solution {N : ℕ} (v : Fin N → ℝ) :
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, v i ^ (N - 1 - ((σ i : Fin N) : ℕ)) =
      ∏ i, ∏ j ∈ Ioi i, (v i - v j) := by
  have h := Matrix.det_projVandermonde (fun _ : Fin N => (1 : ℝ)) v
  rw [← Matrix.det_transpose, Matrix.det_apply'] at h
  simp only [Matrix.transpose_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev] at h
  rw [← h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  omega
end GlobalTheory.FlagHook.Degree
