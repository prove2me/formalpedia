-- Prove2me | solution 1 for GlobalTheory.ClassFin.gramLB_one_le_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:13.186949+00:00
-- url     : https://prove2.me/submissions/5c5536ed-26b8-475d-9f24-b444fc298379

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegral
import Theorems.Thm_GlobalTheory_ClassFin_gramLB_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℝ}
    (hR : R.PosSemidef) : 1 ≤ (R + 1).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hR.1 1
  rw [one_smul] at hEq
  have hdet : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
  rw [hEq, det_mul, det_mul, det_diagonal]
  have e : U.det * (∏ i, (hR.1.eigenvalues i + 1)) * Uᴴ.det = ∏ i, (hR.1.eigenvalues i + 1) := by
    linear_combination (∏ i, (hR.1.eigenvalues i + 1)) * hdet
  rw [e]
  calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
    _ ≤ ∏ i, (hR.1.eigenvalues i + 1) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => by linarith [hR.eigenvalues_nonneg i]
end GlobalTheory.ClassFin
