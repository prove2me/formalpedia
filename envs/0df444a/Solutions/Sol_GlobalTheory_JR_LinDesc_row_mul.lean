-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.row_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:31.001014+00:00
-- url     : https://prove2.me/submissions/9db1bea9-b120-47b7-8a77-3990e44025c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Theorems.Thm_GlobalTheory_JR_LinDesc_bas_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution (hG : A.IsGen τ p) (s c : A.K) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* Algebra.leftMulMatrix (bas A hG) s =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Algebra.leftMulMatrix_eq_repr_mul]
  have hx := (bas A hG).sum_repr (s * bas A hG j)
  calc ∑ i : Fin r, Algebra.trace F A.K (τ ^ (i : ℕ) * c) * (bas A hG).repr (s * bas A hG j) i
      = Algebra.trace F A.K (∑ i : Fin r, ((bas A hG).repr (s * bas A hG j) i • bas A hG i) * c) := by
        rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm, bas_apply A hG i]
    _ = Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
        rw [← Finset.sum_mul, hx, bas_apply]; ring_nf
end GlobalTheory.JR.LinDesc
