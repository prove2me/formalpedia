-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.pow_r_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:03.177737+00:00
-- url     : https://prove2.me/submissions/8dd3d832-712b-4cae-9050-785f5702c4c0

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
theorem _root_.solution [Nontrivial K] (Y : Gl r K) :
    Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ fun i : Fin r => Y.1.charpoly.coeff i) := by
  have h0 := Matrix.aeval_self_charpoly Y.1
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Finset.sum_range_succ,
    Finset.sum_range] at h0
  have hc : Y.1.charpoly.coeff r = 1 := by
    have := (Matrix.charpoly_monic Y.1).coeff_natDegree
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [hc, one_smul, add_comm] at h0
  have hA : Y.1 ^ r = -∑ i : Fin r, Y.1.charpoly.coeff i • Y.1 ^ (i : ℕ) := eq_neg_iff_add_eq_zero.mpr h0
  rw [hA, Matrix.neg_mulVec]
  congr 1
  ext j
  simp only [mulVec, dotProduct, Bm, of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
end GlobalTheory.JR.HermInv
