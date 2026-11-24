-- Prove2me | solution 1 for GlobalTheory.EtIsom.mat_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:17:30.229488+00:00
-- url     : https://prove2.me/submissions/e77db94e-a04c-4c1c-b804-d8188437429c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_pow_rec
import Theorems.Thm_GlobalTheory_EtIsom_bL_apply
import Theorems.Thm_GlobalTheory_EtIsom_cayley
import Theorems.Thm_GlobalTheory_EtIsom_mat_pow_mulVec

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
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.EtIsom
theorem _root_.solution (hG : A.IsGen τ p) {j : A.L ≃ₗ[E] (Fin r → E)} (i : Fin r) :
    (mat A (τ := τ) j).charpoly.coeff i = algebraMap F E (p i) := by
  set M := mat A (τ := τ) j with hM
  have h1 : j (algebraMap A.K A.L (τ ^ r)) + ∑ k : Fin r, M.charpoly.coeff k • j (bL A hG k) = 0 := by
    have := congrArg (fun N => N *ᵥ j 1) (cayley M)
    simp only [Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.zero_mulVec, hM,
      mat_pow_mulVec, mul_one] at this
    simpa only [bL_apply] using this
  have h2 : algebraMap A.K A.L (τ ^ r) = -∑ k : Fin r, algebraMap F E (p k) • bL A hG k := by
    have := congrArg (algebraMap A.K A.L) (pow_rec A hG 0)
    simp only [zero_add, map_neg, map_sum, map_mul] at this
    rw [this]; congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [bL_apply, Algebra.smul_def, ← IsScalarTower.algebraMap_apply F A.K A.L,
      ← IsScalarTower.algebraMap_apply F E A.L]
  rw [h2, map_neg, map_sum] at h1
  have h3 : j (∑ k : Fin r, (M.charpoly.coeff k - algebraMap F E (p k)) • bL A hG k) = 0 := by
    rw [← h1, Finset.sum_congr rfl (fun k _ => sub_smul _ _ _), Finset.sum_sub_distrib, map_sub, map_sum,
      map_sum]
    simp only [map_smul]
    abel
  rw [LinearEquiv.map_eq_zero_iff] at h3
  have h4 := Fintype.linearIndependent_iff.mp (bL A hG).linearIndependent _ h3 i
  exact sub_eq_zero.mp h4
end GlobalTheory.EtIsom
