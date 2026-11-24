-- Prove2me | solution 1 for GlobalTheory.TriangularIsometryBoundedPowers.exists_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:05.634659+00:00
-- url     : https://prove2.me/submissions/c9365ad5-6e8f-48a0-81a3-1ca289227437

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
import Theorems.Thm_GlobalTheory_TriangularIsometryBoundedPowers_det_block_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TriangularIsometryBoundedPowers
open Matrix
namespace GlobalTheory.TriangularIsometryBoundedPowers
theorem _root_.solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) (j : Fin n) :
    ∃ y : Fin n → ℂ, y j = 1 ∧ (∀ c, j < c → y c = 0) ∧
      ∀ a, a < j → ∑ c, B a c * y c = 0 := by
  classical
  set S := B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n) with hS
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (det_block_ne B hB j)
  obtain ⟨w, hw⟩ : ∃ w : {c : Fin n // c < j} → ℂ, S *ᵥ w = fun p => -B p.1 j :=
    ⟨S⁻¹ *ᵥ fun p => -B p.1 j, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩
  refine ⟨fun c => if h : c < j then w ⟨c, h⟩ else if c = j then 1 else 0, by simp, ?_, ?_⟩
  · intro c hc
    simp [not_lt.mpr hc.le, hc.ne']
  · intro a ha
    rw [← Fintype.sum_subtype_add_sum_subtype (fun c => c < j)]
    have h1 : ∑ c : {c : Fin n // c < j}, B a c.1 *
        (if h : c.1 < j then w ⟨c.1, h⟩ else if c.1 = j then 1 else 0) = -B a j := by
      have := congrFun hw ⟨a, ha⟩
      simp only [Matrix.mulVec, dotProduct, hS, Matrix.submatrix_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dif_pos c.2]
    have h2 : ∑ c : {c : Fin n // ¬ c < j}, B a c.1 *
        (if h : c.1 < j then w ⟨c.1, h⟩ else if c.1 = j then 1 else 0) = B a j := by
      rw [Finset.sum_eq_single (⟨j, lt_irrefl j⟩ : {c : Fin n // ¬ c < j})]
      · simp
      · intro c _ hc
        have : c.1 ≠ j := fun h => hc (Subtype.ext h)
        rw [dif_neg c.2, if_neg this, mul_zero]
      · simp
    rw [h1, h2]
    ring
end GlobalTheory.TriangularIsometryBoundedPowers
