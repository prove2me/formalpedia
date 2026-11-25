-- Prove2me | solution 1 for GlobalTheory.bilinPart_eigen_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:06.646627+00:00
-- url     : https://prove2.me/submissions/2296c65a-95c3-4e09-afda-96ff62883fde

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_BilinPartEigenMemRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_M_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gaugeBilinearTerm_eq_neg_double_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (a : O) (u u' : Fin d → R) (α α' : R), (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k α • (fun i => algebraMap R k (u i)) → (dAct k B (star a)).mulVec (fun i => algebraMap R k (u' i)) = algebraMap R k α' • (fun i => algebraMap R k (u' i)) → IsUnit (α - α') → dotProduct (fun i => algebraMap R k (u i)) ((bilinPart k h).mulVec (fun i => algebraMap R k (u' i))) ∈ (algebraMap R k).range := by
  intro R _ d O _ _ k _ _ _ B h hc a u u' α α' hu hu' hα
  choose M hM using fun i j => WickVanishing.M_int B h hc a i j
  set v : Fin d → k := fun i => algebraMap R k (u i) with hv
  set v' : Fin d → k := fun i => algebraMap R k (u' i) with hv'
  have hS : sg1 k h = -(bilinPart k h).transpose := by
    ext i j
    simp only [WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, Matrix.neg_apply, Matrix.transpose_apply, bilinPart]
  have e1 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      -(algebraMap R k (α - α') * dotProduct v ((bilinPart k h).mulVec v')) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, dotProduct_sub,
      Matrix.dotProduct_mulVec v' (dAct k B (star a)).transpose, Matrix.vecMul_transpose, hu', Matrix.mulVec_smul,
      dotProduct_smul, smul_dotProduct, hS, Matrix.neg_mulVec, dotProduct_neg,
      Matrix.dotProduct_mulVec v', Matrix.vecMul_transpose, dotProduct_comm _ v, map_sub]
    simp only [smul_eq_mul]
    ring
  have e2 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      algebraMap R k (∑ i, u' i * ∑ j, M i j * u j) := by
    simp only [map_sum, map_mul, hM, dotProduct, Matrix.mulVec, hv, hv']
  obtain ⟨w, hw⟩ := hα.exists_left_inv
  refine ⟨-(w * ∑ i, u' i * ∑ j, M i j * u j), ?_⟩
  rw [map_neg, map_mul, ← e2, e1, mul_neg, neg_neg, ← mul_assoc, ← map_mul, hw, map_one, one_mul]
end GlobalTheory
