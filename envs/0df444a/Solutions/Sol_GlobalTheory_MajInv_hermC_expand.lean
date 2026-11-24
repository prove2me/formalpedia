-- Prove2me | solution 1 for GlobalTheory.MajInv.hermC_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:43.031939+00:00
-- url     : https://prove2.me/submissions/8683b1f0-ffc0-4ebc-8653-768b005f8d97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
import Theorems.Thm_GlobalTheory_MajInv_col_map_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.MajInv
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open Matrix
open scoped ComplexConjugate
variable {r : ℕ} (X : Data E r)
namespace GlobalTheory.MajInv
theorem _root_.solution (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  rw [Data.mulVec_eq_sum_col (P.map τ) u, Data.mulVec_eq_sum_col (P.map τ) w, hermC_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right, col_map_eq, col_map_eq, hermC_emb]
  ring
end GlobalTheory.MajInv
