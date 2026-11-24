-- Prove2me | solution 1 for GlobalTheory.PerBor.moveMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:08:36.885026+00:00
-- url     : https://prove2.me/submissions/d585e849-dafb-4ce7-994b-31e8cbf24f86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TriangularFrameMovesPeriodBlockTriangular
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_PerMove_bor_inv_tri
import Theorems.Thm_GlobalTheory_PerMove_bor_tri
import Theorems.Thm_GlobalTheory_PerMove_hermC_col_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.PerBor
variable {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r g : ℕ} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r)
    {b : Frame Ψ r}
namespace GlobalTheory.PerBor
theorem _root_.solution (hb : b ∈ Bor Ψ r) (Gm : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (v : Fin r → E)
    (P P' : Fin g → ℂ)
    (hP : ∀ k, P k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2)
    (hP' : ∀ k, P' k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat (rmul x b) (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat (rmul x b) (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2) :
    P' = moveMat q idx b *ᵥ P := by
  funext k
  have hm : FD.mat (FD.rmul x b) (idx k).1 = FD.mat x (idx k).1 * FD.mat b (idx k).1 := rfl
  rw [hP', hm]
  simp only [moveMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (idx k).1]
  · simp only [Equiv.apply_symm_apply, if_true, hP]
    split_ifs with hk
    · rw [PerMove.hermC_col_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · rfl
      · rw [PerMove.bor_tri hb (idx k).1 (show (idx k).2 < c by rw [Fin.lt_def]; omega),
          zero_mul, zero_mul]
    · change ((FD.mat x (idx k).1 * FD.mat b (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v)
        (idx k).2 = _
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · rw [PerMove.bor_inv_tri hb (idx k).1 (show c < (idx k).2 by rw [Fin.lt_def]; omega),
          zero_mul, zero_mul]
      · rfl
  · intro τ _ hτ
    simp [hτ]
  · simp
end GlobalTheory.PerBor
