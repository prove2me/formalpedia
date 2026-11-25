-- Prove2me | solution 1 for GlobalTheory.RankStrataProof.lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:21:23.606382+00:00
-- url     : https://prove2.me/submissions/09a6db3e-05ad-4d6a-b7e5-57c97589da22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingTopEmb
import Theorems.Thm_GlobalTheory_RankStrataProof_pAct_eq
import Theorems.Thm_GlobalTheory_RankStrataProof_isSmoothChar_omChar
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_absPow_add
import Theorems.Thm_GlobalTheory_SmGL_absPow_neg
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two
import Theorems.Thm_GlobalTheory_SmGL_det_parab
import Theorems.Thm_GlobalTheory_SmGL_mem_parabLower_two
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular
import Theorems.Thm_GlobalTheory_T_exists_GL_mul_rightColumns_eq_zero_of_rank
import Theorems.Thm_GlobalTheory_T_leftColumns_mulVec_injective_of_rank_eq_card
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_sweep_smoothly_induced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.RankStrataProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]
namespace GlobalTheory.RankStrataProof
theorem _root_.solution (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (z : ℂ) (hz : z + (Fintype.card c : ℂ) / 2 = (Fintype.card b : ℂ) / 2) :
    Nonempty (Representation.Equiv ((omegaOn a b μ {κ}).comp (MonoidHom.inl _ _))
      (ind₂Lower e (extTensor (colRep b e {κ}
        (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2 + (Fintype.card d : ℂ) / 2)))
        (detRep d (μ⁻¹ * absPow k z))))) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hcl : IsClosed {x : RankIn k a b {κ} | ∀ i j, x.1 i (e (.inr j)) = 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const
  obtain ⟨E, hE⟩ := GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced (GL a k) (RankIn k a b {κ}) (ColZero k b e {κ})
    (SB (ColZero k b e {κ}) ⊗[ℂ] ℂ) (rAct {κ}) (rAct_one _) (rAct_mul _) (continuous_rAct _)
    Subtype.val hcl.isClosedEmbedding_subtypeVal (parabLower k (two e)) (KO k a) SplitFlip.isCompact_KO
    (fun x => by
      obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k b c d a e x.1 (x.2.trans hκ)
      obtain ⟨p, hp, w, hw, h⟩ := iwasawa_blockTriangular k a (fun i => (!blk (two e) i).toNat) g⁻¹
      have hp' : p ∈ parabLower k (two e) := (mem_parabLower_two k).2 fun i j => hp (by
        rw [← two_false e, ← two_true e]; simp only [blk_apply]; simp)
      refine ⟨pAct e _ ⟨rAct _ x g, by rwa [rAct_val]⟩ ⟨p, hp'⟩, w, hw, ?_⟩
      show x = rAct _ (rAct _ (rAct _ x g) p) w
      rw [← rAct_mul, ← rAct_mul, ← h, mul_inv_cancel, rAct_one])
    (pAct e _) (fun _ _ => rfl)
    (fun y y' g h => (mem_parabLower_two k).2 fun i j => by
      refine congrFun (GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k b c d a e y.1.1 (y.1.2.trans hκ) y.2
        (fun m => g.val (e (.inl m)) (e (.inr j))) (funext fun l => ?_)) i
      have := y'.2 l j
      rw [← h, rAct_val, mul_apply_of_cols e y.2] at this
      exact this)
    ((omChar a b μ).comp (MonoidHom.inl _ _))
    ((isSmoothChar_omChar hμ).comp _ (continuous_id.prodMk continuous_const))
    ((twist (MonoidHom.comp (extTensor (colRep b e {κ}
        (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2 + (Fintype.card d : ℂ) / 2)))
        (detRep d (μ⁻¹ * absPow k z))) (leviTwo k c d).symm.toMonoidHom) (deltaHalf k (Two c d))⁻¹).comp
        (leviProjLower k (two e)))
    (TensorProduct.rid ℂ _)
    (fun p w y => by
      obtain ⟨φ, rfl⟩ := (TensorProduct.rid ℂ _).symm.surjective w
      set m := leviProjLower k (two e) p with hm
      have hd : GeneralLinearGroup.det (p : GL a k) =
          GeneralLinearGroup.det (m false) * GeneralLinearGroup.det (m true) := by
        have := det_parab k (opp (two e)) p
        rw [this]
        exact (Fintype.prod_bool _).trans (mul_comm _ _)
      have hδ := deltaHalf_two (k := k) (m false, m true)
      rw [show leviTwo k c d (m false, m true) = m from (leviTwo k c d).right_inv m] at hδ
      rw [LinearEquiv.apply_symm_apply, TensorProduct.rid_symm_apply]
      show (TensorProduct.rid ℂ _ ((((deltaHalf k (Two c d) m)⁻¹ : ℂˣ) : ℂ) •
        extTensor _ _ (m false, m true) (φ ⊗ₜ 1))).1 y = _
      rw [extTensor_tmul, map_smul, TensorProduct.rid_tmul]
      show (((deltaHalf k (Two c d) m)⁻¹ : ℂˣ) : ℂ) * (detRep d _ (m true) 1 *
        ((detChar c _ (m false) : ℂ) * φ.1 (pAct e _ y (fstBlock e (m false))))) = _
      rw [pAct_eq, ← mul_assoc, ← mul_assoc, detRep, ofChar_apply, mul_one, ← Units.val_mul, ← Units.val_mul]
      congr 2
      rw [hδ]
      simp only [omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply, MonoidHom.inl_apply,
        MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, mul_one, hd, map_mul, neg_div, absPow_neg,
        MonoidHom.inv_apply]
      have h1 := DFunLike.congr_fun (absPow_add k z ((Fintype.card c : ℂ) / 2))
        (GeneralLinearGroup.det (m true))
      rw [hz] at h1
      rw [h1, absPow_add]
      simp only [MonoidHom.mul_apply, mul_inv, inv_inv]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp)
  refine ⟨.mk E fun g => LinearMap.ext fun Φ => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
  refine (TensorProduct.rid ℂ _).injective (Subtype.ext (funext fun y => ?_))
  refine (hE _ x y).trans (Eq.trans ?_ (hE Φ (x * g) y).symm)
  rw [map_mul, rAct_mul, Units.val_mul, mul_assoc]
  rfl
end GlobalTheory.RankStrataProof
