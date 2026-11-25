-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.fibStr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:22.275378+00:00
-- url     : https://prove2.me/submissions/38615f76-0ddf-413c-a9e5-82218c45a4fa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_mul_topR
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_topR_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_isClosedEmbedding_topEmbR
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_lAct_topEmbR
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_eq_zero_of_vecMul
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_exists_topEmbR
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_fibChar_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_fibRep_apply
import Theorems.Thm_GlobalTheory_RankStrataProof_continuous_lAct
import Theorems.Thm_GlobalTheory_RankStrataProof_isSmoothChar_omChar
import Theorems.Thm_GlobalTheory_RankStrataProof_lAct_mul
import Theorems.Thm_GlobalTheory_RankStrataProof_lAct_one
import Theorems.Thm_GlobalTheory_RankStrataProof_lAct_val
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_absPow_add
import Theorems.Thm_GlobalTheory_SmGL_absPow_neg
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two
import Theorems.Thm_GlobalTheory_SmGL_det_parab
import Theorems.Thm_GlobalTheory_SmGL_mem_parab_two
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
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
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]
namespace GlobalTheory.CompanionTheory.ThetaGLLen
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b c d : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (κ : ℕ), κ = Fintype.card c → ∀ μ : kˣ →* ℂˣ,
    IsSmoothChar μ → Nonempty ((omegaOn a b μ {κ}).Equiv (indSnd e (fibRep a c d μ κ))) := by
  intro k _ _ _ _ a b c d _ _ _ _ _ _ _ _ e κ hκ μ hμ
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨E, hE⟩ := GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced (GL b k) (RankIn k a b {κ}) (RankIn k a c {κ})
    (SB (RankIn k a c {κ})) (lAct {κ}) (lAct_one _) (lAct_mul _) (continuous_lAct _)
    (topEmbR e) (isClosedEmbedding_topEmbR e) (parab k (two e)) (KO k b) SplitFlip.isCompact_KO
    (exists_topEmbR e hκ)
    (fun y p => lAct _ y (show GL c k from leviProj k (two e) p false)) (lAct_topEmbR e)
    (fun y y' g h => by
      refine inv_mem_iff.1 ((mem_parab_two k).2 fun j i => ?_)
      have h0 : (fun m => (g⁻¹).val (e (.inr j)) (e (.inl m))) ᵥ* y.1 = 0 := by
        funext l
        have := congrArg (fun x : RankIn k a b {κ} => x.1 (e (.inr j)) l) h
        simp only [lAct_val] at this
        exact (mul_topR e _ _ _ l).symm.trans (this.trans (topR_inr e _ j l))
      exact congrFun (eq_zero_of_vecMul e hκ y _ h0) i)
    ((omChar a b μ).comp (MonoidHom.inr _ _))
    ((isSmoothChar_omChar hμ).comp _ (continuous_const.prodMk continuous_id))
    ((twist (MonoidHom.comp ((fibRep a c d μ κ).comp (MonoidHom.inr _ _)) (leviTwo k c d).symm.toMonoidHom)
      (deltaHalf k (Two c d))).comp (leviProj k (two e)))
    (LinearEquiv.refl ℂ _)
    (fun p w y => by
      set m := leviProj k (two e) p with hm
      have hd : GeneralLinearGroup.det (p : GL b k) =
          GeneralLinearGroup.det (m false) * GeneralLinearGroup.det (m true) :=
        (det_parab k (two e) p).trans ((Fintype.prod_bool _).trans (mul_comm _ _))
      have hδ := deltaHalf_two (k := k) (m false, m true)
      rw [show leviTwo k c d (m false, m true) = m from (leviTwo k c d).right_inv m] at hδ
      show (deltaHalf k (Two c d) m : ℂ) * (fibRep a c d μ κ (1, m false, m true) w).1 y = _
      rw [fibRep_apply, ← mul_assoc, ← Units.val_mul]
      refine congrArg₂ _ (congrArg _ ?_) rfl
      rw [hδ]
      simp only [fibChar, omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply,
        MonoidHom.inr_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, one_mul, hd, map_mul,
        neg_div, absPow_neg, MonoidHom.inv_apply, absPow_add, mul_inv, inv_inv, inv_one]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp)
  have hE' : ∀ Φ g y, ((E Φ).1.1 g).1 y =
      (omChar a b μ (1, g) : ℂ) * Φ.1 (lAct _ (topEmbR e y) g) := hE
  refine ⟨.mk E fun g => LinearMap.ext fun Φ => Subtype.ext (Subtype.ext (funext fun x =>
    Subtype.ext (funext fun y => ?_)))⟩
  obtain ⟨γ, h⟩ := g
  refine (hE' _ x y).trans (Eq.trans ?_ (fibRep_apply a c d μ κ γ 1 1 ((E Φ).1.1 (x * h)) y).symm)
  rw [hE', omegaOn_apply, fibChar_fst e, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul,
    ← map_mul, ← map_mul]
  refine congrArg₂ _ (congrArg _ (congrArg _ (by simp))) (congrArg _ (Subtype.ext ?_))
  simp only [lAct_val, act, topEmbR, Units.val_mul, topR_mul, _root_.mul_inv_rev, Matrix.mul_assoc,
    Units.val_one, Matrix.one_mul, inv_one, Matrix.mul_one]
end GlobalTheory.CompanionTheory.ThetaGLLen
