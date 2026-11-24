-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.action_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:03.363903+00:00
-- url     : https://prove2.me/submissions/7e6e498d-39f4-47d1-a38a-09a055cb94cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_Stages_pr_fst
import Theorems.Thm_GlobalTheory_SmGL_Stages_pr_snd
import Theorems.Thm_GlobalTheory_SmGL_Stages_det_pr
import Theorems.Thm_GlobalTheory_SmGL_Stages_dl_apply
import Theorems.Thm_GlobalTheory_SmGL_Stages_dat_apply
import Theorems.Thm_GlobalTheory_SmGL_Stages_tauSnd_apply
import Theorems.Thm_GlobalTheory_SmGL_Stages_tauFst_apply
import Theorems.Thm_GlobalTheory_SmGL_absPow_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution (e₁ : ab ⊕ c ≃ n) (f₁ : a ⊕ b ≃ ab) (e₂ : a ⊕ bc ≃ n) (f₂ : b ⊕ c ≃ bc)
    (Ha : ∀ i, e₁ (.inl (f₁ (.inl i))) = e₂ (.inl i))
    (Hb : ∀ i, e₁ (.inl (f₁ (.inr i))) = e₂ (.inr (f₂ (.inl i))))
    (Hc : ∀ i, e₁ (.inr i) = e₂ (.inr (f₂ (.inr i))))
    (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (π₃ : Representation ℂ (GL c k) V₃) (q₁ : parab k (two e₁)) (q₂ : parab k (two e₂))
    (p₁ : parab k (two f₁)) (p₂ : parab k (two f₂)) (hq : (q₁ : GL n k) = q₂)
    (hp₁ : (pr e₁ q₁).1 = p₁) (hp₂ : (pr e₂ q₂).2 = p₂) (z : (V₂ ⊗[ℂ] V₃) ⊗[ℂ] V₁) :
    TensorProduct.map (dat f₁ (extTensor π₁ π₂) p₁) (tauSnd e₁ π₃ q₁)
        ((TensorProduct.assoc ℂ V₁ V₂ V₃).symm (TensorProduct.comm ℂ _ _ z)) =
      (TensorProduct.assoc ℂ V₁ V₂ V₃).symm (TensorProduct.comm ℂ _ _
        (TensorProduct.map (dat f₂ (extTensor π₂ π₃) p₂) (tauFst e₂ π₁ q₂) z)) := by
  have g₁ : (pr f₁ p₁).1 = (pr e₂ q₂).1 := by
    ext i j
    rw [pr_fst, ← hp₁, pr_fst, pr_fst, Ha, Ha, hq]
  have g₂ : (pr f₁ p₁).2 = (pr f₂ p₂).1 := by
    ext i j
    rw [pr_snd, ← hp₁, pr_fst, pr_fst, ← hp₂, pr_snd, Hb, Hb, hq]
  have g₃ : (pr e₁ q₁).2 = (pr f₂ p₂).2 := by
    ext i j
    rw [pr_snd, pr_snd, ← hp₂, pr_snd, Hc, Hc, hq]
  have hd : dl e₁ q₁ * dl f₁ p₁ = dl e₂ q₂ * dl f₂ p₂ := by
    have c₁ : (Fintype.card ab : ℂ) = Fintype.card a + Fintype.card b := by
      rw [← Fintype.card_congr f₁, Fintype.card_sum, Nat.cast_add]
    have c₂ : (Fintype.card bc : ℂ) = Fintype.card b + Fintype.card c := by
      rw [← Fintype.card_congr f₂, Fintype.card_sum, Nat.cast_add]
    rw [dl_apply, dl_apply, dl_apply, dl_apply, hp₁, hp₂, det_pr f₁ p₁, det_pr f₂ p₂, g₁, g₂, g₃, c₁, c₂]
    simp only [neg_add, add_div, absPow_add, MonoidHom.mul_apply, map_mul]
    generalize GeneralLinearGroup.det (pr e₂ q₂).1 = x
    generalize GeneralLinearGroup.det (pr f₂ p₂).1 = y
    generalize GeneralLinearGroup.det (pr f₂ p₂).2 = w
    apply Units.ext
    simp only [Units.val_mul]
    ring
  induction z with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul y x =>
    induction y with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul y z =>
      rw [TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, dat_apply, dat_apply, extTensor_tmul, extTensor_tmul, g₁, g₂,
        TensorProduct.comm_tmul, tauSnd_apply, tauFst_apply, g₃, TensorProduct.smul_tmul_smul,
        TensorProduct.smul_tmul_smul, map_smul, TensorProduct.assoc_symm_tmul, ← Units.val_mul,
        ← Units.val_mul, ← hd, mul_comm]
end GlobalTheory.SmGL.Stages
