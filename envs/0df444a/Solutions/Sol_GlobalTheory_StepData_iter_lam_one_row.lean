-- Prove2me | solution 1 for GlobalTheory.StepData.iter_lam_one_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:03.280622+00:00
-- url     : https://prove2.me/submissions/d2bcaba6-a576-4fa3-9cad-b7c5b0a7bb43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedDepthOneLevelCharOfOneRowFirstBlock
import Theorems.Thm_GlobalTheory_StepData_det_eq_one_of_one_row
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_lam


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.StepData
namespace GlobalTheory.StepData
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (r₀ : r) : ∀ (h : (P.iter t μ hμ j).J),
    (∀ a b, a ≠ Sum.inl r₀ → (h : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b) →
    (h : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 →
    ∃ g : P.J, (g : GL r k).val = (h : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧
      (P.iter t μ hμ j).lam h = P.lam g := by
  induction j with
  | zero =>
    intro h _ _
    exact ⟨⟨(reGL (ixZero r t)).symm h, h.2⟩, rfl, rfl⟩
  | succ j ih =>
    intro h h1 h2
    set Q := P.iter t μ hμ j with hQ
    let h' : Q.stepJ t := ⟨(reGL (ixSucc r t j)).symm h, h.2⟩
    have eh' : (h' : GL (Ix r t j ⊕ t) k).val = (h : GL (Ix r t (j + 1)) k).val.submatrix (ixSucc r t j) (ixSucc r t j) := rfl
    let c := Q.corner h'
    have ec : ∀ a b, (c : GL (Ix r t j) k).val a b =
        (h : GL (Ix r t (j + 1)) k).val (ixSucc r t j (.inl a)) (ixSucc r t j (.inl b)) := by
      intro a b; rw [Q.corner_val]; rfl
    have hne : ∀ a, a ≠ Sum.inl r₀ → ixSucc r t j (.inl a) ≠ Sum.inl r₀ := by
      intro a ha e; apply ha
      have : (Sum.inl a : Ix r t j ⊕ t) = Sum.inl (Sum.inl r₀) :=
        (ixSucc r t j).injective (e.trans rfl)
      exact Sum.inl_injective this
    have c1 : ∀ a b, a ≠ Sum.inl r₀ → (c : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b := by
      intro a b ha
      rw [ec, h1 _ _ (hne a ha), Matrix.one_apply, Matrix.one_apply]
      simp [(ixSucc r t j).injective.eq_iff]
    have c2 : (c : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 := by rw [ec]; exact h2
    obtain ⟨g, hg, hl⟩ := ih c c1 c2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]; ext x y; exact ec _ _
    · have d1 : Matrix.GeneralLinearGroup.det (c : GL (Ix r t j) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]; exact det_eq_one_of_one_row _ _ c1 c2)
      have d2 : Matrix.GeneralLinearGroup.det (h' : GL (Ix r t j ⊕ t) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, eh', det_submatrix_equiv_self]
        exact det_eq_one_of_one_row _ _ h1 h2)
      have e0 : (P.iter t μ hμ (j + 1)).lam h = (Q.step t (μ (j + 1)) (hμ _)).lam h' := rfl
      rw [e0, Q.step_lam _ _ h' c (Q.corner_val h'), ← hl, d1, d2]
      simp
end GlobalTheory.StepData
