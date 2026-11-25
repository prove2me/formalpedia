-- Prove2me | solution 1 for GlobalTheory.StepData.Model.typeChain_entry_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:44.011805+00:00
-- url     : https://prove2.me/submissions/8fc66e9b-fa42-4e53-9c40-347b652118b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_P2M_GlobalTheory_StepData_Model_opE_ne_zero__77ad6a831e75
import Theorems.Thm_GlobalTheory_StepData_Model_wt_ne_zero
import Theorems.Thm_GlobalTheory_StepData_Model_coords_typeFrame
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_one
import Theorems.Thm_GlobalTheory_StepData_Chain_ofType_regular
import Theorems.Thm_GlobalTheory_StepData_det_reGL
import Theorems.Thm_GlobalTheory_StepData_exists_affPt
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block
import Theorems.Thm_GlobalTheory_StepData_stdOrd_f
import Theorems.Thm_GlobalTheory_StepData_xi_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData.Model
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (s c : ℕ)
    (h : 0 + 1 + c = s) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : P.J, (P.rho (μ 1) g : ℂ) =
      ψ (∑ i : Fin s, (g : GL (κ ⊕ Fin (s + 1)) k).val (.inr i.castSucc) (.inr i.succ) / ϖ)) :
    DoubleCoset.mk _ _ 1 ∈ (typeChain t ϖ P μ hμ).idx ψ ν 0 c h 1 ∧
      (typeChain t ϖ P μ hμ).entry ψ ν 0 c h 1 1 ≠ 0 := by
  obtain rfl : s = c + 1 := by omega
  set T := typeChain t ϖ P μ hμ
  have hT : T.Regular := Chain.ofType_regular _ _ _ _ _
  let o := stdOrd κ t (l := c + 1 + 1) (0 + 1) (c + 1) (by omega)
  let o' := stdOrd κ t (l := c + 1 + 1) 0 (c + 1 + 1) (by omega)
  let Q := P.reindex (ixZero _ t)
  have hQ : ∀ x, T.Phi 0 (c + 1) (by omega) x = Q.Phi t (μ 1)
      (((typeFrame ϖ o).coords (typeFrame ϖ o') x).submatrix (ixSucc _ t 0) id) := fun x => rfl
  have b1 : ∀ i : Fin (c + 1), o (.inl (.inr i.castSucc)) = .inr i := fun i => standardOrderExtendedBasis_apply_low_block κ t _ _ _ i
  have b2 : ∀ i : Fin (c + 1 + 1), o' (.inl (.inr i)) = .inr i := fun i => standardOrderExtendedBasis_apply_low_block κ t _ _ _ i
  let x : Matrix _ _ k := Matrix.of fun r q =>
    wt ϖ r * (fromBlocks (1 : Matrix _ _ k) 0 0 0).submatrix o.symm o'.symm r q * (wt ϖ q)⁻¹
  have a1 : ∀ i, o.symm (.inr i) = .inl (.inr ⟨i.val, by omega⟩) := fun i =>
    o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block κ t _ _ _ i).symm
  have a2 : ∀ i, o'.symm (.inr i) = .inl (.inr ⟨i.val, by omega⟩) := fun i =>
    o'.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block κ t _ _ _ i).symm
  have a3 : ∀ i, o.symm (.inl (.inl (.inr i))) = .inl (.inr ⟨c + 1 + i.val, by omega⟩) := fun i =>
    o.symm_apply_eq.2 (stdOrd_f κ t _ _ _ i).symm
  have a4 : ∀ i, o.symm (.inl (.inl (.inl i))) = .inl (.inl i) := fun i => o.symm_apply_eq.2 rfl
  have a5 : ∀ i, o'.symm (.inl (.inl (.inl i))) = .inl (.inl i) := fun i => o'.symm_apply_eq.2 rfl
  have a6 : ∀ i, o.symm (.inl (.inr i)) = .inr i := fun i => o.symm_apply_eq.2 rfl
  obtain ⟨e, he⟩ := exists_affPt (p := 1) (x := x) (by
    rintro (r | r) (i | i) hf
    · rfl
    · have hi : i.val = 0 := by simp only [Free] at hf; omega
      rcases r with (r | r) | r
      · simp [x, basePt, a2, a4]
      · simp [x, basePt, a2, a3, hi]
      · simp [x, basePt, a2, a6]
    · rcases i with (i | i) | i
      · simp [x, basePt, a1, a5]
      · exact i.elim0
      · exact i.1.elim0
    · by_cases hri : r.val = i.val
      · simp [x, basePt, a1, a2, wt, hri]
      · simp [x, basePt, a1, a2, Matrix.one_apply, wt, hri, Fin.ext_iff])
  have hflat : flat ψ ν (T.mu (0 + 1)) (T.Phi 0 (c + 1) (by omega)) 1 1 ≠ 0 := by
    rw [flat, om_one]
    refine fun h0 => opE_ne_zero' ψ ν 1 (hT.1 0 (c + 1) (by omega)) (fun y hy => ?_) (e₀ := e) ?_
      (congrFun h0 x.toBlocks₁₁)
    · rw [hQ] at hy ⊢
      obtain ⟨⟨g, hg, eg⟩, h2⟩ := (Q.Phi_ne_zero_iff _).1 hy
      rw [Q.Phi_of_mem _ ⟨g, hg⟩ eg h2]
      have := hP ⟨(reGL (ixZero _ t)).symm g, hg⟩
      rw [TypeDatum.rho_apply, Units.val_mul, ← det_reGL (ixZero _ t), MulEquiv.apply_symm_apply] at this
      refine this.trans (congrArg _ (congrArg _ (Finset.sum_congr rfl fun i _ => ?_)))
      change g.val (.inl (.inr i.castSucc)) (.inl (.inr i.succ)) / _ = _
      rw [eg]
      change (typeFrame ϖ o).coords (typeFrame ϖ o') y (.inl (.inr i.castSucc)) (.inl (.inr i.succ)) / _ = _
      rw [coords_typeFrame, b1, b2]
      simp only [wt, Sum.elim_inr, Fin.val_succ]
      field_simp
      ring
    · rw [he, hQ]
      have ex : (typeFrame ϖ o).coords (typeFrame ϖ o') x = fromBlocks 1 0 0 0 := by
        ext i j
        rw [coords_typeFrame]
        have := wt_ne_zero ϖ (o i)
        have := wt_ne_zero ϖ (o' j)
        simp only [x, of_apply, submatrix_apply, Equiv.symm_apply_apply]
        field_simp
      rw [ex, Q.Phi_ne_zero_iff]
      refine ⟨⟨1, one_mem _, ?_⟩, fun i j => ?_⟩
      · ext (i | i) (j | j)
        · simp [ixSucc, toRows₁, Matrix.one_apply]
        · exact j.1.elim0
        · exact i.1.elim0
        · exact i.1.elim0
      · rcases j with j | j <;> simp [ixSucc, toRows₂]
  exact ⟨⟨1, rfl, hflat⟩, fun h0 => hflat ((xi_eq_zero_iff ψ ν _ _ (hT.2.2 _ _ _).1 (hT.2.2 _ _ _).2.1 _ _ _).1 h0)⟩
end GlobalTheory.StepData.Model
