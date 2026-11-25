-- Prove2me | solution 1 for GlobalTheory.StepData.twistChain_entry_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:23.149689+00:00
-- url     : https://prove2.me/submissions/50b97aab-6857-4ba3-83e4-ee49df090078

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_parPhi_of_mem
import Theorems.Thm_GlobalTheory_StepData_parPhi_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_parPhi_ne_zero_iff
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block
import Theorems.Thm_GlobalTheory_StepData_stdOrd_f
import Theorems.Thm_GlobalTheory_StepData_xi_eq_zero_iff
import Theorems.Thm_GlobalTheory_StepData_Chain_ofTwist_regular
import Theorems.Thm_GlobalTheory_StepData_exists_affPt
import Theorems.Thm_GlobalTheory_StepData_opE_ne_zero
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_one
import Theorems.Thm_GlobalTheory_StepData_MaxM_intM
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_intM_zero
import Theorems.Thm_GlobalTheory_StepData_maxM_zero


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
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.StepData
theorem _root_.solution [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    (ν : Measure k) [ν.IsAddHaarMeasure] (κ t : Type*) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
    (s c : ℕ) (h : 0 + 1 + c = s) :
    DoubleCoset.mk _ _ 1 ∈ (twistChain s t κ (1 : kˣ →* ℂˣ) (fun _ _ => rfl) fun _ => 1).idx ψ ν 0 c h 1 ∧
      (twistChain s t κ (1 : kˣ →* ℂˣ) (fun _ _ => rfl) fun _ => 1).entry ψ ν 0 c h 1 1 ≠ 0 := by
  set T := twistChain s t κ (1 : kˣ →* ℂˣ) (fun _ _ => rfl) fun _ => 1
  have hT : T.Regular := Chain.ofTwist_regular _ _ _ _ _
  let o := stdOrd κ t (l := s + 1) (0 + 1) (c + 1) (by omega)
  let o' := stdOrd κ t (l := s + 1) 0 (c + 1 + 1) (by omega)
  have hP : ∀ x, T.Phi 0 (c + 1) (by omega) x = parPhi 1 (x.submatrix o o') := fun x => by
    change parPhi 1 ((plainFrame o).coords (plainFrame o') x) = _
    simp [plainFrame, LatFrame.coords]
  let x : Matrix _ _ k := (fromBlocks (1 : Matrix _ _ k) 0 0 0).submatrix o.symm o'.symm
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
    · simp [x, basePt, a1, a2, Matrix.one_apply])
  have hflat : flat ψ ν (T.mu (0 + 1)) (T.Phi 0 (c + 1) (by omega)) 1 1 ≠ 0 := by
    rw [flat, om_one]
    refine fun h0 => opE_ne_zero hψ ν 1 (hT.1 0 (c + 1) (by omega)) (fun y hy => ?_) (e₀ := e) ?_
      (congrFun h0 x.toBlocks₁₁)
    · rw [hP] at hy ⊢
      obtain ⟨⟨g, hg, eg⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff 1).1 hy
      refine ⟨by rw [parPhi_of_mem 1 hg eg h21 h12 h22]; simp, fun i j => ?_⟩
      have : IntM (y.submatrix o o') := by
        rw [← fromBlocks_toBlocks (y.submatrix o o'), ← eg]
        exact intM_fromBlocks.2 ⟨intM_of_mem_KO hg, h12, h21.intM, h22⟩
      simpa using this (o.symm i) (o'.symm j)
    · rw [he, hP]
      simp only [x, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
      rw [parPhi_fromBlocks 1 (one_mem _) Units.val_one maxM_zero intM_zero intM_zero]
      exact Units.ne_zero _
  exact ⟨⟨1, rfl, hflat⟩, fun h0 => hflat ((xi_eq_zero_iff ψ ν _ _ (hT.2.2 _ _ _).1 (hT.2.2 _ _ _).2.1 _ _ _).1 h0)⟩
end GlobalTheory.StepData
