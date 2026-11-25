-- Prove2me | solution 1 for GlobalTheory.Couple.psi_eq_sum_coupIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:22.071094+00:00
-- url     : https://prove2.me/submissions/73b7e7c9-bd36-438b-b325-946edbf681ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PsiEqSumCoupIdx
import Theorems.Thm_GlobalTheory_StepData_Chain_xiPen_mk
import Theorems.Thm_GlobalTheory_StepData_cosetInd_mem_SB
import Theorems.Thm_GlobalTheory_StepData_integrable_hat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
noncomputable section
open GlobalTheory GlobalTheory.Couple
namespace GlobalTheory.Couple
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z] (T : Chain k s X Z) (A : RepFam k s X) (c₁ c₂ : kˣ) (_ : T.Adapted A (box _ c₁) (box _ c₂)) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (ε : k) (S : Finset ((X (s + 1) → k) ⧸ box (X (s + 1)) c₂)) (_ : T.coupIdx A (box _ c₁) (box _ c₂) ⊆ S), ∀ g ∈ A s 0 rfl, ∀ x₀, (∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y) ∧ ∀ η, GlobalTheory.StepData.hat ψ ν ε (T.Psi g x₀) η = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * GlobalTheory.StepData.hat ψ ν ε (cosetInd (box _ c₂) yb) η := by
  intro k _ _ _ _ _ _ s X _ _ Z _ _ T A c₁ c₂ hA ψ hψ ν _ ε S hS g hg x₀
  classical
  have key : ∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := by
    intro y
    have hc : ∀ yb, cosetInd (box _ c₂) yb y = if Submodule.Quotient.mk y = yb then 1 else 0 := by
      intro yb; simp [cosetInd, Set.indicator_apply]
    simp_rw [hc, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · exact (Chain.xiPen_mk hA hg y x₀).symm
    · by_contra hne
      exact hm (Finset.mem_coe.1 (hS ⟨y, (hA g hg x₀ y).1 hne, rfl, g, hg, x₀, hne⟩))
  refine ⟨key, fun η => ?_⟩
  have hfun : T.Psi g x₀ = fun y => ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := funext key
  rw [hfun]
  simp only [GlobalTheory.StepData.hat, Finset.sum_mul]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun yb _ => ?_
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  · intro yb _
    simp_rw [mul_assoc]
    exact (integrable_hat ψ ν ε hψ (cosetInd_mem_SB c₂ yb) η).const_mul _
end GlobalTheory.Couple
