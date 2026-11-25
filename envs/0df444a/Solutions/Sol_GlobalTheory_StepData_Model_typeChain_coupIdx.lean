-- Prove2me | solution 1 for GlobalTheory.StepData.Model.typeChain_coupIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:36.967653+00:00
-- url     : https://prove2.me/submissions/39d25647-d4d1-4de5-bc17-f83cbb98a42c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_StepData_Model_typeChain_adapted
import Theorems.Thm_GlobalTheory_StepData_Model_coords_surjective
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_one
import Theorems.Thm_GlobalTheory_StepData_Chain_xiPen_mk
import Theorems.Thm_GlobalTheory_StepData_maxM_zero
import Theorems.Thm_GlobalTheory_StepData_withCol_blocks


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
variable {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData.Model
theorem _root_.solution {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {s : ℕ} (P : TypeDatum k (κ ⊕ Fin (s + 1)))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (A : RepFam k s (XIx κ t))
    (hA : (typeChain t ϖ P μ hμ).RepsInStab A) (h1 : 1 ∈ A s 0 rfl) :
    ∃ yb ∈ (typeChain t ϖ P μ hμ).coupIdx A (box _ ϖ⁻¹) (box _ 1),
      (typeChain t ϖ P μ hμ).xiPen (box _ 1) 1 yb ≠ 0 := by
  have H := typeChain_adapted hϖ P μ hμ A hA
  obtain ⟨x, hx⟩ := coords_surjective (typeFrame ϖ (stdOrd κ t (l := s + 1) (s + 1) 0 rfl))
    (typeFrame ϖ (stdOrd κ t (l := s + 1) s (0 + 1) rfl))
    ((fromRows (1 : Matrix _ _ k) (0 : Matrix t _ k)).submatrix (ixSucc _ t s).symm id)
  have hne : (typeChain t ϖ P μ hμ).Psi 1 x.toBlocks₁₁ (fun r => x (.inl r) (.inr 0)) ≠ 0 := by
    rw [Chain.Psi, om_one, withCol_blocks]
    change P.iterPhi t μ hμ s (LatFrame.coords _ _ x) ≠ 0
    rw [hx, TypeDatum.iterPhi, TypeDatum.Phi_ne_zero_iff]
    simp only [submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id, submatrix_id_id]
    exact ⟨⟨1, one_mem _, by simp⟩, by simpa using maxM_zero⟩
  exact ⟨_, ⟨_, (H 1 h1 _ _).1 hne, rfl, 1, h1, _, hne⟩,
    fun h0 => hne ((Chain.xiPen_mk H h1 _ _).symm.trans (congrFun h0 _))⟩
end GlobalTheory.StepData.Model
