-- Prove2me | solution 1 for GlobalTheory.StepData.Model.typeChain_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:45:51.52564+00:00
-- url     : https://prove2.me/submissions/9c3ae42e-1d34-4281-ad18-e398fb7afc0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_StepData_Model_coords_typeFrame
import Theorems.Thm_GlobalTheory_StepData_HasTypes_transport
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply
import Theorems.Thm_GlobalTheory_StepData_LatFrame_om_transport
import Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_add
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_intM_of_Phi_ne_zero
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_stabLat
import Theorems.Thm_GlobalTheory_StepData_om_of_mem_KO


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
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.StepData.Model
theorem _root_.solution {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {s : ℕ} (P : TypeDatum k (κ ⊕ Fin (s + 1)))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (A : RepFam k s (XIx κ t))
    (hA : (typeChain t ϖ P μ hμ).RepsInStab A) :
    (typeChain t ϖ P μ hμ).Adapted A (box _ ϖ⁻¹) (box _ 1) := by
  intro g hg x₀ y
  let F := typeFrame ϖ (stdOrd κ t (l := s + 1) (s + 1) 0 rfl)
  let F' := typeFrame ϖ (stdOrd κ t (l := s + 1) s (0 + 1) rfl)
  have hK : reGL F'.ord (F'.conj.symm g) ∈ KO k _ := by
    have := mem_stabLat.1 (hA s 0 rfl g hg)
    have e := F'.conj_apply (F'.conj.symm g)
    rw [MulEquiv.apply_symm_apply] at e
    change F'.bas⁻¹ * g * F'.bas ∈ _ at this
    rw [e] at this
    simpa [mul_assoc] using this
  have hK' : F'.conj.symm g ∈ KO k _ :=
    ((TypeDatum.full k _).reindex F'.ord.symm).le_KO (show (reGL F'.ord.symm).symm _ ∈ KO k _ from hK)
  obtain ⟨u, rfl⟩ := F'.conj.surjective g
  rw [MulEquiv.symm_apply_apply] at hK'
  have hΨ : ∀ y, (typeChain t ϖ P μ hμ).Psi (F'.conj u) x₀ y =
      μ (s + 1) (Matrix.GeneralLinearGroup.det u) *
        P.iterPhi t μ hμ s (F.coords F' (withCol x₀ y) * u.val) := fun y => by
    have := congrFun (F.om_transport F' (μ (s + 1)) u 1 (P.iterPhi t μ hμ s)) (withCol x₀ y)
    rw [map_one] at this
    refine this.trans ?_
    rw [LatFrame.transport, om_of_mem_KO _ hK' (one_mem _)]
    simp
  refine ⟨fun h i => ?_, fun z hz => ?_⟩
  · rw [hΨ] at h
    have h1 : IntM (F.coords F' (withCol x₀ y) * u.val) := fun i l => by
      simpa using TypeDatum.intM_of_Phi_ne_zero _ _ (right_ne_zero_of_mul h) ((ixSucc _ t s).symm i) l
    have h2 := h1.mul (mem_KO.1 hK').2 (F.ord.symm (.inl i)) (F'.ord.symm (.inr 0))
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, coords_typeFrame] at h2
    simp only [F, F', typeFrame, Equiv.apply_symm_apply, wt, withCol] at h2
    have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
    have h3 : valuation k (y i) * valuation k (ϖ : k) ≤ 1 := by simpa [Valuation.mem_integer_iff] using h2
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← one_mul _⁻¹, le_mul_inv_iff₀ h0]
    exact h3
  · rw [hΨ, hΨ]
    have e : F.coords F' (withCol x₀ (y + z)) = F.coords F' (withCol x₀ y) + F.coords F' (withCol 0 z) := by
      ext i j
      rw [Matrix.add_apply, coords_typeFrame, coords_typeFrame, coords_typeFrame]
      generalize stdOrd κ t (l := s + 1) (s + 1) 0 rfl i = i'
      generalize stdOrd κ t (l := s + 1) s (0 + 1) rfl j = j'
      rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp [withCol, mul_add, add_mul]
    have m : MaxM (F.coords F' (withCol 0 z)) := fun i j => by
      rw [coords_typeFrame]
      generalize stdOrd κ t (l := s + 1) (s + 1) 0 rfl i = i'
      generalize stdOrd κ t (l := s + 1) s (0 + 1) rfl j = j'
      rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp [withCol, wt]
      exact mul_lt_one_of_nonneg_of_lt_one_right (by simpa using hz i') zero_le hϖ
    rw [e, Matrix.add_mul]
    congr 1
    have m' := m.mul_intM (intM_of_mem_KO hK')
    generalize F.coords F' (withCol 0 z) * u.val = w at m' ⊢
    generalize F.coords F' (withCol x₀ y) * u.val = w'
    exact TypeDatum.Phi_add _ (hμ _) (w'.submatrix (ixSucc _ t s) id) (y := w.submatrix (ixSucc _ t s) id)
      fun _ _ => m' _ _
end GlobalTheory.StepData.Model
