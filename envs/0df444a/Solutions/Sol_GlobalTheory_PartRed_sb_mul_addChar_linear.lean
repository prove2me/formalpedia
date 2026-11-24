-- Prove2me | solution 1 for GlobalTheory.PartRed.sb_mul_addChar_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:39:01.768258+00:00
-- url     : https://prove2.me/submissions/6c83ba77-498f-4f97-b825-34ed7692037d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearForm
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_OpenKernel_isLocallyConstant_coe_addChar
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.PartRed
namespace GlobalTheory.PartRed
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] (f : Matrix R Q k →ₗ[k] k) (z : k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => (ψ (f x + z) : ℂ) * Φ x) ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ ψ hψ R Q _ _ f z Φ hΦ
  classical
  obtain ⟨h1, h2⟩ := hΦ
  have hexp : ∀ x : Matrix R Q k, f x = ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := by
    intro x
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← LinearMap.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hf : Continuous f := by
    have : (f : Matrix R Q k → k) = fun x => ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := funext hexp
    rw [this]
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_id.matrix_elem i j).mul continuous_const
  refine ⟨?_, ?_⟩
  · exact ((OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous
      (hf.add continuous_const)).mul h1
  · exact h2.mul_left
end GlobalTheory.PartRed
