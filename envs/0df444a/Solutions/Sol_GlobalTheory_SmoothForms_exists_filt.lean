-- Prove2me | solution 1 for GlobalTheory.SmoothForms.exists_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:06.30574+00:00
-- url     : https://prove2.me/submissions/8b4acafd-7d27-455a-8267-784d7ad7fe26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracketStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutantLiftModStableSelfAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Theorems.Thm_GlobalTheory_SmoothForms_range_le_filt
import Theorems.Thm_GlobalTheory_SmoothForms_filt_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open Matrix
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}
namespace GlobalTheory.SmoothForms
theorem _root_.solution {z : A} (hz : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2)) :
    ∃ d, z ∈ filt E d := by
  have h : z ∈ Submodule.span ℂ (Submonoid.closure (Set.range fun p : Fin n × Fin n => E p.1 p.2) : Set A) := by
    rw [← Algebra.adjoin_eq_span]; exact hz
  clear hz
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    choose p hp using fun i : Fin l.length => hl (l.get i) (List.get_mem l i)
    refine ⟨l.length + 1, range_le_filt (Nat.lt_succ_self _)
      ⟨Matrix.single (fun i => (p i).1) (fun i => (p i).2) 1, ?_⟩⟩
    have e : (List.ofFn fun i => E (p i).1 (p i).2) = l := by
      simp only [hp]; exact List.ofFn_get l
    simp only [wordMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.single, of_apply, ite_smul, one_smul, zero_smul,
      ite_and]
    simp [e]
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, add_mem (filt_mono (le_max_left _ _) ha) (filt_mono (le_max_right _ _) hb)⟩
  | smul c x _ hx => exact ⟨_, Submodule.smul_mem _ c hx.choose_spec⟩
end GlobalTheory.SmoothForms
