-- Prove2me | solution 1 for GlobalTheory.PairOp.isScaledUnitaryOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:19:57.899284+00:00
-- url     : https://prove2.me/submissions/4479ec0b-4c0c-45eb-b38c-33ba2326d459

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_cntIp_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
namespace GlobalTheory.PairOp
theorem _root_.solution {W : Submodule ℂ (Form k n ℂ)} {a : ℂ} (ha : a ≠ 0) (ha' : (starRingEnd ℂ) a = a)
    (hA : KeepsFinite A) (hB : KeepsFinite B) (hAW : ∀ φ ∈ W, A φ ∈ W) (hBW : ∀ φ ∈ W, B φ ∈ W) (h : IsAdj A B)
    (hBA : ∀ φ ∈ W, B (A φ) = a • φ) (hAB : ∀ φ ∈ W, A (B φ) = a • φ) : IsScaledUnitaryOn W a A := by
  refine ⟨⟨fun φ hφ => ⟨hAW φ hφ.1, hA φ hφ.2⟩, fun φ hφ φ' hφ' e => ?_, fun φ hφ => ?_⟩,
    fun φ hφ φ' hφ' hf hf' => ?_⟩
  · have := congrArg B e
    rw [hBA φ hφ.1, hBA φ' hφ'.1] at this
    exact smul_right_injective _ ha this
  · refine ⟨a⁻¹ • B φ, ⟨W.smul_mem _ (hBW φ hφ.1), ?_⟩, ?_⟩
    · exact (hB φ hφ.2).subset (Function.support_const_smul_subset _ _)
    · rw [map_smul, hAB φ hφ.1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · rw [h _ _ hf (hA φ' hf'), hBA φ' hφ', cntIp_smul_right, ha']
end GlobalTheory.PairOp
