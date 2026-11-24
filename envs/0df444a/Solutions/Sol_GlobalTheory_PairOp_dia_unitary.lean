-- Prove2me | solution 1 for GlobalTheory.PairOp.dia_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:19:56.417094+00:00
-- url     : https://prove2.me/submissions/f3753f88-099d-477e-a120-74f4db95f442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_keepsFinite_dia
import Theorems.Thm_GlobalTheory_PairOp_isAdj_dia

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
theorem _root_.solution {W : Submodule ℂ (Form k n ℂ)} (hW : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ W, dia c φ ∈ W) (c : 𝓀[k]ˣ) :
    IsScaledUnitaryOn W 1 (dia c) := by
  have hinv : ∀ d : 𝓀[k]ˣ, ∀ φ : Form k n ℂ, dia d⁻¹ (dia d φ) = φ := fun d φ => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine ⟨⟨fun φ hφ => ⟨hW c φ hφ.1, keepsFinite_dia c φ hφ.2⟩, fun φ _ φ' _ e => ?_, fun φ hφ => ?_⟩,
    fun φ _ φ' _ hf hf' => ?_⟩
  · rw [← hinv c φ, e, hinv c φ']
  · refine ⟨dia c⁻¹ φ, ⟨hW c⁻¹ φ hφ.1, keepsFinite_dia c⁻¹ φ hφ.2⟩, ?_⟩
    have := hinv c⁻¹ φ
    rwa [inv_inv] at this
  · rw [isAdj_dia c _ _ hf (keepsFinite_dia c φ' hf'), hinv c φ', one_mul]
end GlobalTheory.PairOp
