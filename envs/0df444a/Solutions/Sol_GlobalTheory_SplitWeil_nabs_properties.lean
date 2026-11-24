-- Prove2me | solution 1 for GlobalTheory.SplitWeil.nabs_properties
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:19.959064+00:00
-- url     : https://prove2.me/submissions/68e7d607-c2b4-4f12-af01-92e4fcda786f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_le_iff
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_iff
import Theorems.Thm_GlobalTheory_SplitWeil_isLocallyConstant_nabs
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x y : kˣ, nabs k (x * y) = nabs k x * nabs k y) ∧ (∀ x : kˣ, 0 < nabs k x) ∧ (∀ x y : kˣ, nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k)) ∧ (∀ x : kˣ, nabs k x = 1 ↔ valuation k (x : k) = 1) ∧ (∀ (ϖ : 𝒪[k]) (x : kˣ), Irreducible ϖ → (x : k) = (ϖ : k) → nabs k x = (resCard k : ℝ)⁻¹) ∧ IsLocallyConstant (nabs k) ∧ 1 < resCard k :=
  fun k _ _ _ _ => ⟨nabs_mul k, nabs_pos k, nabs_le_iff, nabs_eq_one_iff,
    fun _ _ h h' => nabs_uniformiser h h', isLocallyConstant_nabs k, one_lt_resCard k⟩
end GlobalTheory.SplitWeil
