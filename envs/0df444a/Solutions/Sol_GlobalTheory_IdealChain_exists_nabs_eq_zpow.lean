-- Prove2me | solution 1 for GlobalTheory.IdealChain.exists_nabs_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:54.882052+00:00
-- url     : https://prove2.me/submissions/d45e8511-66d6-4620-9038-2c64ea9662a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_inv
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_pow
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_iff
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IdealChain
theorem _root_.solution (x : kˣ) : ∃ e : ℤ, nabs k x = (resCard k : ℝ) ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have key : ∀ x : kˣ, (x : k) ∈ 𝒪[k] → ∃ e : ℤ, nabs k x = (resCard k : ℝ) ^ e := fun x hx => by
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x, hx⟩ : 𝒪[k])) (fun h => x.ne_zero (congrArg Subtype.val h)) hϖ
    have hu' : (x : k) = ((u : 𝒪[k]) : k) * (ϖ : k) ^ m := by simpa using congrArg Subtype.val hu
    have hv : valuation k ((u : 𝒪[k]) : k) = 1 :=
      (Valuation.Integers.valuation_unit (Valuation.integer.integers (valuation k)) u)
    have : nabs k x = nabs k (Units.mk0 (ϖ : k) h0 ^ m) := by
      rw [nabs_eq_iff, hu', map_mul, hv, one_mul]
      simp
    refine ⟨-m, ?_⟩
    rw [this, OpELevi.nabs_pow, nabs_uniformiser hϖ rfl]
    simp
  rcases le_total (valuation k (x : k)) 1 with h | h
  · exact key x h
  · obtain ⟨e, he⟩ := key x⁻¹ (by
      change valuation k _ ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_le_one_of_one_le₀ h)
    rw [OpELevi.nabs_inv] at he
    exact ⟨-e, by rw [_root_.zpow_neg, ← he, inv_inv]⟩
end GlobalTheory.IdealChain
