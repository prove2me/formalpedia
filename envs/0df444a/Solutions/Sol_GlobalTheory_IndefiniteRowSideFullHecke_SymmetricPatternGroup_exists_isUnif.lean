-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup.exists_isUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:24.91309+00:00
-- url     : https://prove2.me/submissions/def6f048-b834-4e6d-8203-8522ba3f1c97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
theorem _root_.solution : ∃ ϖ : kˣ, IsUnif ϖ := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (p : k) ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  have h1 : valuation k (p : k) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hp.not_isUnit
  refine ⟨Units.mk0 _ h0, fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx h1⟩⟩
  have hm : (⟨x, hx.le⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hx
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨a, ha⟩ := hm
  have : x = (a : k) * p := (congrArg Subtype.val ha).symm
  rw [this, map_mul]
  exact mul_le_of_le_one_left' a.2
end GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
