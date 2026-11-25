-- Prove2me | solution 1 for GlobalTheory.LGrp.IsZonal.one_and_biinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:57:43.106005+00:00
-- url     : https://prove2.me/submissions/41f3bba1-894f-4b2e-97eb-23623da315e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_fixed
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp
namespace IsZonal
theorem _root_.solution {ρ : Representation ℂ G V} {K : Subgroup G} {ω : G → ℂ} (h : IsZonal ρ K ω) :
    ω 1 = 1 ∧ ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, ω (k₁ * g * k₂) = ω g := by
  obtain ⟨v, hv, l, hl, h1, rfl⟩ := h
  refine ⟨by simpa [coeff] using h1, fun k₁ h₁ k₂ h₂ g => ?_⟩
  simp only [coeff, map_mul, Module.End.mul_apply]
  rw [mem_fixed.1 hv k₂ h₂, hl k₁ h₁]
end IsZonal
end GlobalTheory.LGrp
