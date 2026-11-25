-- Prove2me | solution 1 for GlobalTheory.LGrp.IsMatrixCoeff.checkFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:57:41.378849+00:00
-- url     : https://prove2.me/submissions/3173c11d-733f-4511-9132-d192462a0b6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
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
variable {A G H V W : Type} [Group A] [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.LGrp
namespace IsMatrixCoeff
theorem _root_.solution {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {c : G → ℂ} (h : IsMatrixCoeff ρ c) :
    IsMatrixCoeff (smoothDual ρ) (checkFun c) := by
  obtain ⟨v, l, rfl⟩ := h
  refine ⟨l, ⟨(LinearMap.applyₗ v).comp (Submodule.subtype _), ?_⟩, rfl⟩
  refine SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) fun g hg => ?_)
  refine LinearMap.ext fun m => ?_
  show m.1 (ρ g⁻¹⁻¹ v) = m.1 v
  rw [inv_inv, show ρ g v = v from hg]
end IsMatrixCoeff
end GlobalTheory.LGrp
