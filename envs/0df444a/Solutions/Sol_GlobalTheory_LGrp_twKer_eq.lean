-- Prove2me | solution 1 for GlobalTheory.LGrp.twKer_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:58:25.28553+00:00
-- url     : https://prove2.me/submissions/fe56fe58-9348-4906-ae70-7c771adf5b74

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
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp
theorem _root_.solution (ρ : Representation ℂ G V) (N : Subgroup G) (ψ : N →* ℂˣ) :
    twKer ρ N ψ = Representation.Coinvariants.ker (twist ψ⁻¹ (ρ.comp N.subtype)) := by
  unfold twKer Representation.Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨n, v, rfl⟩; exact ⟨(n, (ψ n : ℂ) • v), by simp [smul_smul]⟩
  · rintro ⟨⟨n, v⟩, rfl⟩; exact ⟨n, ((ψ n : ℂ))⁻¹ • v, by simp [smul_smul]⟩
end GlobalTheory.LGrp
