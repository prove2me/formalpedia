-- Prove2me | solution 1 for GlobalTheory.LGrp.isSmooth_unram_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:10:25.194749+00:00
-- url     : https://prove2.me/submissions/62a7be22-f4fe-4531-b58b-d13e33a74522

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_isSmooth_charRep
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
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LGrp
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ} (hμ : SplitWeil.IsUnram μ) :
    IsSmooth (charRep (μ.comp (Matrix.GeneralLinearGroup.det (n := n)))) := by
  refine isSmooth_charRep _ ?_
  have h1 : {y : k | valuation k y = valuation k 1} ∈ nhds (1 : k) := by
    let _ := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    exact Valued.locally_const (R := k) (x := 1) (by simp)
  have hc : Continuous fun g : GL n k => g.val.det := Units.continuous_val.matrix_det
  have h2 := hc.continuousAt (x := 1) (show _ ∈ nhds (1 : GL n k).val.det by simpa using h1)
  refine Filter.mem_of_superset h2 fun g hg => hμ _ ?_
  simpa using hg
end GlobalTheory.LGrp
