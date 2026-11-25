-- Prove2me | solution 1 for GlobalTheory.LGrp.borelGL_two_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:58:25.320371+00:00
-- url     : https://prove2.me/submissions/9d3aa6a9-4780-48df-92d3-8ca138d4beb0

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
theorem _root_.solution : (borelGL k (Fin 2)).U ≠ ⊥ ∧ (borelGL k (Fin 2)).Q ≠ ⊤ := by
  constructor
  · intro h
    let g : GL (Fin 2) k := ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by simp [← Matrix.one_fin_two], by simp [← Matrix.one_fin_two]⟩
    have hg : g ∈ (borelGL k (Fin 2)).U := by
      refine (LeviDatum.mem_U _).2 ⟨fun i j e => ?_, funext fun i => Units.ext ?_⟩
      · fin_cases i <;> fin_cases j <;> simp_all [g]
      · show g.val i i = 1
        fin_cases i <;> simp [g]
    rw [h, Subgroup.mem_bot] at hg
    simpa [g] using congrArg (fun x : GL (Fin 2) k => x.val 0 1) hg
  · intro h
    let g : GL (Fin 2) k := ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by simp [← Matrix.one_fin_two], by simp [← Matrix.one_fin_two]⟩
    have hg : g ∈ (borelGL k (Fin 2)).Q := h ▸ Subgroup.mem_top g
    simpa [g] using hg (show (id 0 : Fin 2) < id 1 by decide)
end GlobalTheory.LGrp
