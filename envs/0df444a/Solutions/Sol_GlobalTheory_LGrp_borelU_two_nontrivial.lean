-- Prove2me | solution 1 for GlobalTheory.LGrp.borelU_two_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:58:30.7798+00:00
-- url     : https://prove2.me/submissions/230452f9-25a0-4d23-b4fa-f26acc223b5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_borelU_U
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
open Formalism.UG
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.LGrp
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : (borelU σ 2).U ≠ ⊥ := by
  obtain ⟨hσ, -, -, -, ⟨z, -, hz⟩, -⟩ := h
  have hx : σ z - z ≠ 0 := fun e => by simp [e] at hz
  let g : GL (Fin 2) L := ⟨!![1, σ z - z; 0, 1], !![1, -(σ z - z); 0, 1], by simp [← Matrix.one_fin_two],
    by simp [← Matrix.one_fin_two]⟩
  have hg : g ∈ GU σ 2 := by
    rw [mem_GU_iff]
    intro i j
    show !![1, -(σ z - z); 0, 1] i j = σ (!![1, σ z - z; 0, 1] j.rev i.rev)
    fin_cases i <;> fin_cases j <;> simp [Fin.rev, hσ]
  have hu : (⟨g, hg⟩ : GU σ 2) ∈ (borelU σ 2).U := by
    rw [mem_borelU_U]
    refine ⟨fun i j e => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all [g]
    · fin_cases i <;> simp [g]
  intro e
  rw [e, Subgroup.mem_bot] at hu
  exact hx (by simpa [g] using congrArg (fun x : GU σ 2 => x.1.val 0 1) hu)
end GlobalTheory.LGrp
