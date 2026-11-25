-- Prove2me | solution 1 for GlobalTheory.LGrp.lineParU_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:58:58.294606+00:00
-- url     : https://prove2.me/submissions/3852122a-f5d0-4cfa-8e16-fb57afc2e201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_lineParU_U
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
open Formalism.UG
variable {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)
omit σ hσ hc
variable {ϖ : L} {σ : L →+* L} {q : ℕ}
namespace GlobalTheory.LGrp
theorem _root_.solution (h : IsUnramInv ϖ σ q) (n : ℕ) :
    (lineParU σ h.1 (continuous_of_unramInv h) n).U ≠ ⊥ := by
  obtain ⟨z, -, hz⟩ := h.2.2.2.2.1
  have hx : σ z - z ≠ 0 := fun e => by simp [e] at hz
  have hne : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := Fin.last_pos.ne
  let g : GL (Fin (n + 2)) L := ⟨transvection 0 (Fin.last (n + 1)) (σ z - z),
    transvection 0 (Fin.last (n + 1)) (-(σ z - z)), by simp [transvection_mul_transvection_same _ _ hne],
    by simp [transvection_mul_transvection_same _ _ hne]⟩
  have hg : g ∈ GU σ (n + 2) := by
    rw [mem_GU_iff]
    intro i j
    show transvection 0 (Fin.last (n + 1)) (-(σ z - z)) i j = σ (transvection 0 (Fin.last (n + 1)) (σ z - z) j.rev i.rev)
    induction i using lineCases <;> induction j using lineCases <;>
      simp [transvection, Matrix.one_apply, Matrix.single_apply, h.1, apply_ite σ, eq_comm]
  have hu : (⟨g, hg⟩ : GU σ (n + 2)) ∈ (lineParU σ h.1 (continuous_of_unramInv h) n).U := by
    rw [mem_lineParU_U]
    refine ⟨fun i hi => ?_, ?_, fun i j => ?_⟩
    · simp [g, transvection, hi, hne.symm]
    · simp [g, transvection, hne.symm]
    · simp [g, transvection, Matrix.one_apply, (midIdx_ne_zero i).symm]
  intro e
  rw [e, Subgroup.mem_bot] at hu
  exact hx (by simpa [g, transvection, hne] using congrArg (fun x : GU σ (n + 2) => x.1.val 0 (Fin.last (n + 1))) hu)
end GlobalTheory.LGrp
