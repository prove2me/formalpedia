-- Prove2me | solution 1 for GlobalTheory.Proof.TwistSupportPeriodicLevels.parPhi_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:10.422789+00:00
-- url     : https://prove2.me/submissions/296947f6-fa56-4c0e-8b46-04c6926e0ad3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_intM
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_exists_mul_KOne
import Theorems.Thm_GlobalTheory_StepData_maxM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_parPhi_ne_zero_iff
import Theorems.Thm_GlobalTheory_StepData_parPhi_of_mem
import Theorems.Thm_GlobalTheory_StepData_tame_det_of_mem_KOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type} [Fintype r] [DecidableEq r]
private theorem parPhi_add_eq_of_maxM {δ : kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) (hx : parPhi δ x ≠ 0) : parPhi δ (x + y) = parPhi δ x := by

  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  have hyb : MaxM (Matrix.fromBlocks y.toBlocks₁₁ y.toBlocks₁₂ y.toBlocks₂₁ y.toBlocks₂₂) := by
    rwa [Matrix.fromBlocks_toBlocks]
  obtain ⟨hy11, hy12, hy21, hy22⟩ := maxM_fromBlocks.mp hyb
  have a11 : (x + y).toBlocks₁₁ = x.toBlocks₁₁ + y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
  have a12 : (x + y).toBlocks₁₂ = x.toBlocks₁₂ + y.toBlocks₁₂ := Matrix.ext fun _ _ => rfl
  have a21 : (x + y).toBlocks₂₁ = x.toBlocks₂₁ + y.toBlocks₂₁ := Matrix.ext fun _ _ => rfl
  have a22 : (x + y).toBlocks₂₂ = x.toBlocks₂₂ + y.toBlocks₂₂ := Matrix.ext fun _ _ => rfl
  have hM : MaxM ((x + y).toBlocks₁₁ - g.val) := by
    rw [a11, ← e]
    simpa using hy11
  obtain ⟨u, hu, hgu⟩ := exists_mul_KOne hg hM
  have k21 : MaxM (x + y).toBlocks₂₁ := by rw [a21]; exact h21.add hy21
  have k12 : IntM (x + y).toBlocks₁₂ := by rw [a12]; exact h12.add hy12.intM
  have k22 : IntM (x + y).toBlocks₂₂ := by rw [a22]; exact h22.add hy22.intM
  rw [parPhi_of_mem δ (mul_mem hg (KOne_le_KO hu)) hgu k21 k12 k22, parPhi_of_mem δ hg e h21 h12 h22]
  simp only [map_mul, tame_det_of_mem_KOne hδ hu, mul_one]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
end
end GlobalTheory.Proof.TwistSupportPeriodicLevels
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type} [Fintype r] [DecidableEq r]
open Classical
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
theorem _root_.solution {δ : kˣ →* ℂˣ} (hδ : IsTame δ) (x : Matrix (r ⊕ s) (r ⊕ s') k) {y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) : parPhi δ (x + y) = parPhi δ x := by
  by_cases hx : parPhi δ x = 0
  · by_contra hne
    have hxy : parPhi δ (x + y) ≠ 0 := fun h0 => hne (h0.trans hx.symm)
    have back := parPhi_add_eq_of_maxM hδ hy.neg hxy
    rw [add_neg_cancel_right] at back
    exact hxy (back.symm.trans hx)
  · exact parPhi_add_eq_of_maxM hδ hy hx
end GlobalTheory.Proof.TwistSupportPeriodicLevels
