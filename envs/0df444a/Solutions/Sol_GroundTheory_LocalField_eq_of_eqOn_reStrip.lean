-- Prove2me | solution 1 for GroundTheory.LocalField.eq_of_eqOn_reStrip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:26:40.26221+00:00
-- url     : https://prove2.me/submissions/33701237-1cc9-4265-8691-70c5e2860bd3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {a b : ℝ} (hab : a < b) (h : ∀ s : ℂ, a < s.re → s.re < b → F s = G s) : F = G := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hGa : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.analyticAt z
  have hopen : IsOpen {s : ℂ | a < s.re ∧ s.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : (((a + b) / 2 : ℝ) : ℂ) ∈ {s : ℂ | a < s.re ∧ s.re < b} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    constructor <;> linarith
  refine hFa.eq_of_eventuallyEq hGa (z₀ := (((a + b) / 2 : ℝ) : ℂ)) ?_
  filter_upwards [hopen.mem_nhds hmem] with s hs using h s hs.1 hs.2
end GroundTheory.LocalField
