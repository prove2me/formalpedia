-- Prove2me | solution 1 for GlobalTheory.latticeFourierCoeff_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:56.923377+00:00
-- url     : https://prove2.me/submissions/0f013f80-28c2-428a-a0c0-564fbb45a9ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_integrableOn_latticeCell_of_continuous
import Theorems.Thm_GlobalTheory_continuous_cexp_neg_inner_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}
namespace GlobalTheory
theorem _root_.solution [CompleteSpace V] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [CompleteSpace W] (T : V →L[ℂ] W) {A : E → V} (hA : Continuous A) (ν : E) :
    latticeFourierCoeff L (fun b ↦ T (A b)) ν = T (latticeFourierCoeff L A ν) := by
  simp only [latticeFourierCoeff, ← map_smul]
  rw [T.integral_comp_comm (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hA ν)), T.map_smul_of_tower]
end GlobalTheory
