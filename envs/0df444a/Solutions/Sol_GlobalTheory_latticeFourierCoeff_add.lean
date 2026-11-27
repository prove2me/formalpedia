-- Prove2me | solution 1 for GlobalTheory.latticeFourierCoeff_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:38:59.699793+00:00
-- url     : https://prove2.me/submissions/4327af3c-21ba-4c50-8de2-18c4f079b179

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
theorem _root_.solution {A B : E → V} (hA : Continuous A) (hB : Continuous B) (ν : E) :
    latticeFourierCoeff L (fun b ↦ A b + B b) ν =
      latticeFourierCoeff L A ν + latticeFourierCoeff L B ν := by
  simp only [latticeFourierCoeff, smul_add]
  rw [integral_add (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hA ν)) (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hB ν)), smul_add]
end GlobalTheory
