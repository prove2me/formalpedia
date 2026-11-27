-- Prove2me | solution 1 for GlobalTheory.hasSum_latticeFourierCoeff_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:33.214134+00:00
-- url     : https://prove2.me/submissions/f87e22d7-523f-4c41-b6b1-dbf3fce66bc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_integrableOn_latticeCell_of_continuous
import Theorems.Thm_GlobalTheory_norm_cexp_two_pi_I
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_cexp_smul

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
theorem _root_.solution [CompleteSpace V] [DecidableEq E] {ι : Type*}
    [Countable ι] {m : ι → E} (hm : ∀ j, m j ∈ L*) {a : ι → V} (ha : Summable fun j ↦ ‖a j‖)
    {ν : E} (hν : ν ∈ L*) :
    HasSum (fun j ↦ if m j = ν then a j else 0)
      (latticeFourierCoeff L (fun b ↦ ∑' j, e[⟪m j, b⟫] • a j) ν) := by
  simp only [← fun j ↦ latticeFourierCoeff_cexp_smul (hm j) hν (a j), latticeFourierCoeff]
  refine HasSum.const_smul _ ?_
  simp only [← tsum_const_smul'' e[-⟪ν, _⟫]]
  refine hasSum_integral_of_summable_integral_norm (fun j ↦ integrableOn_latticeCell_of_continuous L
    (by fun_prop)) ?_
  simp only [norm_smul, norm_cexp_two_pi_I, one_mul, integral_const]
  exact ha.const_smul _
end GlobalTheory
