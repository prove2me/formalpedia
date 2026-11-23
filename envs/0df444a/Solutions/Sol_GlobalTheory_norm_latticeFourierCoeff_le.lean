-- Prove2me | solution 1 for GlobalTheory.norm_latticeFourierCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:00.172547+00:00
-- url     : https://prove2.me/submissions/3df11ead-bbd7-4552-9a73-6b24b94d1e09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_volume_latticeCell_lt_top
import Theorems.Thm_GlobalTheory_covolume_eq_volume_latticeCell
import Theorems.Thm_GlobalTheory_norm_cexp_two_pi_I

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
theorem _root_.solution {A : E → V} {S : ℝ} (hS : ∀ b, ‖A b‖ ≤ S) (ν : E) :
    ‖latticeFourierCoeff L A ν‖ ≤ S := by
  have hpos := ZLattice.covolume_pos L volume
  unfold latticeFourierCoeff
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos,
    covolume_eq_volume_latticeCell, mul_comm _ S]
  refine norm_setIntegral_le_of_norm_le_const (volume_latticeCell_lt_top L) fun b _ ↦ ?_
  rw [norm_smul, norm_cexp_two_pi_I, one_mul]
  exact hS b
end GlobalTheory
