-- Prove2me | solution 1 for GlobalTheory.latticeFourierCoeff_eq_setIntegral_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:05.732859+00:00
-- url     : https://prove2.me/submissions/8b5f74a6-ce89-46f0-beae-2a7433407ddb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_isAddFundamentalDomain_latticeCell
import Theorems.Thm_GlobalTheory_covolume_eq_volume_latticeCell
import Theorems.Thm_GlobalTheory_cexp_neg_inner_add_lattice
import Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_cube

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
theorem _root_.solution {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {ν : E} (hν : ν ∈ L*) (μ : Measure E) [μ.IsAddHaarMeasure] {F : Set E}
    (hF : IsAddFundamentalDomain L F μ) :
    latticeFourierCoeff L A ν = (ZLattice.covolume L μ)⁻¹ • ∫ b in F, e[-⟪ν, b⟫] • A b ∂μ := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  rw [← (isAddFundamentalDomain_latticeCell L μ).setIntegral_eq hF fun x b ↦ ?_,
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain_latticeCell L μ),
    latticeFourierCoeff, covolume_eq_volume_latticeCell, latticeCell,
    average_fundamentalDomain_eq_cube, average_fundamentalDomain_eq_cube]
  have : x +ᵥ b = b + (x : E) := add_comm _ _
  rw [this, cexp_neg_inner_add_lattice hν x.2, hA x x.2]
end GlobalTheory
