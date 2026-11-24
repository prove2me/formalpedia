-- Prove2me | solution 1 for GlobalTheory.latticeFourierCoeff_eq_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:16.185807+00:00
-- url     : https://prove2.me/submissions/52e305f0-010d-47d0-bc59-6cfdb2a7b0b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_isAddFundamentalDomain_latticeCell
import Theorems.Thm_GlobalTheory_cexp_neg_inner_add_lattice

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
    {ν : E} (hν : ν ∈ L*) {F : Set E} (hF : IsAddFundamentalDomain L F volume) :
    latticeFourierCoeff L A ν =
      (ZLattice.covolume L)⁻¹ • ∫ b in F, e[-⟪ν, b⟫] • A b := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  unfold latticeFourierCoeff
  congr 1
  refine (isAddFundamentalDomain_latticeCell L _).setIntegral_eq hF fun x b ↦ ?_
  have : x +ᵥ b = b + (x : E) := add_comm _ _
  rw [this, cexp_neg_inner_add_lattice hν x.2, hA x x.2]
end GlobalTheory
