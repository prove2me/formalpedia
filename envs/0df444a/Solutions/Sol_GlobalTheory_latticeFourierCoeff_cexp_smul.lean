-- Prove2me | solution 1 for GlobalTheory.latticeFourierCoeff_cexp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:12.127735+00:00
-- url     : https://prove2.me/submissions/2177d7ea-d3d0-4e0a-bbf8-80e372f8d11c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_covolume_eq_volume_latticeCell
import Theorems.Thm_GlobalTheory_cexp_two_pi_I_add
import Theorems.Thm_GlobalTheory_cexp_two_pi_I_half
import Theorems.Thm_GlobalTheory_cexp_inner_add_lattice
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_comp_add
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_smul

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
theorem _root_.solution [CompleteSpace V] [DecidableEq E] {μ ν : E} (hμ : μ ∈ L*)
    (hν : ν ∈ L*) (v : V) :
    latticeFourierCoeff L (fun b ↦ e[⟪μ, b⟫] • v) ν = if μ = ν then v else 0 := by
  split_ifs with h
  · subst h
    have hpos := ZLattice.covolume_pos L volume
    simp only [latticeFourierCoeff, smul_smul, ← cexp_two_pi_I_add, neg_add_cancel]
    simp [← covolume_eq_volume_latticeCell, smul_smul, hpos.ne']
  · have hn : 0 < ‖μ - ν‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
    set c : E := (2 * ‖μ - ν‖ ^ 2)⁻¹ • (μ - ν) with hc
    have h1 : ⟪μ, c⟫ = ⟪ν, c⟫ + 1 / 2 := by
      rw [← sub_eq_iff_eq_add', ← inner_sub_left, hc, inner_smul_right,
        real_inner_self_eq_norm_sq]; field_simp
    have h2 := latticeFourierCoeff_comp_add (L := L) (A := fun b ↦ e[⟪μ, b⟫] • v)
      (fun x hx b ↦ by simp only [cexp_inner_add_lattice hμ hx]) hν c
    simp only [inner_add_right, cexp_two_pi_I_add, mul_comm _ e[⟪μ, c⟫], mul_smul] at h2
    rw [latticeFourierCoeff_smul, h1, cexp_two_pi_I_add, cexp_two_pi_I_half, ← sub_eq_zero,
      ← sub_smul, smul_eq_zero] at h2
    refine h2.resolve_left fun h3 ↦ Complex.exp_ne_zero (2 * π * Complex.I * (⟪ν, c⟫ : ℝ)) ?_
    linear_combination (-1 / 2 : ℂ) * h3
end GlobalTheory
