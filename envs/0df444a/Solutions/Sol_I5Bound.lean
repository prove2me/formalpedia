-- Prove2me | solution 1 for I5Bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:46:12.048439+00:00
-- url     : https://prove2.me/submissions/83dd22f9-9aad-4b77-b46b-bb85d6b70da8

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs
import Theorems.Thm_MellinOfSmooth1b

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

--open scoped ArithmeticFunction in

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED

theorem solution {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by
  unfold LogDerivZetaIsHoloSmall HolomorphicOn at h_logDeriv_holo
  let zeta'_zeta_on_line := fun (t : ℝ) ↦ ζ' (σ₂ + t * I) / ζ (σ₂ + t * I)

  have subst : {σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
    simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, neg_le_self_iff,
      Nat.ofNat_nonneg, uIcc_of_le]
    intro z hyp_z
    simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
    simp only [mem_diff, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · constructor
      · rw [hyp_z.1]
        apply left_mem_uIcc
      · exact hyp_z.2
    · push Not
      by_contra h
      rw [h] at hyp_z
      simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
      linarith [hσ₂.2]

  have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn

  have is_compact' : IsCompact ({σ₂} ×ℂ uIcc (-3) 3) := by
    refine IsCompact.reProdIm ?_ ?_
    · exact isCompact_singleton
    · exact isCompact_uIcc

  let ⟨zeta_bound, zeta_prop⟩ :=
    IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

  let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

  unfold I₅
  unfold SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith[hσ₂.2]))

  simp only [mul_inv_rev] at mellin_prop

  let Const := 1 + (σ₂^2)⁻¹ * (abs zeta_bound) * M

  let C := |π|⁻¹ * 2⁻¹ * 6 * Const
  use C
  have C_pos : 0 < C := by positivity
  use C_pos

  clear C_pos

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < σ₂^2 := by
    exact sq_pos_of_pos (by linarith[hσ₂.1])

  have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        simp only [le_add_iff_nonneg_right]
        exact zpow_two_nonneg t
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add]
        ring_nf
        positivity
      positivity

  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
    intro t hyp_t
    have Z := by
      calc
        ‖(-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)) * (𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · trivial
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z

  -- Now want to apply the triangle inequality
  -- and bound everything trivially
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε := by
    unfold C
    ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)

open Filter Topology

-- `x * rexp (-c * (log x) ^ B)) = Real.exp (Real.log x - c * (Real.log x) ^ B))`
-- so if `B < 1`, the exponent goes to infinity
