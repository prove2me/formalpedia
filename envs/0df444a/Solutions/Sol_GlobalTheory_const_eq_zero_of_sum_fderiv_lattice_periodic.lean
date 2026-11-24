-- Prove2me | solution 1 for GlobalTheory.const_eq_zero_of_sum_fderiv_lattice_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:21.539822+00:00
-- url     : https://prove2.me/submissions/0afd9199-da79-481e-ae9b-51f35a77584e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Theorems.Thm_GlobalTheory_setIntegral_fderiv_eq_zero_of_lattice_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open MeasureTheory Module
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
namespace GlobalTheory
theorem _root_.solution
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    {F : ι → E → ℂ} {a : ι → ℂ} {v : ι → E} {C : ℂ}
    (hF : ∀ k, ContDiff ℝ 1 (F k) ∧ ∀ (l : L) z, F k (z + l) = F k z)
    (hC : ∀ z, ∑ k, a k * fderiv ℝ (F k) z (v k) = C) : C = 0 := by
  classical
  let μ : Measure E := Measure.addHaar
  let b := Module.Free.chooseBasis ℤ L
  have hD : IsAddFundamentalDomain L (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ :=
    ZLattice.isAddFundamentalDomain b μ
  have hm : MeasurableSet (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_measurableSet _
  have hb : Bornology.IsBounded (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_isBounded _
  set D := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) with hDdef
  have hzero : ∀ k, ∫ z in D, fderiv ℝ (F k) z (v k) ∂μ = 0 := fun k =>
    setIntegral_fderiv_eq_zero_of_lattice_periodic μ L hD hm hb (hF k).1 (hF k).2 (v k)
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hint : ∀ k, IntegrableOn (fun z => a k * fderiv ℝ (F k) z (v k)) D μ := fun k =>
    ((continuous_const.mul
      (((hF k).1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : E) R)).mono_set hR
  have hsum : ∫ z in D, (∑ k, a k * fderiv ℝ (F k) z (v k)) ∂μ = 0 := by
    rw [integral_finsetSum _ (fun k _ => hint k)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, hzero k, mul_zero]
  simp_rw [hC] at hsum
  rw [setIntegral_const] at hsum
  have : VAddInvariantMeasure L E μ := ⟨fun g s _ => measure_preimage_add μ (g : E) s⟩
  have hne : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)
  have hfin : μ D ≠ ⊤ := hb.measure_lt_top.ne
  rcases smul_eq_zero.1 hsum with h | h
  · exact absurd h (ENNReal.toReal_ne_zero.2 ⟨hne, hfin⟩)
  · exact h
end GlobalTheory
