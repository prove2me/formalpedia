-- Prove2me | solution 1 for GlobalTheory.integral_div_covolume_eq_of_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:51.169623+00:00
-- url     : https://prove2.me/submissions/95808c90-b6c2-4c93-a4d1-a4b0e83c23a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ZlatticeTsumDilateSubIntegralLeRapidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptotic
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ ν : Measure V)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (f : V → ℂ) (s : ℝ) :
    (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * s : ℝ) : ℂ) =
      (∫ x, f x ∂ν) / ((ZLattice.covolume L ν * s : ℝ) : ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : μ = 0 := by simpa using hc
    exact (NeZero.ne μ) this
  let b := Module.Free.chooseBasis ℤ L
  have h1 := ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain b μ)
  have h2 := ZLattice.covolume_eq_measure_fundamentalDomain L ν
    (ZLattice.isAddFundamentalDomain b ν)
  have h3 : ZLattice.covolume L μ = (c : ℝ) * ZLattice.covolume L ν := by
    rw [h1, h2]
    conv_lhs => rw [hc]
    simp [Measure.real]
  have h4 : ∫ x, f x ∂μ = (c : ℂ) * ∫ x, f x ∂ν := by
    conv_lhs => rw [hc]
    rw [integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
  have hc1 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  rw [h3, h4]
  push_cast
  rw [mul_assoc, mul_div_mul_left _ _ hc1]
end GlobalTheory
