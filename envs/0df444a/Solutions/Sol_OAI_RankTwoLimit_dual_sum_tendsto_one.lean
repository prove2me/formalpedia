-- Prove2me | solution 1 for OAI.RankTwoLimit.dual_sum_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:40.315088+00:00
-- url     : https://prove2.me/submissions/11c5a158-b2ae-4132-89ff-a8b3828186b3

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_RankTwoEisShift_dualPhase_norm
import Theorems.Thm_OAI_RankTwoPoisson_eisQ_lower
import Theorems.Thm_OAI_RankTwoPoisson_eis_gauss_summable
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace OscillatoryDeterminant
open Complex
end OscillatoryDeterminant
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinFiberShift
end EisensteinFiberShift
namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates
end ShortDraftLatticeCount
namespace EisensteinGaussianPrefactor
end EisensteinGaussianPrefactor
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinGaussianPrefactor
end EisensteinGaussianPrefactor
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace OscillatoryDeterminant
open Complex
end OscillatoryDeterminant
open Filter Real Asymptotics
namespace RankTwoLimit
section
open scoped Topology
open RankTwoPoisson RankTwoEisShift Filter
private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
private theorem eisQ_pos {z : ℤ × ℤ} (hz : z ≠ (0,0)) :
    0 < RankTwoPoisson.eisQ z := by
  by_cases hm : z.1 = 0
  · have hn : z.2 ≠ 0 := by
      intro h0
      exact hz (Prod.ext hm h0)
    have hnR : (z.2 : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hnR]
  · have hmR : (z.1 : ℝ) ≠ 0 := by exact_mod_cast hm
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hmR, sq_nonneg (z.2 : ℝ)]
private theorem eisGauss_norm (T : ℝ) (z : ℤ × ℤ) :
    ‖RankTwoPoisson.eisGauss T z‖ =
      Real.exp (-Real.pi * T * RankTwoPoisson.eisQ z) := by
  simp [RankTwoPoisson.eisGauss, Complex.norm_exp]
private theorem dualTerm_tendsto (x y : ℝ) (z : ℤ × ℤ) :
    Tendsto (fun T : ℝ => dualTerm T x y z) atTop (𝓝 (limitTerm z)) := by
  by_cases hz : z = (0,0)
  · subst z
    simp [dualTerm, limitTerm, RankTwoPoisson.eisGauss,
      RankTwoPoisson.eisQ, RankTwoEisShift.dualPhase]
  · have hz' : (z.1,-z.2) ≠ ((0,0) : ℤ × ℤ) := by
      intro h
      apply hz
      have h1 : z.1 = 0 := by simpa using congrArg Prod.fst h
      have h2 : z.2 = 0 := by simpa using congrArg Prod.snd h
      exact Prod.ext h1 h2
    have hq := eisQ_pos hz'
    have hneg : -Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) < 0 := by
      nlinarith [mul_pos Real.pi_pos hq]
    have harg : Tendsto
        (fun T : ℝ => -Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2))
        atTop atBot := by
      convert tendsto_id.const_mul_atTop_of_neg hneg using 1
      ext T
      simp [mul_assoc, mul_comm]
    have hexp : Tendsto
        (fun T : ℝ => Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
    have hc : Tendsto (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2))
        atTop (𝓝 (0 : ℂ)) := by
      have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp hexp
      have heq : (fun T : ℝ =>
          ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ)) =
          (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2)) := by
        funext T
        simp [RankTwoPoisson.eisGauss, Complex.ofReal_exp]
      change Tendsto (fun T : ℝ =>
        ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) at hh
      rw [heq] at hh
      exact hh
    simpa [dualTerm, limitTerm, hz] using
      hc.mul_const (RankTwoEisShift.dualPhase z.1 z.2 x y)
end
open scoped Topology
open Filter
end RankTwoLimit
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.RankTwoLimit
open scoped Topology
open RankTwoPoisson RankTwoEisShift Filter
namespace OAI.RankTwoLimit
theorem _root_.solution (x y : ℝ) :
    Tendsto (fun T : ℝ => ∑' z : ℤ × ℤ, dualTerm T x y z)
      atTop (𝓝 (1 : ℂ)) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss 1 (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable (by norm_num))
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ z : ℤ × ℤ,
      ‖dualTerm T x y z‖ ≤ ‖RankTwoPoisson.eisGauss 1 (z.1,-z.2)‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT z
    rw [dualTerm, norm_mul, RankTwoEisShift.dualPhase_norm, mul_one,
      eisGauss_norm, eisGauss_norm]
    have hq := eisQ_nonneg (z.1,-z.2)
    have hpq : 0 ≤ Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) :=
      mul_nonneg Real.pi_pos.le hq
    have hm := mul_le_mul_of_nonneg_right hT hpq
    apply Real.exp_le_exp.mpr
    nlinarith [hm]
  have h := tendsto_tsum_of_dominated_convergence hE.norm
    (dualTerm_tendsto x y) hbound
  simpa [limitTerm] using h
end OAI.RankTwoLimit
