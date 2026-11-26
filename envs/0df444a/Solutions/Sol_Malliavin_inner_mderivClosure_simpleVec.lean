-- Prove2me | solution 1 for Malliavin.inner_mderivClosure_simpleVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:43.185103+00:00
-- url     : https://prove2.me/submissions/b7bdbd71-0cc5-481e-b04b-4f9b0b867afd

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) (k : SimpleIndex μ) :
    ⟪mderivClosure μ F, simpleVec μ k⟫_ℝ = ⟪F, simpleDiv μ k⟫_ℝ := by
  obtain ⟨Fk, hF1, hD1⟩ := inGraphClosure_mderivClosure μ hF
  have h1 : Tendsto (fun n ↦ ⟪(Fk n).2.mderivLp μ, simpleVec μ k⟫_ℝ) atTop
      (𝓝 ⟪mderivClosure μ F, simpleVec μ k⟫_ℝ) :=
    Filter.Tendsto.inner (𝕜 := ℝ) hD1 (tendsto_const_nhds (x := simpleVec μ k))
  have e : (fun n ↦ ⟪(Fk n).2.mderivLp μ, simpleVec μ k⟫_ℝ) =
      fun n ↦ ⟪(Fk n).2.toLp μ, simpleDiv μ k⟫_ℝ :=
    funext fun n ↦ inner_mderivLp_smulLp μ (Fk n).2 k.1.2 k.2
  have h2 : Tendsto (fun n ↦ ⟪(Fk n).2.toLp μ, simpleDiv μ k⟫_ℝ) atTop
      (𝓝 ⟪F, simpleDiv μ k⟫_ℝ) :=
    Filter.Tendsto.inner (𝕜 := ℝ) hF1 (tendsto_const_nhds (x := simpleDiv μ k))
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2
end Malliavin
