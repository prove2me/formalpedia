-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.hasSum_smul_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:34:02.083891+00:00
-- url     : https://prove2.me/submissions/6dbc41d0-e8bd-4fe6-80e9-94ebd2eedb0e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Theorems.Thm_GroundTheory_Global_LatticePoisson_inner_equivFun_symm_dualPt
import Theorems.Thm_GroundTheory_Global_LatticePoisson_coe_dualEquiv
import Theorems.Thm_GroundTheory_Global_LatticePoisson_mFourier_toTorus
import Theorems.Thm_GroundTheory_Global_LatticePoisson_perTorus_toTorus
import Theorems.Thm_GroundTheory_Global_LatticePoisson_mFourierCoeff_perTorus
import Theorems.Thm_GroundTheory_Global_LatticePoisson_summable_mFourierCoeff_perTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
open GroundTheory.Global.LatticePoisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
variable [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Global.LatticePoisson
theorem _root_.solution (f : 𝓢(E, ℂ)) (a : E) :
    HasSum (fun μ : dualLattice L => (ZLattice.covolume L)⁻¹ • (𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫))
      (per L f a) := by
  classical
  let b := Free.chooseBasis ℤ L
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (summable_mFourierCoeff_perTorus b f) (toTorus ((b.ofZLatticeBasis ℝ L).equivFun a))
  rw [perTorus_toTorus, LinearEquiv.symm_apply_apply] at h
  rw [← (dualEquiv b).hasSum_iff]
  convert h using 1
  funext m
  have hin : ⟪dualPt b m, a⟫ = ∑ i, (m i : ℝ) * (b.ofZLatticeBasis ℝ L).equivFun a i := by
    rw [real_inner_comm, ← inner_equivFun_symm_dualPt b, LinearEquiv.symm_apply_apply]
  simp only [Function.comp_apply, coe_dualEquiv, mFourierCoeff_perTorus, mFourier_toTorus, hin,
    smul_eq_mul, smul_mul_assoc]
end GroundTheory.Global.LatticePoisson
