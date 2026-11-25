-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.mFourierCoeff_perTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:49:41.979869+00:00
-- url     : https://prove2.me/submissions/72f43a51-b0e7-4d15-9ee6-297aa47ba949

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Theorems.Thm_GroundTheory_Global_LatticePoisson_inner_equivFun_symm_dualPt
import Theorems.Thm_GroundTheory_Global_LatticePoisson_mFourier_toTorus
import Theorems.Thm_GroundTheory_Global_LatticePoisson_perTorus_toTorus
import Theorems.Thm_GroundTheory_Global_LatticePoisson_integral_fundamentalDomain
import Theorems.Thm_GroundTheory_Global_LatticePoisson_setIntegral_cube

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
theorem _root_.solution (f : 𝓢(E, ℂ)) (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (perTorus b f) m =
      (ZLattice.covolume L)⁻¹ • 𝓕 (f : E → ℂ) (dualPt b m) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ m 0]
  have h1 : ∀ x : ι → ℝ, UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
      perTorus b f (fun i => (x i : UnitAddCircle)) =
      (𝐞 (-⟪(b.ofZLatticeBasis ℝ L).equivFun.symm x, dualPt b m⟫) : ℂ) *
        ∑' ℓ : L, f ((b.ofZLatticeBasis ℝ L).equivFun.symm x + ℓ) := by
    intro x
    rw [show (fun i => (x i : UnitAddCircle)) = toTorus x from rfl, mFourier_toTorus,
      perTorus_toTorus, smul_eq_mul, inner_equivFun_symm_dualPt]
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, per]
  simp_rw [h1]
  have e1 : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      Set.pi univ (fun i => Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i)) := by ext; simp
  have e2 : {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} =
      Set.pi univ (fun i => Ico ((0 : ι → ℝ) i) ((1 : ι → ℝ) i)) := by ext; simp
  have hae : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} := by
    rw [e1, e2]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  rw [setIntegral_congr_set hae,
    setIntegral_cube b (fun y => (𝐞 (-⟪y, dualPt b m⟫) : ℂ) * ∑' ℓ : L, f (y + ℓ)),
    integral_fundamentalDomain b f (dualPt_mem b m)]
end GroundTheory.Global.LatticePoisson
