-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.setIntegral_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:57.286849+00:00
-- url     : https://prove2.me/submissions/e9414ad0-8385-4be8-b64e-988899745a5e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson

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
omit [DecidableEq ι]
namespace GroundTheory.Global.LatticePoisson
theorem _root_.solution (φ : E → ℂ) :
    ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1}, φ ((b.ofZLatticeBasis ℝ L).equivFun.symm x) =
      (ZLattice.covolume L)⁻¹ • ∫ y in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L), φ y := by
  set b₀ := b.ofZLatticeBasis ℝ L
  set D := ZSpan.fundamentalDomain b₀
  let T : (ι → ℝ) ≃L[ℝ] E := b₀.equivFun.symm.toContinuousLinearEquiv
  have hT : ∀ x, T x = b₀.equivFun.symm x := fun _ => rfl
  set ν := Measure.map T (volume : Measure (ι → ℝ))
  have : ν.IsAddHaarMeasure := T.isAddHaarMeasure_map volume
  have hpre : T ⁻¹' D = {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} := by
    ext x
    have : ∀ i, b₀.repr (b₀.equivFun.symm x) i = x i := fun i => by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [Set.mem_preimage, D, ZSpan.mem_fundamentalDomain, hT, this, Set.mem_ofPred_eq]
  have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet b₀
  have hνD : ν D = 1 := by
    rw [Measure.map_apply T.continuous.measurable hDm, hpre]
    have : {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} =
        Set.pi univ (fun i => Ico ((0 : ι → ℝ) i) ((1 : ι → ℝ) i)) := by ext; simp
    rw [this, Real.volume_pi_Ico]
    simp
  have hcv : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  have hvolD : volume D = ENNReal.ofReal (ZLattice.covolume L) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume), measureReal_def, ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top.ne
  set c := ν.addHaarScalarFactor volume
  have hν : ν = c • volume := Measure.isAddLeftInvariant_eq_smul ν volume
  have hc : (c : ℝ) = (ZLattice.covolume L)⁻¹ := by
    have h1 := hνD
    rw [hν, Measure.smul_apply, hvolD, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hcv.le,
      ENNReal.toReal_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  calc ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1}, φ (b₀.equivFun.symm x)
      = ∫ x in T ⁻¹' D, φ (T x) := by rw [hpre]; rfl
    _ = ∫ y in D, φ y ∂ν := (T.continuous.measurable.measurePreserving volume).setIntegral_preimage_emb
          T.toHomeomorph.measurableEmbedding φ D
    _ = (ZLattice.covolume L)⁻¹ • ∫ y in D, φ y := by
          rw [hν, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, hc]
  rfl
end GroundTheory.Global.LatticePoisson
