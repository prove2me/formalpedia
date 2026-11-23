-- Prove2me | solution 1 for GlobalTheory.average_fundamentalDomain_eq_cube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:46.044788+00:00
-- url     : https://prove2.me/submissions/6388d305-7de1-4f9e-b565-e8da95537ca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional

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
omit [InnerProductSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → V) :
    (μ.real (ZSpan.fundamentalDomain b))⁻¹ • ∫ y in ZSpan.fundamentalDomain b, g y ∂μ =
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1}, g (b.equivFun.symm x) := by
  set T := b.equivFunL.symm with hT
  have hae : T ⁻¹' ZSpan.fundamentalDomain b =ᵐ[volume] {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} := by
    have h1 : T ⁻¹' ZSpan.fundamentalDomain b = Set.pi univ fun _ ↦ Ico (0 : ℝ) 1 := by
      ext x
      have : ∀ i, b.repr (T x) i = x i := fun i ↦ congrFun (b.equivFun.apply_symm_apply x) i
      simp only [mem_preimage, ZSpan.mem_fundamentalDomain, this, mem_univ_pi]
    have h2 : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ ↦ Ioc (0 : ℝ) 1 := by
      ext x; simp
    rw [h1, h2]
    exact Measure.univ_pi_Ico_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hμ := Measure.isAddLeftInvariant_eq_smul (Measure.map T volume) μ
  set c := Measure.addHaarScalarFactor (Measure.map T volume) μ
  have hone : (Measure.map T volume).real (ZSpan.fundamentalDomain b) = 1 := by
    rw [measureReal_def, hemb.map_apply, measure_congr hae]
    have h2 : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ ↦ Ioc (0 : ℝ) 1 := by
      ext x; simp
    rw [h2, Real.volume_pi_Ioc]
    simp
  have hint := hemb.setIntegral_map (μ := volume) g (ZSpan.fundamentalDomain b)
  rw [setIntegral_congr_set hae] at hint
  rw [hμ, measureReal_nnreal_smul_apply] at hone
  rw [hμ, Measure.restrict_smul, integral_smul_nnreal_measure] at hint
  rw [← eq_inv_of_mul_eq_one_left hone]
  exact hint
end GlobalTheory
