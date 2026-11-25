-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.coeFn_avgVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:51.360881+00:00
-- url     : https://prove2.me/submissions/34638f2e-70e0-4645-ac2e-df03c573ea5e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open GroundTheory.Automorphic.MeasurablePartition
variable (p : MeasurablePartition X)
omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [BorelSpace X]
namespace GroundTheory.Automorphic.MeasurablePartition
theorem _root_.solution (i : p.nonnull μ) :
    p.avgVec μ i =ᵐ[μ] fun y => (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) *
      (p.E i).indicator (fun _ => (1 : ℂ)) y := by
  filter_upwards [Lp.coeFn_smul (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ)
    (indicatorConstLp 2 (p.measurableSet i) (measure_ne_top μ _) (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := p.measurableSet i)
      (hμs := measure_ne_top μ _) (c := (1 : ℂ))] with y h1 h2
  rw [avgVec, h1, Pi.smul_apply, h2, smul_eq_mul]
end GroundTheory.Automorphic.MeasurablePartition
