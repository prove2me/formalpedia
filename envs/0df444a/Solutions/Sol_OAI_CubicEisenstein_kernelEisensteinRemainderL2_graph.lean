-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelEisensteinRemainderL2_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:16:31.510395+00:00
-- url     : https://prove2.me/submissions/8dd008ce-4305-45ac-92c6-b659f9b7d6b2

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Theorems.Thm_OAI_CubicEisenstein_kernelEisensteinRemainder_operator_equation
import Theorems.Thm_OAI_CubicEisenstein_kernel_bounded_smooth_operator_graph
import Theorems.Thm_OAI_CubicEisenstein_eisensteinRemainderBound_nonneg
import Theorems.Thm_OAI_CubicEisenstein_eisenstein_sub_seed_bounded
import Theorems.Thm_OAI_CubicEisenstein_kernelEisensteinRemainder_scaled_fderiv_bound
import Theorems.Thm_OAI_CubicEisenstein_kernelEisensteinRemainder_smooth
import Theorems.Thm_OAI_CubicEisenstein_kernel_eisenstein_sub_seed_memLp


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    (kernelEisensteinRemainderL2 a b ha hab s hs,
      kernelL2Defect a b (by linarith) hab s+kernelEisensteinSpectralParameter s •
        kernelEisensteinRemainderL2 a b ha hab s hs)∈kernelEnergyLaplacian.graph := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  let A : KernelQuotient→ℂ := fun q => kernelQuotientDefect a b s q+
    kernelEisensteinSpectralParameter s*f q
  have hD := kernelQuotientDefect_memLp a b s (by linarith) hab
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    hD.add (hfL.const_smul (kernelEisensteinSpectralParameter s))
  have hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p) := by
    intro p hp
    exact kernelEisensteinRemainder_operator_equation a b ha hab s (by linarith) p hp
  have hgraph := kernel_bounded_smooth_operator_graph f hf hfL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad A hA hEq
  have hAL : hA.toLp A=kernelL2Defect a b (by linarith) hab s+
      kernelEisensteinSpectralParameter s • kernelEisensteinRemainderL2 a b ha hab s hs := by
    exact (hD.toLp_add (hfL.const_smul (kernelEisensteinSpectralParameter s))).trans
      (congrArg (fun x => hD.toLp (kernelQuotientDefect a b s)+x)
        (hfL.toLp_const_smul (kernelEisensteinSpectralParameter s)))
  rw [hAL] at hgraph
  exact hgraph
end OAI.CubicEisenstein
