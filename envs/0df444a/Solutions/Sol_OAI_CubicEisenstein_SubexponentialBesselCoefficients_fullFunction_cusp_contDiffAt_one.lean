-- Prove2me | solution 1 for OAI.CubicEisenstein.SubexponentialBesselCoefficients.fullFunction_cusp_contDiffAt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:05:52.543907+00:00
-- url     : https://prove2.me/submissions/1bb44eb4-8796-4cdd-b327-44c86e073a13

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ArbitraryCuspPullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubeCorrespondence
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConjugateCuspProfiles
import Theorems.Thm_OAI_CubicEisenstein_SubexponentialBesselCoefficients_series_contDiffAt_one
import Theorems.Thm_OAI_CubicEisenstein_SubexponentialBesselCoefficients_fullFunction_cusp_eq


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
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding
open OAI.CubicEisenstein.SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)
namespace OAI.CubicEisenstein.SubexponentialBesselCoefficients
theorem _root_.solution (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hreal : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>q.1^(2/3:ℝ)) p :=
    contDiff_fst.contDiffAt.rpow_const_of_ne hp.ne'
  have hcast := Complex.ofRealCLM.contDiff.contDiffAt.comp p hreal
  have hpow : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>(q.1:ℂ)^(2/3:ℂ)) p := by
    apply hcast.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    have he := Complex.ofReal_cpow (le_of_lt hq) (2/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
    exact he.symm
  have hfull : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p :=
    (contDiffAt_const.mul hpow).add (coeff.series_contDiffAt_one p hp)
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq
end OAI.CubicEisenstein.SubexponentialBesselCoefficients
