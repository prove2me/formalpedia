-- Prove2me | solution 1 for OAI.CompletedGauss.fractional_cusp_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:44:46.826199+00:00
-- url     : https://prove2.me/submissions/05b3ddb2-27fd-41cc-9e20-086c9845d5cb

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_UnitNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CompletedEnergy
import Theorems.Thm_OAI_CompletedGauss_fractionalThetaPoint_norm_sq
import Theorems.Thm_OAI_CompletedGauss_normalized_cusp_coefficient_nat


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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CompletedDyadic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.CompletedGauss
theorem _root_.solution (d ζ : ℂ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O)
    (hn : n≠0) (hb : b≠0) :
    ζ*(d/((‖fractionalThetaPoint u m n b‖:ℝ):ℂ)) =
      (4/3:ℂ)*(81*ζ)*(normalizedCuspAmplitude d ((m:ℝ)-4) (‖eisEmbedding b‖^2) /
        ((4*ramifiedScale completedRamifiedInitial completedRamifiedStep m*
          ‖eisEmbedding n‖*‖eisEmbedding b‖^2:ℝ):ℂ)) := by
  have hn0 : 0<‖eisEmbedding n‖:=norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hn)
  have hb0 : 0<‖eisEmbedding b‖:=norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hb)
  have hh:=normalized_cusp_coefficient_nat d ζ m (‖eisEmbedding n‖^2) (‖eisEmbedding b‖^2)
    (sq_pos_of_pos hn0) (sq_pos_of_pos hb0)
  rw [←fractionalThetaPoint_norm_sq u m n b,Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hh
  exact hh
end OAI.CompletedGauss
