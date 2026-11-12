-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeSource_difference_decay_from_representatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:29:33.062506+00:00
-- url     : https://prove2.me/submissions/52ef56b3-8d5f-4689-9371-0751fac428dc

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Theorems.Thm_OAI_CubicEisenstein_cubeSource_difference_eq_remainders
import Theorems.Thm_OAI_CubicEisenstein_cubePrime_norm_ge_one
import Theorems.Thm_OAI_CubicEisenstein_cubeReducedRemainder_bound
import Theorems.Thm_OAI_CubicEisenstein_cube_normalized_sum_bound
import Theorems.Thm_OAI_CubicEisenstein_sourceCuspRemainder_bound_all


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
open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)‖≤
    (K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹))/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp.ne_zero
  have ha:(‖eisEmbedding p‖^3)⁻¹≤v:=by
    calc
      _≤1:=inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
      _≤v:=hv1
  have hbase:=sourceCuspRemainder_bound_all K _ hrep M z v hv ha
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hsum:=cube_normalized_sum_bound p hp.ne_zero
    (fun r=>cubeReducedRemainder (d r) hp.ne_zero z v hv) (K*‖eisEmbedding p‖^9/v^3)
    (by positivity) (fun r=>cubeReducedRemainder_bound (d r) hp.ne_zero K hK hrep z v hv hv1)
  have hrest:‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [cubeSource_difference_eq_remainders M p hp hprimary z v hv]
  refine (norm_sub_le _ _).trans ?_
  calc
    _≤K*‖eisEmbedding p‖^9/v^3+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=
      add_le_add hsum hrest
    _=_:=by ring
end OAI.CubicEisenstein
