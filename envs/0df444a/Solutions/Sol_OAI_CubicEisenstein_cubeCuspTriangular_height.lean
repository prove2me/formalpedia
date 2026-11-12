-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeCuspTriangular_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:47:08.936341+00:00
-- url     : https://prove2.me/submissions/403973f4-43cc-4393-a549-25c0f435d9bb

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Theorems.Thm_OAI_CubicEisenstein_cubeCuspTriangular_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span


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
open scoped Classical MatrixGroups BigOperators
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution {A:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData A p q) (hp:p≠0) (v:ℝ) (hv:0<v) :
    ((v/‖cubeCuspTriangular d hp 1 1‖^2:ℝ):ℂ)^(2/3:ℂ)=
      (v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  rw [cubeCuspTriangular_norm_sq]
  have hnon:0<‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)):=Real.rpow_pos_of_pos hr _
  have hcast:((2/3:ℝ):ℂ)=(2/3:ℂ):=by norm_num
  rw [←hcast,←Complex.ofReal_cpow (le_of_lt (div_pos hv hnon)),
    ←Complex.ofReal_cpow hv.le]
  unfold cubeCuspHeightWeight
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  rw [←Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [Real.div_rpow hv.le hnon.le,←Real.rpow_mul hr.le]
  have hp2:(‖eisEmbedding p‖^2)^((2*(d.exponent.val:ℝ)-3)/3)=
      ‖eisEmbedding p‖^(((2*(d.exponent.val:ℝ)-3)/3)*2):=by
    rw [←Real.rpow_natCast_mul hr.le 2]
    congr 1
    ring
  rw [hp2,div_eq_mul_inv,←Real.rpow_neg hr.le]
  congr 1
  ring_nf
end OAI.CubicEisenstein
