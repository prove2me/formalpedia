-- Prove2me | solution 1 for OAI.CubicEisenstein.breveE_embedding_third_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:18:33.029523+00:00
-- url     : https://prove2.me/submissions/7469ab30-5df8-4743-a9d9-247119a20876

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ArbitraryCuspPullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspDilation
import Theorems.Thm_OAI_CubicEisenstein_ramifiedEmbedding_traceLambda
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_real_trace_of_O
import Theorems.Thm_OAI_CubicEisenstein_embedding_cubicExp
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval


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
open scoped BigOperators Classical
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (A B : ℤ) :
    ShortDraftTrace.breveE (eisEmbedding (ActualEisensteinCoordinates.eval A B)/3)=
      eisEmbedding (cubicExp (2*A-B)) := by
  have htrace : ramifiedTraceLambda=ActualEisensteinCoordinates.eval 1 2 := by
    change 1+2*omega=(1:Eis)+(2:Eis)*omega
    rfl
  have h := breveE_real_trace_of_O (3:ℝ)
    (ActualEisensteinCoordinates.eval A B*ramifiedTraceLambda)
  rw [map_mul,ramifiedEmbedding_traceLambda,mul_div_cancel_right₀ _ eisLam_ne_zero] at h
  rw [htrace,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval] at h
  norm_num only [Complex.ofReal_ofNat] at h
  rw [h,embedding_cubicExp]
  congr 3
  ring_nf
end OAI.CubicEisenstein
