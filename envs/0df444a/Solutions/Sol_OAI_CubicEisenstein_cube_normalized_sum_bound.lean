-- Prove2me | solution 1 for OAI.CubicEisenstein.cube_normalized_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:06:51.694804+00:00
-- url     : https://prove2.me/submissions/621f1219-2ce5-48d2-bdb2-79a2420e8306

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span


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
theorem _root_.solution (p:Eis) (hp:p≠0)
    (f:(Eis⧸Ideal.span {p^3})→ℂ) (B:ℝ) (_hB:0≤B) (hf:∀r,‖f r‖≤B) :
    ‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*(∑' r,f r)‖≤B := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℝ)≠0:=by exact_mod_cast hqN
  have hs:‖∑' r,f r‖≤(Ideal.absNorm (Ideal.span {p}):ℝ)^3*B:=by
    calc
      _≤∑' r,‖f r‖:=norm_tsum_le_tsum_norm (Summable.of_finite)
      _≤∑' (_:Eis⧸Ideal.span {p^3}),B:=(Summable.of_finite).tsum_le_tsum hf Summable.of_finite
      _=_:=by
        rw [tsum_const,nsmul_eq_mul]
        change (Ideal.absNorm (Ideal.span {p^3}):ℝ)*B=_
        rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  rw [norm_mul,norm_pow,norm_inv,Complex.norm_natCast]
  calc
    _≤(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹^3*((Ideal.absNorm (Ideal.span {p}):ℝ)^3*B):=
      mul_le_mul_of_nonneg_left hs (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3)
    _=B:=by field_simp
end OAI.CubicEisenstein
