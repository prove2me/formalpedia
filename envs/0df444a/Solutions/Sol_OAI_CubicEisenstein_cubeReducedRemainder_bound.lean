-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeReducedRemainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:35:22.37126+00:00
-- url     : https://prove2.me/submissions/b637673f-9ac6-438c-9dfb-2b4ee866f8da

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Theorems.Thm_OAI_CubicEisenstein_cubePrime_norm_ge_one
import Theorems.Thm_OAI_CubicEisenstein_cubeCuspTriangular_norm_sq
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
theorem _root_.solution {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeReducedRemainder d hp z v hv‖≤K*‖eisEmbedding p‖^9/v^3 := by
  let D:=‖cubeCuspTriangular d hp 1 1‖^2
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp
  have hd:D≤‖eisEmbedding p‖^3:=by
    rw [show D=‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)) from cubeCuspTriangular_norm_sq d hp]
    rw [←Real.rpow_natCast ‖eisEmbedding p‖ 3]
    apply Real.rpow_le_rpow_of_exponent_le hr1
    norm_num only [Nat.cast_ofNat]
    have hj:0≤(d.exponent.val:ℝ):=Nat.cast_nonneg _
    linarith
  have ha:(‖eisEmbedding p‖^3)⁻¹≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(‖eisEmbedding p‖^3)⁻¹*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (pow_nonneg hr.le 3))
      _=1:=inv_mul_cancel₀ (pow_ne_zero 3 hr.ne')
      _≤v:=hv1
  have hb:=sourceCuspRemainder_bound_all K (‖eisEmbedding p‖^3)⁻¹ hrep
    d.matrix ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/D) (div_pos hv hD) ha
  change ‖cubeReducedRemainder d hp z v hv‖≤K/(v/D)^3 at hb
  refine hb.trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hd 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)
end OAI.CubicEisenstein
