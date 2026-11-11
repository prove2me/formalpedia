-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.canonicalShortState_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:05:02.351197+00:00
-- url     : https://prove2.me/submissions/89993e82-314f-44e3-b732-bffe9e8b58f4

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_UnitNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CompletedEnergy
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_CanonicalRowCompletion_canonicalLabels_subset_idealRange
import Theorems.Thm_OAI_CanonicalRowCompletion_excludedGenerator_mem
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealGenerator_ne_zero
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalRankMargin_lower
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalRankMass_global


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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.CanonicalRowCompletion
theorem _root_.solution (S : Finset (Ideal ActualEisensteinCubic.O))
    (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/80)
    (hfixed : 2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80)) :
    let G:=Ideal.span {m*excludedGenerator S}
    G≠0 ∧ (∀P∈fixedBadPrimes,P∣G) ∧ labels⊆idealRange F ∧
      X*F≤Z^3 ∧ (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) := by
  have hprod : (∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hSp P hP).ne_zero)
  have he : excludedGenerator S≠0:=idealGenerator_ne_zero _ hprod
  have hG : (Ideal.span {m*excludedGenerator S}:Ideal ActualEisensteinCubic.O)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hstate.mask_ne_zero he)
  have hpG : ∀P∈fixedBadPrimes,P∣Ideal.span {m*excludedGenerator S} := by
    intro P hP
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem S (hbad hP)))
  have hlabels : labels⊆idealRange F:=canonicalLabels_subset_idealRange base (∏P∈S,P) Z η Ψ m labels X F K hstate
    (fun P hP=>Finset.dvd_prod_of_mem (fun Q:Ideal ActualEisensteinCubic.O=>Q) (hbad hP))
  have hmass : X*F≤Z^3:=hstate.mass_le.trans (canonicalRankMass_global Z hZbig _)
  refine ⟨hG,hpG,hlabels,hmass,?_⟩
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hXF : 0≤X*F:=mul_nonneg hstate.column_pos.le (zero_le_one.trans hstate.label_ge_one)
  have hm : (3:ℝ)/80≤canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K) :=
    (by linarith : (3:ℝ)/80≤(1:ℝ)/20-3000*η).trans (canonicalRankMargin_lower _ η hη _)
  have hi : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((3:ℝ)/80)):=
    hstate.invariant.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (neg_le_neg hm)) hXF)
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,map_mul,norm_mul,mul_pow]
  calc
    (2*K)*(‖eisEmbedding m‖^2*‖eisEmbedding (excludedGenerator S)‖^2)=
        (2*‖eisEmbedding (excludedGenerator S)‖^2)*(K*‖eisEmbedding m‖^2):=by ring
    _ ≤ Z^((1:ℝ)/80)*((X*F)*Z^(-((3:ℝ)/80))):=
      mul_le_mul hfixed hi (mul_nonneg (zero_le_one.trans hstate.row_ge_one) (sq_nonneg _)) (by positivity)
    _ = (X*F)*(Z^((1:ℝ)/80)*Z^(-((3:ℝ)/80))):=by ring
    _ = _:=by rw [←Real.rpow_add hZ0]; norm_num
end OAI.CanonicalRowCompletion
