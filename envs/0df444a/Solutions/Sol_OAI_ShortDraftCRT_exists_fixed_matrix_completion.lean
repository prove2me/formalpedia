-- Prove2me | solution 1 for OAI.ShortDraftCRT.exists_fixed_matrix_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:27:14.467209+00:00
-- url     : https://prove2.me/submissions/9d13b243-adff-4ba0-b965-a924ec743084

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Theorems.Thm_OAI_ShortDraftCRT_exists_fixed_completion
import Theorems.Thm_OAI_ShortDraftCRT_fixed_completion_matrix_congr

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
open OAI.ShortDraftCRT
open scoped BigOperators Classical Matrix
variable {R : Type*} [CommRing R] [IsDomain R]
namespace OAI.ShortDraftCRT
theorem _root_.solution (M c a0 r0 d0 b0 : R)
    (hc : c≠0) (hdet0 : a0*d0-b0*(c*r0)=1) :
    ∀a r : R, M*c∣a-a0 → M∣r-r0 → IsCoprime r (M*c) → IsCoprime a r →
      ∃b d : R, a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧
        (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) =
          (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  have hbase : c ∣ a0*d0-1 := by
    refine ⟨b0*r0,?_⟩
    linear_combination hdet0
  have hfixed : c ∣ a*d0-1 := by
    have hdiff := dvd_mul_of_dvd_left ((dvd_mul_left c M).trans ha) d0
    convert dvd_add hdiff hbase using 1 ; ring
  obtain ⟨b,d,hdet,hd⟩ := exists_fixed_completion M c r a d0 hfixed hr har
  exact ⟨b,d,hdet,hd,fixed_completion_matrix_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr⟩
end OAI.ShortDraftCRT
