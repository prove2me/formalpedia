-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.exists_primary_prime_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:22:01.526829+00:00
-- url     : https://prove2.me/submissions/092f9aaa-2caa-4e54-a5de-d67e72490785

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Theorems.Thm_OAI_ActualEisensteinCubic_primary_associated_eq
import Theorems.Thm_OAI_ActualEisensteinCubic_primary_multiset_prod
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_exists_primary_generator
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply



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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (t : O) (ht0 : t ≠ 0)
    (ht : lambda ^ 2 ∣ t - 1) :
    ∃ s : Multiset O, s.prod = t ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
  classical
  obtain ⟨f, hf, hft⟩ := UniqueFactorizationMonoid.exists_prime_factors t ht0
  have hfgood : ∀ r ∈ f, lambda ∉ (Ideal.span {r} : Ideal O) := by
    intro r hr
    have hp := hf r hr
    let : (Ideal.span {r} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    apply primary_maximal_divisor_good t ht
    exact Ideal.mem_span_singleton.mpr ((Multiset.dvd_prod hr).trans hft.dvd)
  have hreplace : ∃ s : Multiset O, Associated s.prod f.prod ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
    clear hft
    induction f using Multiset.induction_on with
    | empty => exact ⟨0, Associated.refl _, by simp⟩
    | @cons a f ih =>
      have ha := hf a (Multiset.mem_cons_self _ _)
      let : (Ideal.span {a} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible ha.irreducible
      obtain ⟨r, hrspan, hrprimary, _⟩ := cubicJacobi_exists_primary_generator
        (Ideal.span {a}) (hfgood a (Multiset.mem_cons_self _ _))
      have har : Associated a r := Ideal.span_singleton_eq_span_singleton.mp hrspan
      obtain ⟨s, hsf, hs⟩ := ih
        (fun r hr => hf r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hfgood r (Multiset.mem_cons_of_mem hr))
      refine ⟨r ::ₘ s, ?_, ?_⟩
      · simpa only [Multiset.prod_cons] using har.symm.mul_mul hsf
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ⟨har.prime_iff.mp ha, hrprimary⟩
        · exact hs x hx
  obtain ⟨s, hsf, hs⟩ := hreplace
  refine ⟨s, ?_, hs⟩
  exact primary_associated_eq _ _ (hsf.trans hft)
    (primary_multiset_prod s (fun r hr => (hs r hr).2)) ht
end OAI.ActualEisensteinCubic
