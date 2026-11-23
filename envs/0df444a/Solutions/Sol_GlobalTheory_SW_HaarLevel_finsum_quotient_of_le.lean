-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.finsum_quotient_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:08.063651+00:00
-- url     : https://prove2.me/submissions/db7bcf26-b0d1-4f2f-b76b-974408f21e37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution {A : Type} [AddCommGroup A] {s t : AddSubgroup A} (h : s ≤ t)
    (hn : s.relIndex t ≠ 0) (φ : A → ℂ) (hφ : ∀ x, ∀ y ∈ t, φ (x + y) = φ x)
    (hf : (Function.support fun q : A ⧸ t => φ q.out).Finite) :
    ∑ᶠ q : A ⧸ s, φ q.out = (s.relIndex t : ℂ) * ∑ᶠ q : A ⧸ t, φ q.out := by
  classical
  set e := AddSubgroup.quotientEquivProdOfLE h
  haveI : Finite (t ⧸ s.addSubgroupOf t) := Nat.finite_of_card_ne_zero hn
  haveI : Fintype (t ⧸ s.addSubgroupOf t) := Fintype.ofFinite _
  have h1 : ∀ q : A ⧸ s, φ q.out = φ (e q).1.out := by
    intro q
    have h2 : (e q).1 = (q.out : A ⧸ t) := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    have h3 : ((e q).1.out : A ⧸ t) = (q.out : A ⧸ t) := by
      rw [QuotientAddGroup.out_eq', h2]
    have := hφ (e q).1.out _ (QuotientAddGroup.eq.1 h3)
    rw [← this]; congr 1; abel
  simp_rw [h1]
  rw [finsum_comp_equiv e (f := fun p => φ p.1.out),
    finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ Finset.univ), finsum_eq_sum _ hf,
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  · intro p hp
    simpa using hp
end GlobalTheory.SW.HaarLevel
