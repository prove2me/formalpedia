-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:47.801572+00:00
-- url     : https://prove2.me/submissions/3192063b-e415-4a32-a6cd-599a6b5c119e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V),
        ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  intro S _ u hu
  obtain ⟨m, hm, hum⟩ := Ideal.exists_le_maximal (Ideal.span {u})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hum' : u ∈ m := hum (Ideal.mem_span_singleton_self u)
  haveI := hm.isPrime
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := m) bot_le
  haveI hqp : q.IsPrime := hq.1.1
  let L := AlgebraicClosure (FractionRing (S ⧸ q))
  let g : S →+* L := ((algebraMap (FractionRing (S ⧸ q)) L).comp
    (algebraMap (S ⧸ q) (FractionRing (S ⧸ q)))).comp (Ideal.Quotient.mk q)
  have hg : ∀ s, g s = 0 ↔ s ∈ q := by
    intro s
    simp only [g, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (algebraMap (FractionRing (S ⧸ q)) L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) (FractionRing (S ⧸ q))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hne : m.map g.rangeRestrict ≠ ⊤ := by
    intro h
    have h1 : (1 : g.range) ∈ m.map g.rangeRestrict := h ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ :=
      (Ideal.mem_map_iff_of_surjective _ g.rangeRestrict_surjective).1 h1
    have h2 : g (x - 1) = 0 := by
      have := congrArg Subtype.val hx1
      simp only [RingHom.coe_rangeRestrict, OneMemClass.coe_one] at this
      rw [map_sub, this, map_one, sub_self]
    have h3 : x - 1 ∈ m := hqm ((hg _).1 h2)
    have h4 : (1 : S) ∈ m := by simpa using m.sub_mem hx h3
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h4)
  obtain ⟨V, hV, hV'⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hmem : ∀ s, g s ∈ V := fun s => hV (show g s ∈ g.range from ⟨s, rfl⟩)
  refine ⟨L, inferInstance, inferInstance, V, g.codRestrict V hmem, ?_, ?_⟩
  · have h1 : g u ∈ V.nonunits :=
      hV' ⟨g.rangeRestrict u, Ideal.mem_map_of_mem _ hum', rfl⟩
    have h2 := (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨g u, hmem u⟩)).1 h1
    exact h2
  · intro s hs h0
    have h1 : g s = 0 := congrArg Subtype.val h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq)
      ((hg s).1 h1) hs
end GlobalTheory
