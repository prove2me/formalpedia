-- Prove2me | solution 1 for IsRegularLocalRing.of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f2a0974b-8fa4-57f9-bcf9-6b5603fde4ad

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors

set_option autoImplicit false

open IsLocalRing

namespace RegLift

variable {S : Type*} [CommRing S] [IsLocalRing S]

theorem mk_mem_maximalIdeal {I : Ideal S} (hI : I ≤ maximalIdeal S) [IsLocalRing (S ⧸ I)] {m : S}
    (hm : m ∈ maximalIdeal S) : Ideal.Quotient.mk I m ∈ maximalIdeal (S ⧸ I) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq] at hv
  have h1 : m * w ∈ maximalIdeal S := Ideal.mul_mem_right _ _ hm
  have h2 : (1 : S) = m * w - (m * w - 1) := by ring
  apply (maximalIdeal.isMaximal S).ne_top
  rw [Ideal.eq_top_iff_one, h2]
  exact Ideal.sub_mem _ h1 (hI hv)

theorem mem_maximalIdeal_of_mk_mem {I : Ideal S} [IsLocalRing (S ⧸ I)] {x : S}
    (hx : Ideal.Quotient.mk I x ∈ maximalIdeal (S ⧸ I)) : x ∈ maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun hu => hx (hu.map _)

theorem main [IsNoetherianRing S]
    (ϖ : S) (hϖ : ϖ ∈ maximalIdeal S) (hreg : ϖ ∈ nonZeroDivisors S)
    (hfib : IsRegularLocalRing (S ⧸ Ideal.span {ϖ})) :
    IsRegularLocalRing S ∧ ringKrullDim S = ringKrullDim (S ⧸ Ideal.span {ϖ}) + 1 ∧
      (ringKrullDim (S ⧸ Ideal.span {ϖ}) = 1 → ∃ t : S, maximalIdeal S = Ideal.span {ϖ, t}) := by
  classical
  set I : Ideal S := Ideal.span {ϖ} with hIdef
  have hI : I ≤ maximalIdeal S := by
    rw [hIdef, Ideal.span_le, Set.singleton_subset_iff]; exact hϖ
  haveI : IsLocalRing (S ⧸ I) := hfib.toIsLocalRing
  have hdim : ringKrullDim (S ⧸ I) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hreg hϖ

  have hfg : (maximalIdeal (S ⧸ I)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hscard, hsspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  let σ : S ⧸ I → S := Function.surjInv Ideal.Quotient.mk_surjective
  have hσ : ∀ x, Ideal.Quotient.mk I (σ x) = x := Function.surjInv_eq Ideal.Quotient.mk_surjective
  let T : Finset S := s.image σ
  have hTimg : (Ideal.Quotient.mk I) '' (T : Set S) = (s : Set (S ⧸ I)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      rw [hσ]; exact Finset.mem_coe.2 hy
    · intro hz
      exact ⟨σ z, Finset.mem_coe.2 (Finset.mem_image.2 ⟨z, Finset.mem_coe.1 hz, rfl⟩), hσ z⟩
  have hmax : maximalIdeal S = Ideal.span (insert ϖ (T : Set S)) := by
    apply le_antisymm
    · intro m hm
      have hm' : Ideal.Quotient.mk I m ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (T : Set S)) := by
        rw [Ideal.map_span, hTimg]
        have := mk_mem_maximalIdeal hI hm
        rw [← hsspan] at this
        exact this
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hm'
      obtain ⟨l, hl, hlm⟩ := hm'
      have hml : m - l ∈ I := by rw [← Ideal.Quotient.eq, hlm]
      have : m = (m - l) + l := by ring
      rw [this]
      refine Ideal.add_mem _ ?_ (Ideal.span_mono (Set.subset_insert _ _) hl)
      rw [hIdef] at hml
      exact Ideal.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) hml
    · rw [Ideal.span_le]
      intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hxT
      · exact hϖ
      · apply mem_maximalIdeal_of_mk_mem (I := I)
        rw [← hsspan]
        apply Submodule.subset_span
        rw [← hTimg]
        exact ⟨x, hxT, rfl⟩

  have hTcard : T.card ≤ s.card := Finset.card_image_le
  have hrank : (maximalIdeal S).spanFinrank ≤ s.card + 1 := by
    rw [hmax]
    calc (Ideal.span (insert ϖ (T : Set S))).spanFinrank ≤ (insert ϖ (T : Set S)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)
      _ ≤ (T : Set S).ncard + 1 := Set.ncard_insert_le _ _
      _ = T.card + 1 := by rw [Set.ncard_coe_finset]
      _ ≤ s.card + 1 := by omega
  have hfibdim : ((maximalIdeal (S ⧸ I)).spanFinrank : WithBot ℕ∞) = ringKrullDim (S ⧸ I) :=
    hfib.spanFinrank_maximalIdeal
  have hdimS : ringKrullDim S = ((s.card + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hdim, ← hfibdim, ← hscard]; rfl
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le S ?_, hdim.symm, ?_⟩
  · rw [hdimS]; exact_mod_cast hrank
  · intro h1
    have hs1 : s.card = 1 := by
      have : ((s.card : ℕ) : WithBot ℕ∞) = 1 := by rw [hscard, hfibdim, h1]
      exact_mod_cast this
    obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hs1
    refine ⟨σ y, ?_⟩
    rw [hmax]
    simp only [T, hy, Finset.image_singleton, Finset.coe_singleton]

end RegLift

theorem solution
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (ϖ : S) (hϖ : ϖ ∈ maximalIdeal S) (hreg : ϖ ∈ nonZeroDivisors S)
    (hfib : IsRegularLocalRing (S ⧸ Ideal.span {ϖ})) :
    IsRegularLocalRing S ∧ ringKrullDim S = ringKrullDim (S ⧸ Ideal.span {ϖ}) + 1 ∧
      (ringKrullDim (S ⧸ Ideal.span {ϖ}) = 1 → ∃ t : S, maximalIdeal S = Ideal.span {ϖ, t}) :=
  RegLift.main ϖ hϖ hreg hfib

end S_IsRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors
end P2MW
export P2MW.S_IsRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors (solution)
