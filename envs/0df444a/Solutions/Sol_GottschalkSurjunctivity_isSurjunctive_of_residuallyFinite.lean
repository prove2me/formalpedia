-- Prove2me | solution 1 for GottschalkSurjunctivity.isSurjunctive_of_residuallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:19:08.120992+00:00
-- url     : https://prove2.me/submissions/02f9285a-b478-489c-8b66-0846a31d586e

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

set_option autoImplicit false

namespace GottschalkSurjunctivityAux

open GottschalkSurjunctivity

theorem exists_sep (G : Type) [Group G] (hG : IsResiduallyFinite G) (F : Finset G) :
    ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧
      ∀ f ∈ F, ∀ f' ∈ F, f⁻¹ * f' ∈ N → f = f' := by
  classical
  have hM : ∀ g : G, ∃ M : Subgroup G, M.Normal ∧ M.FiniteIndex ∧ (g ≠ 1 → g ∉ M) := by
    intro g
    by_cases hg : g = 1
    · exact ⟨⊤, inferInstance, inferInstance, fun h => (h hg).elim⟩
    · obtain ⟨N, h1, h2, h3⟩ := hG g hg
      exact ⟨N, h1, h2, fun _ => h3⟩
  choose M hMn hMf hMs using hM
  refine ⟨⨅ p : (F ×ˢ F : Finset (G × G)), M (p.1.1⁻¹ * p.1.2),
    Subgroup.normal_iInf_normal (fun p => hMn _), Subgroup.finiteIndex_iInf (fun p => hMf _), ?_⟩
  intro f hf f' hf' hmem
  by_contra hne
  have hp : (f, f') ∈ F ×ˢ F := Finset.mem_product.2 ⟨hf, hf'⟩
  have h2 := (Subgroup.mem_iInf.1 hmem) ⟨(f, f'), hp⟩
  apply hMs _ _ h2
  intro h1
  exact hne (inv_mul_eq_one.1 h1)

theorem fix_finite (G : Type) [Group G] (A : Type) [Finite A] (N : Subgroup G) [hN : N.Normal]
    [N.FiniteIndex] : Set.Finite {x : G → A | ∀ n ∈ N, shift G n x = x} := by
  classical
  have : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  refine Set.Finite.of_finite_image (f := fun x => fun q : G ⧸ N => x q.out) (Set.toFinite _) ?_
  have key : ∀ z : G → A, z ∈ {x : G → A | ∀ n ∈ N, shift G n x = x} →
      ∀ h : G, z h = z (QuotientGroup.mk h : G ⧸ N).out := by
    intro z hz h
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N h
    rw [hk]
    have hm : h * (k : G) * h⁻¹ ∈ N := hN.conj_mem _ k.2 h
    have e := congrFun (hz _ (N.inv_mem hm)) h
    simp only [shift_apply, inv_inv] at e
    rw [← e]
    congr 1
    group
  intro x hx y hy hxy
  funext h
  rw [key x hx h, key y hy h]
  exact congrFun hxy _

theorem main (G : Type) [Group G] (hG : IsResiduallyFinite G) : IsSurjunctive G := by
  classical
  intro A _ _ _ _ τ hc he hi
  have hclosed : IsClosed (Set.range τ) := (isCompact_range hc).isClosed
  have hdense : ∀ y : G → A, y ∈ closure (Set.range τ) := by
    intro y
    rw [mem_closure_iff_nhds]
    intro s hs
    rw [nhds_pi, Filter.mem_pi'] at hs
    obtain ⟨I, t, ht, hsub⟩ := hs
    obtain ⟨N, hNn, hNf, hsep⟩ := exists_sep G hG I
    let g : G ⧸ N → A := fun q =>
      if h : ∃ f ∈ I, (QuotientGroup.mk f : G ⧸ N) = q then y h.choose else y 1
    let z : G → A := fun h => g (QuotientGroup.mk h)
    have hzI : ∀ f ∈ I, z f = y f := by
      intro f hf
      have hex : ∃ f' ∈ I, (QuotientGroup.mk f' : G ⧸ N) = QuotientGroup.mk f := ⟨f, hf, rfl⟩
      show g (QuotientGroup.mk f) = y f
      simp only [g, dif_pos hex]
      obtain ⟨h1, h2⟩ := hex.choose_spec
      rw [hsep _ h1 f hf (QuotientGroup.eq.1 h2)]
    let S : Set (G → A) := {x : G → A | ∀ n ∈ N, shift G n x = x}
    have hzN : z ∈ S := by
      intro n hn
      funext h
      simp only [shift_apply]
      show g (QuotientGroup.mk (n⁻¹ * h)) = g (QuotientGroup.mk h)
      congr 1
      apply QuotientGroup.eq.2
      have e : (n⁻¹ * h)⁻¹ * h = h⁻¹ * n * h⁻¹⁻¹ := by group
      rw [e]
      exact hNn.conj_mem _ hn _
    have hSf : Set.Finite S := fix_finite G A N
    have : Finite S := hSf.to_subtype
    have hmaps : ∀ x ∈ S, τ x ∈ S := by
      intro x hx n hn
      rw [← he n x, hx n hn]
    let F : S → S := fun x => ⟨τ x.1, hmaps x.1 x.2⟩
    have hFi : Function.Injective F := by
      intro a b hab
      exact Subtype.ext (hi (congrArg Subtype.val hab))
    obtain ⟨⟨x, hxS⟩, hx⟩ := (Finite.injective_iff_surjective.1 hFi) ⟨z, hzN⟩
    have hx' : τ x = z := congrArg Subtype.val hx
    refine ⟨τ x, hsub (fun i hi' => ?_), x, rfl⟩
    rw [hx', hzI i (Finset.mem_coe.1 hi')]
    exact mem_of_mem_nhds (ht i)
  intro y
  have := hdense y
  rw [hclosed.closure_eq] at this
  exact this

end GottschalkSurjunctivityAux

open GottschalkSurjunctivity in
theorem solution (G : Type) [Group G]
    (hG : IsResiduallyFinite G) : IsSurjunctive G := by
  exact GottschalkSurjunctivityAux.main G hG
