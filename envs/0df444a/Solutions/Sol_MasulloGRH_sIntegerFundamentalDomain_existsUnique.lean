-- Prove2me | solution 1 for MasulloGRH.sIntegerFundamentalDomain_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:49:49.602431+00:00
-- url     : https://prove2.me/submissions/dec543d7-e5c5-4ece-bb87-9bf313d070dc

import Mathlib
import Definitions.Def_MasulloGRH_SIntegerFundamentalDomain
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_cover
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_disjoint

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_sIntegerFundamentalDomain_existsUnique

open MasulloGRH RiemannMasullo
open scoped NumberField.AdeleRing Pointwise

variable {F : Type*} [Field F] [NumberField F]

open Classical in
/-- The finite part of the extension by zero of an `S`-adele. -/
noncomputable def extendFin (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf) :
    FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mk (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
    (fun v => if h : v ∈ Sf then x.2 ⟨v, h⟩ else 0) (by
      refine Filter.eventually_cofinite.mpr (Sf.finite_toSet.subset fun v hv => ?_)
      by_contra h
      have h' : v ∉ Sf := h
      refine hv ?_
      simp only [dif_neg h']
      exact zero_mem _)

/-- Extension by zero of an `S`-adele to a full adele: the components at the finite places
outside `S` are set to `0`. -/
noncomputable def extend (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf) : 𝔸[F] :=
  Prod.mk (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F) x.1 (extendFin Sf x)

lemma extend_fst (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf) :
    (extend Sf x).1 = x.1 := rfl

open Classical in
lemma extend_snd_of_mem (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf)
    {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ Sf) : (extend Sf x).2 v = x.2 ⟨v, h⟩ := by
  change (if h : v ∈ Sf then x.2 ⟨v, h⟩ else (0 : v.adicCompletion F)) = _
  rw [dif_pos h]

open Classical in
lemma extend_snd_of_notMem (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf)
    {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ Sf) : (extend Sf x).2 v = 0 := by
  change (if h : v ∈ Sf then x.2 ⟨v, h⟩ else (0 : v.adicCompletion F)) = _
  rw [dif_neg h]

/-- Membership in the subring of adeles that are integral at every finite place. -/
lemma mem_integralAdelesOutside_empty (a : 𝔸[F]) :
    a ∈ integralAdelesOutside F ∅ ↔
      ∀ v : HeightOneSpectrum (𝓞 F), a.2 v ∈ v.adicCompletionIntegers F := by
  unfold integralAdelesOutside
  simp only [Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true, forall_true_left,
    Subring.mem_comap]
  rfl

/-- The components of the difference of an adele and a principal adele. -/
lemma sub_algebraMap_snd (a : 𝔸[F]) (ξ : F) (v : HeightOneSpectrum (𝓞 F)) :
    (a - algebraMap F 𝔸[F] ξ).2 v = a.2 v - (ξ : v.adicCompletion F) := rfl

lemma sDiagonal_snd (Sf : Finset (HeightOneSpectrum (𝓞 F))) (ξ : F) (v : Sf) :
    (sDiagonal Sf ξ).2 v = ((ξ : F) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) := rfl

lemma sDiagonal_fst (Sf : Finset (HeightOneSpectrum (𝓞 F))) (ξ : F) :
    (sDiagonal Sf ξ).1 = (algebraMap F 𝔸[F] ξ).1 := rfl

/-- The key translation: `ξ` is an `S`-integer with `x - ξ ∈ D_{F,S}` if and only if the
extension by zero of `x`, translated by `-ξ`, lies in the full adelic fundamental domain. -/
lemma key {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F)) (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (x : SAdeleRing F Sf) (ξ : F) :
    (ξ ∈ SIntegers (F := F) Sf ∧ x - sDiagonal Sf ξ ∈ sIntegerFundamentalDomain F b Sf) ↔
      extend Sf x - algebraMap F 𝔸[F] ξ ∈ adeleFundamentalDomain F b := by
  have hint : ∀ v : HeightOneSpectrum (𝓞 F),
      ((ξ : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔ v.valuation F ξ ≤ 1 := by
    intro v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  constructor
  · rintro ⟨hξ, hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    rw [mem_integralAdelesOutside_empty]
    intro v
    rw [sub_algebraMap_snd]
    by_cases hv : v ∈ Sf
    · rw [extend_snd_of_mem Sf x hv]
      exact hx2 ⟨v, hv⟩
    · rw [extend_snd_of_notMem Sf x hv, zero_sub]
      exact neg_mem ((hint v).2 (hξ v (by simpa using hv)))
  · rintro ⟨h1, h2⟩
    rw [mem_integralAdelesOutside_empty] at h2
    refine ⟨?_, h1, ?_⟩
    · intro v hv
      have hv' : v ∉ Sf := by simpa using hv
      have := h2 v
      rw [sub_algebraMap_snd, extend_snd_of_notMem Sf x hv', zero_sub] at this
      exact (hint v).1 (by simpa using neg_mem this)
    · intro v
      have := h2 v
      rw [sub_algebraMap_snd, extend_snd_of_mem Sf x v.2] at this
      exact this

end Sol_MasulloGRH_sIntegerFundamentalDomain_existsUnique

open MasulloGRH RiemannMasullo Sol_MasulloGRH_sIntegerFundamentalDomain_existsUnique in
open scoped NumberField.AdeleRing Pointwise in
theorem solution
    (F : Type*) [Field F] [NumberField F] {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf) :
    ∃! ξ : F, ξ ∈ SIntegers (F := F) Sf ∧
      x - sDiagonal Sf ξ ∈ sIntegerFundamentalDomain F b Sf := by
  simp only [key b Sf x]
  -- existence: the translates of the full adelic fundamental domain cover the adele ring
  have hcov : extend Sf x ∈ ⋃ ξ : F, algebraMap F 𝔸[F] ξ +ᵥ adeleFundamentalDomain F b := by
    rw [adeleFundamentalDomain_cover F b]
    exact Set.mem_univ _
  obtain ⟨ξ, hξ⟩ := Set.mem_iUnion.1 hcov
  obtain ⟨y, hy, hya⟩ := Set.mem_vadd_set.1 hξ
  rw [vadd_eq_add] at hya
  have hy' : extend Sf x - algebraMap F 𝔸[F] ξ = y := by
    rw [← hya, add_sub_cancel_left]
  refine ⟨ξ, by change _ ∈ _; rw [hy']; exact hy, ?_⟩
  -- uniqueness: distinct translates of the full adelic fundamental domain are disjoint
  intro η hη
  change _ ∈ _ at hη
  by_contra hne
  have hne' : ξ - η ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hdisj := adeleFundamentalDomain_disjoint F b (ξ - η) hne'
  refine Set.disjoint_left.1 hdisj ?_ hη
  refine Set.mem_vadd_set.2 ⟨y, hy, ?_⟩
  rw [vadd_eq_add, ← hy', map_sub]
  ring
