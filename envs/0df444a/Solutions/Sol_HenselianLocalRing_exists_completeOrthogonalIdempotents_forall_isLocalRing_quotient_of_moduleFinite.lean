-- Prove2me | solution 1 for HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/918f8fcd-adcf-5413-937e-00d77c0e387f

import Mathlib
import Theorems.Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite

set_option autoImplicit false

universe u v

section hensSplitHelpers

open IsLocalRing

theorem hensSplit_comap_map_mk {S : Type v} [CommRing S] {K m : Ideal S} (hK : K ≤ m) :
    (m.map (Ideal.Quotient.mk K)).comap (Ideal.Quotient.mk K) = m := by
  rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hK]

theorem hensSplit_isMaximal_map_mk {S : Type v} [CommRing S] {K m : Ideal S} (hm : m.IsMaximal)
    (hK : K ≤ m) : (m.map (Ideal.Quotient.mk K)).IsMaximal := by
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective hm
    with h | h
  · exfalso
    apply hm.ne_top
    rw [← hensSplit_comap_map_mk hK, h, Ideal.comap_top]
  · exact h

theorem hensSplit_map_maximalIdeal_le {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] (m : Ideal S) (hm : m.IsMaximal) :
    (maximalIdeal R).map (algebraMap R S) ≤ m := by
  rw [Ideal.map_le_iff_le_comap]
  haveI := hm
  have hmax : (m.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  rw [IsLocalRing.eq_maximalIdeal hmax]

theorem hensSplit_isArtinianRing_fibre {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  set J : Ideal S := (maximalIdeal R).map (algebraMap R S) with hJ
  let k := R ⧸ maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  have hJR : ∀ r ∈ maximalIdeal R, algebraMap R (S ⧸ J) r = 0 := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ J), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  letI : Algebra k (S ⧸ J) := (Ideal.Quotient.lift _ (algebraMap R (S ⧸ J)) hJR).toAlgebra
  haveI : IsScalarTower R k (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Module.Finite k (S ⧸ J) := Module.Finite.of_restrictScalars_finite R k (S ⧸ J)
  exact IsArtinianRing.of_finite k (S ⧸ J)

theorem hensSplit_finite_maximalSpectrum {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  set J : Ideal S := (maximalIdeal R).map (algebraMap R S) with hJ
  haveI : IsArtinianRing (S ⧸ J) := hensSplit_isArtinianRing_fibre
  let F : MaximalSpectrum S → MaximalSpectrum (S ⧸ J) := fun m =>
    ⟨m.asIdeal.map (Ideal.Quotient.mk J),
      hensSplit_isMaximal_map_mk m.isMaximal (hensSplit_map_maximalIdeal_le (R := R) _ m.isMaximal)⟩
  refine Finite.of_injective F ?_
  intro m₁ m₂ h
  have h2 : (m₁.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) =
      (m₂.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) := by
    have := congrArg MaximalSpectrum.asIdeal h
    simp only [F] at this
    rw [this]
  rw [hensSplit_comap_map_mk (hensSplit_map_maximalIdeal_le (R := R) _ m₁.isMaximal),
    hensSplit_comap_map_mk (hensSplit_map_maximalIdeal_le (R := R) _ m₂.isMaximal)] at h2
  exact MaximalSpectrum.ext h2

theorem hensSplit_isIdempotentElem_eq_zero_or_one {R : Type u} [CommRing R] [IsLocalRing R] {a : R}
    (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · right
    exact h.mul_left_cancel (by rw [mul_one]; exact ha.eq)
  · left
    have : (1 - a) * a = (1 - a) * 0 := by rw [mul_zero, sub_mul, one_mul, ha.eq, sub_self]
    exact h.mul_left_cancel this

theorem hensSplit_isIdempotentElem_eq_of_mk_eq {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) a =
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b) : a = b :=
  (HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
      (Ideal.Quotient.mk _ a) (ha.map _)).unique ⟨ha, rfl⟩ ⟨hb, h.symm⟩

theorem hensSplit_isLocalRing_quotient {S : Type v} [CommRing S] (e : S) (m : Ideal S) (hm : m.IsMaximal)
    (h1 : 1 - e ∈ m) (h2 : ∀ m' : Ideal S, m'.IsMaximal → m' ≠ m → e ∈ m') :
    IsLocalRing (S ⧸ Ideal.span {1 - e}) := by
  apply IsLocalRing.of_unique_max_ideal
  set K : Ideal S := Ideal.span {1 - e} with hKdef
  have hK : K ≤ m := by
    rw [hKdef, Ideal.span_le, Set.singleton_subset_iff]
    exact h1
  refine ⟨m.map (Ideal.Quotient.mk K), hensSplit_isMaximal_map_mk hm hK, ?_⟩
  intro N hN
  have hNc : (N.comap (Ideal.Quotient.mk K)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have heq : N.comap (Ideal.Quotient.mk K) = m := by
    by_contra hne
    have he : e ∈ N.comap (Ideal.Quotient.mk K) := h2 _ hNc hne
    have hKmem : 1 - e ∈ K := Ideal.subset_span (Set.mem_singleton _)
    have h1e : 1 - e ∈ N.comap (Ideal.Quotient.mk K) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hKmem]
      exact N.zero_mem
    have : (1 : S) ∈ N.comap (Ideal.Quotient.mk K) := by
      have := add_mem h1e he
      rwa [sub_add_cancel] at this
    exact hNc.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  rw [← heq, Ideal.map_comap_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective]

end hensSplitHelpers

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (_ : Fintype (MaximalSpectrum S)) (e : MaximalSpectrum S → S),
      CompleteOrthogonalIdempotents e ∧
      (∀ m : MaximalSpectrum S, e m ∉ m.asIdeal) ∧
      (∀ m m' : MaximalSpectrum S, m ≠ m' → e m ∈ m'.asIdeal) ∧
      (∀ m : MaximalSpectrum S, IsLocalRing (S ⧸ Ideal.span {1 - e m})) := by
  classical
  haveI : Finite (MaximalSpectrum S) := hensSplit_finite_maximalSpectrum (R := R)
  letI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  haveI : IsArtinianRing (S ⧸ J) := hensSplit_isArtinianRing_fibre
  have hJle : ∀ m : MaximalSpectrum S, J ≤ m.asIdeal := fun m =>
    hensSplit_map_maximalIdeal_le (R := R) m.asIdeal m.isMaximal

  let P : MaximalSpectrum S → Type v := fun m => S ⧸ m.asIdeal
  let π : S →+* (∀ m, P m) := RingHom.pi fun m => Ideal.Quotient.mk m.asIdeal
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum S => m.asIdeal) := by
    intro m m' h
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne m.isMaximal m'.isMaximal
      (fun h' => h (MaximalSpectrum.ext h'))
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop x
    exact ⟨r, funext hr⟩
  have hJπ : ∀ s ∈ J, π s = 0 := by
    intro s hs
    funext m
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJle m hs)
  let ψ : S ⧸ J →+* (∀ m, P m) := Ideal.Quotient.lift J π hJπ
  have hψmk : ∀ s, ψ (Ideal.Quotient.mk J s) = π s := fun s => Ideal.Quotient.lift_mk J π hJπ
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨s, hs⟩ := hπ x
    exact ⟨Ideal.Quotient.mk J s, by rw [hψmk, hs]⟩

  have hnil : ∀ x ∈ RingHom.ker ψ, IsNilpotent x := by
    intro x hx
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hs : ∀ m : MaximalSpectrum S, s ∈ m.asIdeal := by
      intro m
      have h0 : π s = 0 := by rw [← hψmk]; exact hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h0 m)
    have hmem : Ideal.Quotient.mk J s ∈ Ideal.jacobson (⊥ : Ideal (S ⧸ J)) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro N ⟨-, hN⟩
      haveI := hN
      have hNc : (N.comap (Ideal.Quotient.mk J)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      exact hs ⟨_, hNc⟩
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hmem n
    rw [hn] at this
    simpa using this

  have hf : CompleteOrthogonalIdempotents fun m : MaximalSpectrum S => (Pi.single m 1 : ∀ m, P m) :=
    CompleteOrthogonalIdempotents.single P
  obtain ⟨ē, hē, hēf⟩ :=
    CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker ψ hnil hf (fun m => hψ _)

  have hex := fun m : MaximalSpectrum S =>
    (HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite (ē m) (hē.idem m)).exists
  choose e he hemk using hex
  have hπe : ∀ m m' : MaximalSpectrum S,
      Ideal.Quotient.mk m'.asIdeal (e m) = (Pi.single m 1 : ∀ m, P m) m' := by
    intro m m'
    have h1 : π (e m) = Pi.single m 1 := by
      rw [← hψmk, hemk]
      exact congrFun hēf m
    exact congrFun h1 m'
  have hnotMem : ∀ m : MaximalSpectrum S, e m ∉ m.asIdeal := by
    intro m hm
    have h1 := hπe m m
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, Pi.single_eq_same] at h1
    exact m.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp h1)
  have hmem : ∀ m m' : MaximalSpectrum S, m ≠ m' → e m ∈ m'.asIdeal := by
    intro m m' h
    have h1 := hπe m m'
    rw [Pi.single_eq_of_ne (Ne.symm h)] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, ?_⟩
    intro m m' h
    refine hensSplit_isIdempotentElem_eq_of_mk_eq (R := R) ((he m).mul (he m'))
      (IsIdempotentElem.zero) ?_
    rw [map_mul, map_zero, hemk, hemk]
    exact hē.ortho h
  have hcomplete : ∑ m, e m = 1 := by
    refine hensSplit_isIdempotentElem_eq_of_mk_eq (R := R) hortho.isIdempotentElem_sum
      (IsIdempotentElem.one) ?_
    rw [map_sum, map_one]
    simp_rw [hemk]
    exact hē.complete
  refine ⟨inferInstance, e, ⟨hortho, hcomplete⟩, hnotMem, hmem, ?_⟩

  intro m
  refine hensSplit_isLocalRing_quotient (e m) m.asIdeal m.isMaximal ?_ ?_
  · have h1 := hπe m m
    rw [Pi.single_eq_same] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, h1, sub_self]
  · intro m' hm' hne
    exact hmem m ⟨m', hm'⟩ (fun h => hne (congrArg MaximalSpectrum.asIdeal h).symm)

end S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
end P2MW
export P2MW.S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite (solution)
