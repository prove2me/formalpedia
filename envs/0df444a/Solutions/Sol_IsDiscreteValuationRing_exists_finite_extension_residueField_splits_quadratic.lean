-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_finite_extension_residueField_splits_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ad319e5c-ce95-5140-9ff1-b2c40c4c63e6

import Theorems.Thm_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_finite_extension_residueField_splits_quadratic

set_option autoImplicit false

noncomputable section

namespace K7Engine

open Polynomial IsLocalRing
open scoped IntermediateField

section FiniteField

variable {k : Type} [Field k] [Fintype k]

theorem dvd_X_pow_card_sq_sub_X (g : k[X]) (hg : g.Monic) (hg2 : g.natDegree = 2)
    (hirr : Irreducible g) : g ∣ X ^ (Fintype.card k ^ 2) - X := by
  classical
  haveI := Fact.mk hirr
  have hg0 : g ≠ 0 := hg.ne_zero
  let pb := AdjoinRoot.powerBasis hg0
  haveI : Module.Finite k (AdjoinRoot g) := Module.Finite.of_basis pb.basis
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite k
  letI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot g) = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), pb.finrank, AdjoinRoot.powerBasis_dim, hg2]
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard, FiniteField.pow_card,
    sub_self]

variable {K : Type} [Field K] [Fintype K] [Algebra k K]

theorem exists_root_quadratic (x : K) (f : k[X]) (hf : f.Monic) (hf2 : f.natDegree = 2)
    (hirr : Irreducible f) (hx : aeval x f = 0) (a b : k) :
    ∃ y : K, y ^ 2 - algebraMap k K a * y + algebraMap k K b = 0 := by
  classical
  set g : k[X] := X ^ 2 - C a * X + C b with hg
  have hgm : g.Monic := by rw [hg]; monicity!
  have hg2 : g.natDegree = 2 := by rw [hg]; compute_degree!
  have hgeval : ∀ y : K, (g.map (algebraMap k K)).eval y =
      y ^ 2 - algebraMap k K a * y + algebraMap k K b := by
    intro y
    simp [hg]
  suffices ∃ y : K, (g.map (algebraMap k K)).IsRoot y by
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by rwa [IsRoot.def, hgeval] at hy⟩
  by_cases hroot : ∃ y : k, g.IsRoot y
  · obtain ⟨y, hy⟩ := hroot
    refine ⟨algebraMap k K y, ?_⟩
    rw [IsRoot.def, eval_map, eval₂_hom, hy.eq_zero, map_zero]
  · push Not at hroot
    have hgirr : Irreducible g := by
      refine (hgm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr ?_
      refine Multiset.eq_zero_of_forall_notMem fun y hy => hroot y ((mem_roots hgm.ne_zero).mp hy)

    set N : ℕ := Fintype.card k ^ 2 with hN
    obtain ⟨h, hh⟩ := dvd_X_pow_card_sq_sub_X g hgm hg2 hgirr
    have hq : 1 < Fintype.card k := Fintype.one_lt_card
    have hN1 : 1 < N := by rw [hN]; nlinarith
    have hXN : (X ^ N - X : k[X]).natDegree = N := FiniteField.X_pow_card_sub_X_natDegree_eq k hN1
    have hXN0 : (X ^ N - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hN1
    have hh0 : h ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hh
      exact hXN0 hh
    have hdeg : h.natDegree = N - 2 := by
      have := congrArg natDegree hh
      rw [hXN, natDegree_mul hgm.ne_zero hh0, hg2] at this
      omega

    have hxint : IsIntegral k x := ⟨f, hf, hx⟩
    have hmin : minpoly k x = f := (minpoly.eq_of_irreducible_of_monic hirr hx hf).symm
    have hfin : Module.finrank k k⟮x⟯ = 2 := by
      rw [IntermediateField.adjoin.finrank hxint, hmin, hf2]
    letI : Fintype k⟮x⟯ := Fintype.ofFinite _
    have hcardE : Fintype.card k⟮x⟯ = N := by
      rw [Module.card_eq_pow_finrank (K := k), hfin]
    let Z : Finset K := Finset.univ.map ⟨((↑) : k⟮x⟯ → K), Subtype.val_injective⟩
    have hZcard : Z.card = N := by
      simp only [Z, Finset.card_map, Finset.card_univ, hcardE]
    have hZroot : ∀ y ∈ Z, y ^ N = y := by
      intro y hy
      obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hy
      have hw := FiniteField.pow_card w
      rw [hcardE] at hw
      have := congrArg ((↑) : k⟮x⟯ → K) hw
      simpa using this

    by_contra hno
    push Not at hno
    have hh0' : h.map (algebraMap k K) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap k K).injective).mpr hh0
    have hsub : Z.val ⊆ (h.map (algebraMap k K)).roots := by
      intro y hy
      have hyZ : y ∈ Z := hy
      rw [mem_roots hh0', IsRoot.def]
      have hprod : (g.map (algebraMap k K)).eval y * (h.map (algebraMap k K)).eval y = 0 := by
        rw [← eval_mul, ← Polynomial.map_mul, ← hh, Polynomial.map_sub, Polynomial.map_pow, map_X,
          eval_sub, eval_pow, eval_X, hZroot y hyZ, sub_self]
      exact (mul_eq_zero.mp hprod).resolve_left (hno y)
    have hle := card_le_degree_of_subset_roots hsub
    rw [hZcard, natDegree_map, hdeg] at hle
    omega

end FiniteField

section Adjoin

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem isLocalRing_adjoinRoot (f : R[X]) (hf : f.Monic)
    (hirr : Irreducible (f.map (residue R))) : IsLocalRing (AdjoinRoot f) := by
  haveI : Fact (Irreducible (f.map (residue R))) := ⟨hirr⟩
  haveI : Module.Finite R (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := inferInstance
  let 𝔑 : Ideal (AdjoinRoot f) := (maximalIdeal R).map (AdjoinRoot.of f)
  have h𝔑 : 𝔑.IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    have hF : IsField (AdjoinRoot (f.map (residue R))) := Field.toIsField _
    exact MulEquiv.isField hF (AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)).toMulEquiv
  refine IsLocalRing.of_unique_max_ideal ⟨𝔑, h𝔑, fun 𝔐 h𝔐 => ?_⟩
  haveI := h𝔐
  have hcomap : (𝔐.comap (algebraMap R (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔐
  have heq : 𝔐.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hcomap
  have hle : 𝔑 ≤ 𝔐 := by
    rw [Ideal.map_le_iff_le_comap, ← AdjoinRoot.algebraMap_eq, heq]
  exact (h𝔑.eq_of_le h𝔐.ne_top hle).symm

end Adjoin

theorem algebraMap_injective_of_charZero
    {𝒪 A : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Finite (ResidueField 𝒪)]
    [CommRing A] [IsDomain A] [CharZero A] [Algebra 𝒪 A] :
    Function.Injective (algebraMap 𝒪 A) := by
  classical
  obtain ⟨q, hqchar⟩ := CharP.exists (ResidueField 𝒪)
  haveI := hqchar
  have hq : q.Prime := CharP.char_is_prime (ResidueField 𝒪) q
  have hqm : (q : 𝒪) ∈ maximalIdeal 𝒪 := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (ResidueField 𝒪) q
  rw [RingHom.injective_iff_ker_eq_bot]
  set 𝔭 := RingHom.ker (algebraMap 𝒪 A) with h𝔭
  haveI h𝔭prime : 𝔭.IsPrime := RingHom.ker_isPrime _
  have hq𝔭 : (q : 𝒪) ∉ 𝔭 := by
    intro h
    rw [h𝔭, RingHom.mem_ker, map_natCast] at h
    exact hq.ne_zero (Nat.cast_eq_zero.mp h)
  by_contra hne
  have hmax : 𝔭 = maximalIdeal 𝒪 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
    have hϖmem : ϖ ∈ 𝔭 := by
      have hpow : ϖ ^ n ∈ 𝔭 := hn ▸ Ideal.mem_span_singleton_self _
      exact h𝔭prime.mem_of_pow_mem n hpow
    apply le_antisymm (IsLocalRing.le_maximalIdeal h𝔭prime.ne_top)
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖmem
  exact hq𝔭 (hmax ▸ hqm)

theorem quad_split {F : Type} [CommRing F] {a b y : F} (hy : y ^ 2 - a * y + b = 0) (z : F) :
    z ^ 2 - a * z + b = (z - y) * (z - (a - y)) := by
  linear_combination hy

theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪] :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    ∀ a b : IsLocalRing.ResidueField 𝒪, ∃ x y : IsLocalRing.ResidueField 𝒪',
      ∀ z : IsLocalRing.ResidueField 𝒪',
        z ^ 2 - IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') a * z + IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') b =
          (z - x) * (z - y) := by
  classical
  set k := ResidueField 𝒪
  letI : Fintype k := Fintype.ofFinite k
  by_cases hall : ∀ a b : k, ∃ y : k, y ^ 2 - a * y + b = 0
  ·
    refine ⟨𝒪, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, Algebra.id 𝒪, inferInstance, ?_, ?_, ?_⟩
    · rw [Algebra.algebraMap_self]; infer_instance
    · exact fun _ _ h => h
    · intro a b
      obtain ⟨y, hy⟩ := hall a b
      refine ⟨y, a - y, fun z => ?_⟩
      obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
      obtain ⟨b₀, rfl⟩ := IsLocalRing.residue_surjective b
      rw [ResidueField.map_residue, ResidueField.map_residue, Algebra.algebraMap_self_apply,
        Algebra.algebraMap_self_apply]
      exact quad_split hy z
  ·
    push Not at hall
    obtain ⟨a, b, hab⟩ := hall
    set fbar : k[X] := X ^ 2 - C a * X + C b with hfbar
    have hfbm : fbar.Monic := by rw [hfbar]; monicity!
    have hfb2 : fbar.natDegree = 2 := by rw [hfbar]; compute_degree!
    have hfbirr : Irreducible fbar := by
      refine (hfbm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr ?_
      refine Multiset.eq_zero_of_forall_notMem fun y hy => hab y ?_
      have := ((mem_roots hfbm.ne_zero).mp hy).eq_zero
      simpa [hfbar] using this
    obtain ⟨a', ha'⟩ := IsLocalRing.residue_surjective a
    obtain ⟨b', hb'⟩ := IsLocalRing.residue_surjective b
    set f : 𝒪[X] := X ^ 2 - C a' * X + C b' with hfdef
    have hfm : f.Monic := by rw [hfdef]; monicity!
    have hf2 : f.natDegree = 2 := by rw [hfdef]; compute_degree!
    have hfmap : f.map (residue 𝒪) = fbar := by
      simp only [hfdef, hfbar, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, map_X,
        Polynomial.map_mul, map_C, ha', hb']
    have hfirr' : Irreducible (f.map (residue 𝒪)) := hfmap ▸ hfbirr
    have hfirr : Irreducible f := hfm.irreducible_of_irreducible_map (residue 𝒪) f hfirr'

    haveI : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hfirr.prime
    haveI : IsLocalRing (AdjoinRoot f) := isLocalRing_adjoinRoot f hfm hfirr'
    haveI : Module.Finite 𝒪 (AdjoinRoot f) :=
      Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
    haveI : Module.Free 𝒪 (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
    haveI : Module.IsTorsionFree 𝒪 (AdjoinRoot f) := inferInstance

    obtain ⟨n, A, _, _, _, _, _, _, _, _, _, χ, hχloc, hker, -⟩ :=
      IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot (𝒪 := 𝒪) (P := AdjoinRoot f)

    have hn : 0 < n := by
      by_contra hn
      obtain rfl : n = 0 := by omega
      have htop : (⨅ i : Fin 0, RingHom.ker (χ i).toRingHom) = ⊤ := iInf_of_empty _
      rw [htop] at hker
      have h1 : (1 : AdjoinRoot f) ∈ (⊥ : Ideal (AdjoinRoot f)) := hker ▸ Submodule.mem_top
      rw [Ideal.mem_bot] at h1
      exact one_ne_zero h1
    let i₀ : Fin n := ⟨0, hn⟩
    haveI := hχloc i₀

    refine ⟨A i₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      algebraMap_injective_of_charZero, ?_⟩

    set k' := ResidueField (A i₀)
    letI : Fintype k' := Fintype.ofFinite k'
    let ι : k →+* k' := ResidueField.map (algebraMap 𝒪 (A i₀))
    letI : Algebra k k' := ι.toAlgebra
    set x : k' := residue (A i₀) (χ i₀ (AdjoinRoot.root f)) with hxdef
    have hx : aeval x fbar = 0 := by
      have h1 : aeval (χ i₀ (AdjoinRoot.root f)) f = 0 := by
        rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
      have h2 : residue (A i₀) (aeval (χ i₀ (AdjoinRoot.root f)) f) = 0 := by rw [h1, map_zero]
      rw [aeval_def, hom_eval₂] at h2
      rw [aeval_def, ← hfmap, eval₂_map]
      convert h2 using 2
      rfl
    intro a₁ b₁
    obtain ⟨y, hy⟩ := exists_root_quadratic x fbar hfbm hfb2 hfbirr hx a₁ b₁
    refine ⟨y, ι a₁ - y, fun z => ?_⟩
    exact quad_split hy z

end K7Engine

end

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪] :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    ∀ a b : IsLocalRing.ResidueField 𝒪, ∃ x y : IsLocalRing.ResidueField 𝒪',
      ∀ z : IsLocalRing.ResidueField 𝒪',
        z ^ 2 - IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') a * z + IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') b =
          (z - x) * (z - y) :=
  K7Engine.main

end S_IsDiscreteValuationRing_exists_finite_extension_residueField_splits_quadratic
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_finite_extension_residueField_splits_quadratic (solution)
