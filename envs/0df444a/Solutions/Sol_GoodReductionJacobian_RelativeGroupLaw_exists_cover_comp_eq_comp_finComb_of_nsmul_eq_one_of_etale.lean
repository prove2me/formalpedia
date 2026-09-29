-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/128d469e-797f-54c8-87f1-b802d798bec5

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace Exhaust

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

noncomputable def compHom {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := L.pointGroup t; letI := L.pointGroup t'; SchemeHomOver t f →* SchemeHomOver t' f :=
  letI := L.pointGroup t; letI := L.pointGroup t'
  { toFun := schemeHomOverComp ψ hψ
    map_one' := L.one_natural t t' ψ hψ
    map_mul' := fun x y => L.mul_natural t t' ψ hψ x y }

theorem nsmul_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = (letI := L.pointGroup t; x ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]; rfl

theorem nsmul_finComb_eq_one (hc : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    {m : ℕ} (x : Fin m → SchemeHomOver t f) (hx : ∀ i, L.nsmul t n (x i) = L.one t) (c : Fin m → ℕ) :
    L.nsmul t n (L.finComb t x c) = L.one t := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun a b => hc t a b }
  rw [nsmul_eq_pow]
  show (List.ofFn fun i => x i ^ c i).prod ^ n = 1
  have hmem : (List.ofFn fun i => x i ^ c i).prod ∈ MonoidHom.mker (powMonoidHom n : SchemeHomOver t f →* _) := by
    apply Submonoid.list_prod_mem
    rw [List.forall_mem_ofFn_iff]
    intro i
    rw [MonoidHom.mem_mker, powMonoidHom_apply, ← pow_mul, mul_comm, pow_mul]
    have : x i ^ n = 1 := by rw [← nsmul_eq_pow]; exact hx i
    rw [this, one_pow]
  rwa [MonoidHom.mem_mker, powMonoidHom_apply] at hmem

theorem range_specMap_eq_singleton {R : Type} [CommRing R] {k : Type} [Field k] (sk : R →+* k)
    (s : Spec (CommRingCat.of R)) (hk : RingHom.ker sk = s.asIdeal) :
    Set.range (Spec.map (CommRingCat.ofHom sk)).base = {s} := by
  have hpt : ∀ x : Spec (CommRingCat.of k), (Spec.map (CommRingCat.ofHom sk)).base x = s := by
    intro x
    apply PrimeSpectrum.ext
    have hx : x.asIdeal = ⊥ := by
      haveI : Subsingleton (PrimeSpectrum k) := inferInstance
      have : x = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
      rw [this]; rfl
    show Ideal.comap sk x.asIdeal = s.asIdeal
    rw [hx, ← RingHom.ker_eq_comap_bot, hk]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩; exact hpt x
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨(default : PrimeSpectrum k)⟩
    exact ⟨x, hy ▸ hpt x⟩

theorem exists_geomPoint {R : Type} [CommRing R] (s : Spec (CommRingCat.of R)) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (sk : R →+* k), RingHom.ker sk = s.asIdeal := by
  let D := R ⧸ s.asIdeal
  let K := FractionRing D
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance,
    (algebraMap K (AlgebraicClosure K)).comp ((algebraMap D K).comp (Ideal.Quotient.mk s.asIdeal)), ?_⟩
  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_comap, ← Ideal.comap_comap,
    Ideal.comap_bot_of_injective _ (algebraMap K (AlgebraicClosure K)).injective,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective D K), ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem not_mem_specMap_away {R : Type} [CommRing R] (r : R) (x : Spec (CommRingCat.of (Localization.Away r))) :
    r ∉ ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base x).asIdeal := by
  show r ∉ Ideal.comap (algebraMap R (Localization.Away r)) x.asIdeal
  intro h
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit r))

theorem exists_finset_span_eq_top {R : Type} [CommRing R] (rr : PrimeSpectrum R → R) (hrr : ∀ p, rr p ∉ p.asIdeal) :
    ∃ T : Finset R, (↑T : Set R) ⊆ Set.range rr ∧ Ideal.span (↑T : Set R) = ⊤ := by
  classical
  have htop : Ideal.span (Set.range rr) = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    exact hrr ⟨M, hM.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have h1 : (1 : R) ∈ Ideal.span (Set.range rr) := by rw [htop]; trivial
  obtain ⟨T, hT, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  exact ⟨T, hT, (Ideal.eq_top_iff_one _).2 h1T⟩

end Exhaust

open Exhaust in
theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (n : ℕ)

    (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B]
    (ι : Spec (CommRingCat.of B) ⟶ A) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (hιc : IsClosedImmersion ι)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)

    (S' : Type) [CommRing S'] [Algebra S S'] {m : ℕ}
    (P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) f)
    (hP : ∀ i, L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap S S'))) n (P i) =
      L.one (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hspan : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
      (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) f),
      L.nsmul (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) n Q =
        L.one (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) →
      ∃ c : Fin m → Fin n,
        Spec.map (CommRingCat.ofHom sk) ≫
          (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 = Q.1)

    (R : Type) [CommRing R] [Algebra S' R]
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) f)
    (hy : L.nsmul (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) n y =
      L.one (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S'))))) :
    ∃ (M : ℕ) (r : Fin M → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ c : Fin m → Fin n,
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ y.1 =
        Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away (r j))).comp (algebraMap S' R))) ≫
          (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 := by
  classical

  have htR : Spec.map (CommRingCat.ofHom (algebraMap S' R)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) =
      Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S'))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]

  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap S B))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr ‹Algebra.Etale S B›)
  haveI : Mono ι := inferInstance
  let tR := Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))
  let πB := Spec.map (CommRingCat.ofHom (algebraMap S B))
  let p := pullback.snd πB tR
  haveI : FormallyUnramified p := inferInstance
  haveI : LocallyOfFiniteType p := inferInstance
  haveI : IsSeparated p := inferInstance

  obtain ⟨zy, hzy⟩ := (hιn _ tR y).mp hy
  have hzyB : zy ≫ πB = 𝟙 _ ≫ tR := by
    show zy ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) = 𝟙 _ ≫ tR
    rw [← hι, ← Category.assoc, hzy, y.2, Category.id_comp]
  let σy : Spec (CommRingCat.of R) ⟶ pullback πB tR := pullback.lift zy (𝟙 _) hzyB
  have hσy : σy ≫ p = 𝟙 _ := pullback.lift_snd _ _ _

  let Q : (Fin m → Fin n) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) f :=
    fun c => L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))
  have hQ : ∀ c, L.nsmul _ n (Q c) = L.one _ := fun c =>
    nsmul_finComb_eq_one L hc _ n P hP _
  have hQR : ∀ c, L.nsmul tR n (schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap S' R))) htR (Q c)) = L.one tR := by
    intro c
    rw [← L.nsmul_natural _ _ _ htR, hQ, L.one_natural]
  have hz : ∀ c, ∃ zc : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of B),
      zc ≫ ι = Spec.map (CommRingCat.ofHom (algebraMap S' R)) ≫ (Q c).1 := fun c => (hιn _ tR _).mp (hQR c)
  choose zc hzc using hz
  have hzcB : ∀ c, zc c ≫ πB = 𝟙 _ ≫ tR := by
    intro c
    show zc c ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) = 𝟙 _ ≫ tR
    rw [← hι, ← Category.assoc, hzc, Category.assoc, (Q c).2, htR, Category.id_comp]
  let σc : (Fin m → Fin n) → (Spec (CommRingCat.of R) ⟶ pullback πB tR) := fun c => pullback.lift (zc c) (𝟙 _) (hzcB c)
  have hσc : ∀ c, σc c ≫ p = 𝟙 _ := fun c => pullback.lift_snd _ _ _

  have key := fun c => AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated p σy (σc c) hσy (hσc c)
  let U : (Fin m → Fin n) → (Spec (CommRingCat.of R)).Opens :=
    fun c => (pullback.lift σy (σc c) (hσy.trans (hσc c).symm)) ⁻¹ᵁ (pullback.diagonal p).opensRange

  have bridge : ∀ c {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of R)),
      Set.range g.base ⊆ (U c : Set _) ↔ g ≫ y.1 = g ≫ Spec.map (CommRingCat.ofHom (algebraMap S' R)) ≫ (Q c).1 := by
    intro c T g
    rw [(key c).2 g]
    have e1 : σy ≫ pullback.fst πB tR ≫ ι = y.1 := by rw [← Category.assoc, pullback.lift_fst, hzy]
    have e2 : σc c ≫ pullback.fst πB tR ≫ ι = Spec.map (CommRingCat.ofHom (algebraMap S' R)) ≫ (Q c).1 := by
      rw [← Category.assoc, pullback.lift_fst, hzc]
    constructor
    · intro h
      rw [← e1, ← e2, ← Category.assoc, h, Category.assoc]
    · intro h
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, ← cancel_mono ι, Category.assoc,
          Category.assoc, hzy, hzc]
        exact h
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]

  have cover : ∀ 𝔭 : Spec (CommRingCat.of R), ∃ c, 𝔭 ∈ (U c : Set _) := by
    intro 𝔭
    obtain ⟨k, _, _, sk, hk⟩ := exists_geomPoint 𝔭
    have hg : Spec.map (CommRingCat.ofHom sk) ≫ tR =
        Spec.map (CommRingCat.ofHom ((sk.comp (algebraMap S' R)).comp (algebraMap S S'))) := by
      show Spec.map (CommRingCat.ofHom sk) ≫ Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S'))) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]
    have hQy : L.nsmul _ n (schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) hg y) = L.one _ := by
      rw [← L.nsmul_natural _ _ _ hg, hy, L.one_natural]
    obtain ⟨c, hcq⟩ := hspan k (sk.comp (algebraMap S' R)) (schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) hg y) hQy
    refine ⟨c, ?_⟩
    have hsub : Set.range (Spec.map (CommRingCat.ofHom sk)).base ⊆ (U c : Set _) := by
      rw [bridge c]
      have e : (schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) hg y).1 = Spec.map (CommRingCat.ofHom sk) ≫ y.1 := rfl
      rw [← e, ← hcq, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [range_specMap_eq_singleton sk 𝔭 hk, Set.singleton_subset_iff] at hsub
    exact hsub

  have hbasic : ∀ 𝔭 : Spec (CommRingCat.of R), ∃ (c : Fin m → Fin n) (r : R),
      r ∉ 𝔭.asIdeal ∧ ∀ x : Spec (CommRingCat.of R), r ∉ x.asIdeal → x ∈ (U c : Set (Spec (CommRingCat.of R))) := by
    intro 𝔭
    obtain ⟨c, hc𝔭⟩ := cover 𝔭
    obtain ⟨V, ⟨r, rfl⟩, hV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hc𝔭
    exact ⟨c, r, hV, fun x hx => hVU hx⟩
  choose cp rp hrp hrpU using hbasic
  have hrr : ∀ 𝔭 : PrimeSpectrum R, rp 𝔭 ∉ 𝔭.asIdeal := fun 𝔭 => hrp 𝔭
  obtain ⟨T, hT, hTtop⟩ := exists_finset_span_eq_top rp hrr

  have hpre : ∀ j : Fin T.card, ∃ 𝔭, rp 𝔭 = (T.equivFin.symm j).1 := fun j => hT (T.equivFin.symm j).2
  choose pj hpj using hpre
  refine ⟨T.card, fun j => (T.equivFin.symm j).1, ?_, fun j => ⟨cp (pj j), ?_⟩⟩
  ·
    have : Set.range (fun j : Fin T.card => (T.equivFin.symm j).1) = (↑T : Set R) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩; exact (T.equivFin.symm j).2
      · intro hx; exact ⟨T.equivFin ⟨x, hx⟩, by simp⟩
    rw [this, hTtop]
  ·
    have hsub : Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (T.equivFin.symm j).1)))).base ⊆
        (U (cp (pj j)) : Set _) := by
      rintro _ ⟨x, rfl⟩
      apply hrpU (pj j)
      rw [hpj j]
      exact not_mem_specMap_away _ x
    rw [bridge] at hsub
    refine hsub.trans ?_
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale (solution)
