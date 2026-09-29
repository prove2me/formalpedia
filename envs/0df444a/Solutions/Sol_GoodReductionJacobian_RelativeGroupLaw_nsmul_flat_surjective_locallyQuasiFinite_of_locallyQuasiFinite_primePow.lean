-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0de903f7-c3b8-5ef2-a569-39bada4200c1

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul
import Theorems.Thm_GaloisRep_ratLocalizedAt_exists_specMap_comp_eq_fromSpecResidueField
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom
import Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

set_option maxHeartbeats 1600000

namespace L3C6p

open GoodReductionJacobian.RelativeGroupLaw

section generic
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem preconnectedSpace_fibreScheme (s : (Spec (CommRingCat.of R) : Scheme.{u}))
    (h : _root_.IsPreconnected (f.base ⁻¹' {s})) : PreconnectedSpace ↥(fibreScheme f s) := by
  have h1 : PreconnectedSpace ↥(f.base ⁻¹' {s}) := isPreconnected_iff_preconnectedSpace.mp h
  constructor
  have := (f.fiberHomeo s).symm.isPreconnected_image.mpr h1.isPreconnected_univ
  rwa [Set.image_univ, EquivLike.range_eq_univ] at this

theorem nonempty_fibreScheme (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Nonempty ↥(fibreScheme f s) := by
  let e := ((G.fibre s).one (𝟙 _)).1
  obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (baseResidueField s))))
  exact ⟨e.base x⟩

theorem isCommutative_fibre (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
    (s : (Spec (CommRingCat.of R) : Scheme.{u})) : (G.fibre s).IsCommutative := by
  rw [fibre_eq_baseChange]
  exact hc.baseChange _

theorem nsmul_coe (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := by
    apply Subtype.ext
    simp [GoodReductionJacobian.schemeHomOverComp]
  have := G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hx] at this
  rw [← this]
  rfl

theorem nsmul_add' (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (m n : ℕ)
    (x : SchemeHomOver t f) : G.nsmul t (m + n) x = G.mul t (G.nsmul t m x) (G.nsmul t n x) := by
  induction n with
  | zero => rw [Nat.add_zero, RelativeGroupLaw.nsmul_zero, G.mul_one]
  | succ n ih => rw [Nat.add_succ, nsmul_succ, nsmul_succ, ih, G.mul_assoc]

theorem nsmul_mul' (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : ℕ)
    (x : SchemeHomOver t f) : G.nsmul t (a * b) x = G.nsmul t a (G.nsmul t b x) := by
  induction a with
  | zero => rw [Nat.zero_mul, RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]
  | succ a ih => rw [Nat.succ_mul, nsmul_add', ih, nsmul_succ]

theorem schemeNsmul_mul (G : RelativeGroupLaw R f) (a b : ℕ) :
    G.schemeNsmul (a * b) = G.schemeNsmul b ≫ G.schemeNsmul a := by
  show (G.nsmul f (a * b) idPoint).1 = _
  rw [nsmul_mul', nsmul_coe, nsmul_coe]
  simp

theorem schemeNsmul_baseChange_comp (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] [P.RespectsIso] [P.ContainsIdentities]
    {R' : Type u} [CommRing R'] {R'' : Type u} [CommRing R'']
    (ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    (G : RelativeGroupLaw R f) (n : ℕ) (hfl : P ((G.baseChange ι').schemeNsmul n)) :
    P ((G.baseChange (j ≫ ι')).schemeNsmul n) := by

  have hmap := (baseChange_schemeNsmul_comp_fst_and_eq_pullback_map j (G.baseChange ι') n).2.2
  have hfl2 : P (((G.baseChange ι').baseChange j).schemeNsmul n) := by
    rw [hmap]
    exact MorphismProperty.pullback_map hfl (P.id_mem _)
      ((G.baseChange ι').schemeNsmul_over n).symm (Category.id_comp j).symm

  obtain ⟨u, v, huv, hvu, -, hhom⟩ := exists_schemeHomOver_baseChange_baseChange_iso ι' j G
  have hcomm := (schemeNsmul_comp_eq_comp_schemeNsmul_of_hom _ _ u hhom).2.2 n

  have heq : (G.baseChange (j ≫ ι')).schemeNsmul n =
      v.1 ≫ ((G.baseChange ι').baseChange j).schemeNsmul n ≫ u.1 := by
    rw [hcomm, ← Category.assoc, hvu, Category.id_comp]
  haveI : IsIso u.1 := ⟨⟨v.1, huv, hvu⟩⟩
  haveI : IsIso v.1 := ⟨⟨u.1, hvu, huv⟩⟩
  rw [heq]
  exact MorphismProperty.RespectsIso.precomp P v.1 _ (MorphismProperty.RespectsIso.postcomp P u.1 _ hfl2)

end generic

section overZ
variable {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of ℤ)}

theorem isUnit_natCast_baseResidueField (s : (Spec (CommRingCat.of ℤ) : Scheme.{0})) (n : ℕ)
    (hn : (n : ℤ) ∉ s.asIdeal) : IsUnit ((n : baseResidueField s)) := by
  let e := Scheme.Spec.residueFieldIso (CommRingCat.of ℤ) s

  have hu : IsUnit ((n : s.asIdeal.ResidueField)) := by
    have h1 : IsUnit (algebraMap ℤ (Localization.AtPrime s.asIdeal) (n : ℤ)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ s.asIdeal (n : ℤ)).mpr hn
    have h2 := h1.map (IsLocalRing.residue (Localization.AtPrime s.asIdeal))
    simpa using h2

  have := hu.map e.inv.hom
  rwa [map_natCast] at this

theorem exists_prime_eq_span (s : (Spec (CommRingCat.of ℤ) : Scheme.{0})) (n : ℕ) (hn0 : 0 < n)
    (hmem : (n : ℤ) ∈ s.asIdeal) : ∃ ℓ : ℕ, ℓ.Prime ∧ s.asIdeal = Ideal.span {(ℓ : ℤ)} ∧ ℓ ∣ n := by
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal s.asIdeal).principal
  have hq' : s.asIdeal = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [hq', Ideal.span_singleton_zero, Ideal.mem_bot] at hmem
    exact_mod_cast hn0.ne' (by exact_mod_cast hmem)
  have hqprime : Prime q := (Ideal.span_singleton_prime hq0).mp (hq' ▸ s.isPrime)
  refine ⟨q.natAbs, Int.prime_iff_natAbs_prime.mp hqprime, ?_, ?_⟩
  · rw [hq', Int.span_natAbs]
  · have : (q : ℤ) ∣ (n : ℤ) := Ideal.mem_span_singleton.mp (hq' ▸ hmem)
    exact Int.natCast_dvd_natCast.mp ((Int.natAbs_dvd.mpr this))

variable [Smooth g] (L : RelativeGroupLaw ℤ g)

theorem locallyQuasiFinite_fibre_schemeNsmul (hc : L.IsCommutative) (p : ℕ) [Fact p.Prime]
    (hA : ∀ s : Spec (CommRingCat.of ℤ), s.asIdeal = Ideal.span {(p : ℤ)} →
      ∀ k : ℕ, 0 < k → LocallyQuasiFinite ((L.fibre s).schemeNsmul (p ^ k)))
    (hB : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite ((L.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))).schemeNsmul (ℓ ^ k)))
    (s : Spec (CommRingCat.of ℤ)) (n : ℕ) (hn : 0 < n) :
    LocallyQuasiFinite ((L.fibre s).schemeNsmul n) := by
  have hcs : (L.fibre s).IsCommutative := isCommutative_fibre L hc s

  have hunit : ∀ m : ℕ, (m : ℤ) ∉ s.asIdeal → LocallyQuasiFinite ((L.fibre s).schemeNsmul m) := fun m hm =>
    locallyQuasiFinite_schemeNsmul_of_isUnit (L.fibre s) (fun t x y => hcs t x y) m
      (isUnit_natCast_baseResidueField s m hm)
  by_cases hmem : (n : ℤ) ∈ s.asIdeal
  · obtain ⟨ℓ, hℓ, hs, hℓn⟩ := exists_prime_eq_span s n hn hmem
    haveI : Fact ℓ.Prime := ⟨hℓ⟩

    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' ℓ hℓ.ne_one
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso; rw [hkm, h0, pow_zero, _root_.one_mul] at hℓn; exact hm hℓn
      · exact h0
    have hmunit : (m : ℤ) ∉ s.asIdeal := by
      rw [hs, Ideal.mem_span_singleton]
      exact fun h => hm (Int.natCast_dvd_natCast.mp h)

    have hpow : LocallyQuasiFinite ((L.fibre s).schemeNsmul (ℓ ^ k)) := by
      by_cases hℓp : ℓ = p
      · subst hℓp
        exact hA s hs k hk
      · obtain ⟨φ, -, -, hφ⟩ := GaloisRep.ratLocalizedAt.exists_specMap_comp_eq_fromSpecResidueField ℓ s hs
        have key := schemeNsmul_baseChange_comp @LocallyQuasiFinite
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))
          (Spec.map (CommRingCat.ofHom φ)) L (ℓ ^ k) (hB ℓ hℓp k hk)
        have gen : ∀ (m' : Spec (CommRingCat.of (baseResidueField s)) ⟶ Spec (CommRingCat.of ℤ)),
            m' = basePointInclusion s → LocallyQuasiFinite ((L.baseChange m').schemeNsmul (ℓ ^ k)) →
              LocallyQuasiFinite ((L.fibre s).schemeNsmul (ℓ ^ k)) := by
          intro m' hm' h
          subst hm'
          exact h
        exact gen _ hφ key

    haveI := hpow
    haveI := hunit m hmunit
    rw [hkm, schemeNsmul_mul]
    infer_instance
  · exact hunit n hmem

theorem flat_fibre_schemeNsmul
    (hconn : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (s : Spec (CommRingCat.of ℤ)) (n : ℕ) [LocallyQuasiFinite ((L.fibre s).schemeNsmul n)] :
    Flat ((L.fibre s).schemeNsmul n) := by
  haveI : PreconnectedSpace ↥(fibreScheme g s) := preconnectedSpace_fibreScheme s (hconn s)
  exact flat_schemeNsmul_of_locallyQuasiFinite_of_field (L.fibre s) n

theorem surjective_fibre_schemeNsmul (hc : L.IsCommutative)
    (hconn : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (s : Spec (CommRingCat.of ℤ)) (n : ℕ) [Flat ((L.fibre s).schemeNsmul n)] :
    Surjective ((L.fibre s).schemeNsmul n) := by
  haveI : PreconnectedSpace ↥(fibreScheme g s) := preconnectedSpace_fibreScheme s (hconn s)
  haveI : Nonempty ↥(fibreScheme g s) := nonempty_fibreScheme L s
  haveI : IsIntegral (fibreScheme g s) :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (fibreStr g s)
  exact surjective_schemeNsmul_of_flat_of_field (L.fibre s) (isCommutative_fibre L hc s) n

end overZ

end L3C6p

theorem solution
    (p : ℕ) [Fact p.Prime] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of ℤ)} [Smooth g]
    (L : RelativeGroupLaw ℤ g) (hc : L.IsCommutative)
    (hconn : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (hA : ∀ s : Spec (CommRingCat.of ℤ), s.asIdeal = Ideal.span {(p : ℤ)} →
      ∀ k : ℕ, 0 < k → LocallyQuasiFinite ((L.fibre s).schemeNsmul (p ^ k)))
    (hB : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite ((L.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))).schemeNsmul (ℓ ^ k))) :
    (∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n)) ∧ (∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n)) ∧
      (∀ n : ℕ, 0 < n → LocallyQuasiFinite (L.schemeNsmul n)) := by
  have hlqf : ∀ s (n : ℕ), 0 < n → LocallyQuasiFinite ((L.fibre s).schemeNsmul n) := fun s n hn =>
    L3C6p.locallyQuasiFinite_fibre_schemeNsmul L hc p hA hB s n hn
  have hflat : ∀ s (n : ℕ), 0 < n → Flat ((L.fibre s).schemeNsmul n) := fun s n hn => by
    haveI := hlqf s n hn
    exact L3C6p.flat_fibre_schemeNsmul L hconn s n
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · exact GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul L n
      (fun s => hflat s n hn)
  · apply GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul L n
    intro s
    haveI := hflat s n hn
    exact L3C6p.surjective_fibre_schemeNsmul L hc hconn s n
  · apply AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo g
      (L.schemeNsmul n) (L.schemeNsmul_over n)
    intro s
    rw [← GoodReductionJacobian.RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo]
    exact hlqf s n hn

end S_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow (solution)
