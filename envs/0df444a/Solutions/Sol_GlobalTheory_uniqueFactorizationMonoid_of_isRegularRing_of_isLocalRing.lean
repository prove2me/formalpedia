-- Prove2me | solution 1 for GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:58.900702+00:00
-- url     : https://prove2.me/submissions/9d1231f4-881e-4713-93e5-9f8768d793cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace RegularFactorial
open IsLocalRing
end RegularFactorial
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
open IsLocalRing in
private lemma prime_of_mem_maximalIdeal_of_not_mem_sq {A : Type} [CommRing A] [IsRegularLocalRing A]
    {x : A} (hx : x ∈ maximalIdeal A) (hx2 : x ∉ maximalIdeal A ^ 2) : Prime x := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (Ideal.zero_mem _)
  haveI := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hx hx2
  haveI : IsDomain (A ⧸ Ideal.span {x}) := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  rw [← Ideal.span_singleton_prime hx0]
  exact (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma isPrincipal_of_isPrincipal_map_away_prime {A : Type} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {x : A} (hx : Prime x) {p : Ideal A} [hp : p.IsPrime] (hxp : x ∉ p)
    (h : (p.map (algebraMap A (Localization.Away x))).IsPrincipal) : p.IsPrincipal := by
  obtain ⟨f, hf⟩ := h
  have hfmem : f ∈ p.map (algebraMap A (Localization.Away x)) := by
    rw [hf]; exact Submodule.mem_span_singleton_self f
  obtain ⟨⟨a, m⟩, ham⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers x) (Localization.Away x)).1 hfmem
  have hx0 : x ≠ 0 := hx.ne_zero
  have hinj : Function.Injective (algebraMap A (Localization.Away x)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  have hmul : ∀ y ∈ p, ∃ (s : ℕ) (c : A), x ^ s * y = (a : A) * c := by
    intro y hy
    have hy' : algebraMap A (Localization.Away x) y ∈ p.map (algebraMap A (Localization.Away x)) :=
      Ideal.mem_map_of_mem _ hy
    rw [hf] at hy'
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hy'
    obtain ⟨⟨e, k⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) d
    obtain ⟨j, hj⟩ := k.2
    obtain ⟨i, hi⟩ := m.2
    refine ⟨j + i, e, hinj ?_⟩
    simp only [smul_eq_mul] at hd
    have h1 := IsLocalization.mk'_spec (Localization.Away x) e k
    dsimp only at ham hj hi
    rw [map_mul, map_mul, ← hd, ← ham, pow_add, map_mul, hj, hi, ← h1]
    ring
  by_cases ha0 : (a : A) = 0
  · refine ⟨0, le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨s, c, hsc⟩ := hmul y hy
      rw [ha0, zero_mul] at hsc
      have hy0 : y = 0 := (mul_eq_zero.1 hsc).resolve_left (pow_ne_zero _ hx0)
      rw [hy0]; exact Submodule.zero_mem _
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact p.zero_mem
  · obtain ⟨g, hag, hxg⟩ :=
      (FiniteMultiplicity.of_not_isUnit hx.not_unit ha0).exists_eq_pow_mul_and_not_dvd
    have hxr : x ^ multiplicity x (a : A) ∉ p := fun h => hxp (hp.mem_of_pow_mem _ h)
    have hg : g ∈ p := (hp.mem_or_mem (hag ▸ a.2)).resolve_left hxr
    refine ⟨g, le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨s, c, hsc⟩ := hmul y hy
      rw [hag] at hsc
      obtain ⟨c', hc'⟩ := hx.pow_dvd_of_dvd_mul_left s hxg
        (⟨y, by linear_combination -hsc⟩ : x ^ s ∣ g * (x ^ multiplicity x (a : A) * c))
      have hy : y = g * c' :=
        mul_left_cancel₀ (pow_ne_zero s hx0) (by linear_combination hsc + g * hc')
      rw [hy]
      exact Submodule.mem_span_singleton.2 ⟨c', by rw [smul_eq_mul, mul_comm]⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hg
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
open IsLocalRing in
private lemma uniqueFactorizationMonoid_localization_of_height_le
    (hPD : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n)
    (hPrin : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R)
      (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R I) n →
      Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal)
    {R : Type} [CommRing R] [IsRegularRing R] (n : ℕ) :
    ∀ (Q : Ideal R) [Q.IsPrime], Q.height ≤ n → UniqueFactorizationMonoid (Localization.AtPrime Q) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ hQ
  rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
  intro p _ hph
  by_cases hm : ∃ x ∈ maximalIdeal (Localization.AtPrime Q), x ∉ maximalIdeal (Localization.AtPrime Q) ^ 2
  · obtain ⟨x, hx, hx2⟩ := hm
    have hxp := prime_of_mem_maximalIdeal_of_not_mem_sq hx hx2
    by_cases hxmem : x ∈ p
    · exact ⟨x, Ideal.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩
    · refine isPrincipal_of_isPrincipal_map_away_prime hxp hxmem ?_
      obtain ⟨N, hN⟩ := hPD (Localization.AtPrime Q) p
      refine hPrin _ x (Localization.Away x) p N hN ?_
      haveI : Module.FinitePresentation (Localization.Away x)
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))) :=
        Module.finitePresentation_of_finite _ _
      refine Module.projective_of_localization_maximal (fun q hq => ?_)
      haveI := hq.isPrime
      haveI hloc₁ : IsLocalization.AtPrime (Localization.AtPrime q)
          (q.comap (algebraMap (Localization.AtPrime Q) (Localization.Away x))) :=
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers x) _ q
      set q₁ := q.comap (algebraMap (Localization.AtPrime Q) (Localization.Away x)) with hq₁
      haveI hloc₂ : IsLocalization.AtPrime (Localization.AtPrime q) (q₁.comap (algebraMap R (Localization.AtPrime Q))) :=
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl _ q₁
      set q₂ := q₁.comap (algebraMap R (Localization.AtPrime Q)) with hq₂
      have hxq₁ : x ∉ q₁ := fun h => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x))
      have hq₁m : q₁ ≤ maximalIdeal (Localization.AtPrime Q) :=
        IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ hq.ne_top)
      have hq₂Q : q₂ < Q := by
        refine lt_of_le_of_ne ?_ ?_
        · rw [← IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime Q) Q]
          exact Ideal.comap_mono hq₁m
        · intro h
          apply hxq₁
          have := IsLocalization.map_comap Q.primeCompl (Localization.AtPrime Q) q₁
          rw [← this]
          change x ∈ Ideal.map _ q₂
          rw [h, IsLocalization.AtPrime.map_eq_maximalIdeal]
          exact hx
      have hlt : q₂.height < n := lt_of_lt_of_le (Ideal.height_strict_mono_of_isPrime hq₂Q) hQ
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hmn : m < n := by rw [← hm] at hlt; exact_mod_cast hlt
      haveI := ih m hmn q₂ hm.symm.le
      haveI : UniqueFactorizationMonoid (Localization.AtPrime q) :=
        (IsLocalization.algEquiv q₂.primeCompl (Localization.AtPrime q₂)
          (Localization.AtPrime q)).toMulEquiv.uniqueFactorizationMonoid inferInstance
      haveI : IsDomain (Localization.AtPrime q) :=
        (IsLocalization.algEquiv q₂.primeCompl (Localization.AtPrime q₂)
          (Localization.AtPrime q)).toRingEquiv.symm.injective.isDomain _
      have hJ : (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))).map
          (algebraMap (Localization.Away x) (Localization.AtPrime q)) =
          p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) := by
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      have hJprin : (p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q))).IsPrincipal := by
        by_cases hdisj : p ≤ q₁
        · have hd : Disjoint (q₁.primeCompl : Set (Localization.AtPrime Q)) p :=
            Set.disjoint_left.2 fun a ha hap => ha (hdisj hap)
          haveI := IsLocalization.isPrime_of_isPrime_disjoint q₁.primeCompl (Localization.AtPrime q) p ‹_› hd
          exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
            (by rw [IsLocalization.height_map_of_disjoint q₁.primeCompl p hd, hph])
        · obtain ⟨a, hap, haq⟩ := Set.not_subset.1 hdisj
          have htop : p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) = ⊤ :=
            Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hap)
              (IsLocalization.map_units (Localization.AtPrime q) (⟨a, haq⟩ : q₁.primeCompl))
          rw [htop]
          exact ⟨1, Ideal.span_singleton_one.symm⟩
      obtain ⟨g, hg⟩ := hJprin
      haveI : Module.Free (Localization.AtPrime q)
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q))) := by
        by_cases hg0 : g = 0
        · have hbot : p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) = ⊥ := by
            rw [hg, hg0]; exact Submodule.span_singleton_eq_bot.2 rfl
          rw [hbot]; infer_instance
        · rw [hg]; exact Module.Free.of_equiv (LinearEquiv.toSpanNonzeroSingleton _ _ g hg0)
      have heq : Submodule.localized' (Localization.AtPrime q) q.primeCompl
          (Algebra.linearMap (Localization.Away x) (Localization.AtPrime q))
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))) =
          p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) := by
        rw [Ideal.localized'_eq_map, hJ]
      exact Module.Projective.of_equiv (((IsLocalizedModule.iso q.primeCompl
        (Submodule.toLocalized' (Localization.AtPrime q) q.primeCompl
          (Algebra.linearMap (Localization.Away x) (Localization.AtPrime q))
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))))).extendScalarsOfIsLocalization
        q.primeCompl (Localization.AtPrime q)).trans (LinearEquiv.ofEq _ _ heq)).symm
  · push_neg at hm
    have hbot := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq (Localization.AtPrime Q) hm
    have hp : p = ⊥ := le_bot_iff.1 (hbot ▸ IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
    exact absurd hph (by rw [hp, Ideal.height_bot]; exact zero_ne_one)
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R)
      (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R I) n →
      Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal) →
    ∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R],
      UniqueFactorizationMonoid R := by
  intro hPD hPrin R _ _ _ _
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Ideal.height_ne_top (maximalIdeal.isMaximal R).ne_top)
  haveI := uniqueFactorizationMonoid_localization_of_height_le hPD hPrin n (maximalIdeal R) hn.symm.le
  exact (IsLocalization.atUnits R (maximalIdeal R).primeCompl
    (S := Localization.AtPrime (maximalIdeal R))
    (fun y hy => IsLocalRing.notMem_maximalIdeal.1 hy)).symm.toMulEquiv.uniqueFactorizationMonoid
    inferInstance
end _root_.GlobalTheory
end GlobalTheory
