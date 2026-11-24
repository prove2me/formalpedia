-- Prove2me | solution 1 for GlobalTheory.QNorm.conj_places_transitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:55.754811+00:00
-- url     : https://prove2.me/submissions/42525fa3-878d-41d2-968e-86745ff745e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Theorems.Thm_GlobalTheory_QNorm_valuation_of_eq_comap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma ringOfIntegers_mapRingEquiv_algebraMap {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : 𝓞 F) :
    RingOfIntegers.mapRingEquiv (σ : E ≃+* E) (algebraMap (𝓞 F) (𝓞 E) n) =
      algebraMap (𝓞 F) (𝓞 E) n := by
  ext
  rw [show ((algebraMap (𝓞 F) (𝓞 E) n : 𝓞 E) : E) = algebraMap F E (n : F) from rfl]
  exact σ.commutes _
open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_algebraMap_eq_mul_conj_of_isQuad {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
    (hq : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (x : 𝓞 E) :
    ∃ n : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) n = x * RingOfIntegers.mapRingEquiv (σ : E ≃+* E) x := by
  obtain ⟨a, b, hab⟩ := hq.span (x : E)
  have hprod : (x : E) * σ (x : E) = algebraMap F E (a ^ 2 - b ^ 2 * δ) := by
    rw [hab]
    simp only [map_add, map_mul, AlgEquiv.commutes, hq.conj]
    rw [map_sub, map_mul, map_pow, map_pow, ← hq.sq]
    ring
  have hint : IsIntegral ℤ (algebraMap F E (a ^ 2 - b ^ 2 * δ)) := by
    rw [← hprod]
    exact (RingOfIntegers.isIntegral_coe x).mul
      (RingOfIntegers.isIntegral_coe (RingOfIntegers.mapRingEquiv (σ : E ≃+* E) x))
  refine ⟨⟨a ^ 2 - b ^ 2 * δ,
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).mp hint⟩, ?_⟩
  ext
  exact hprod.symm
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ w : HeightOneSpectrum (𝓞 E), ∃ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 F) = w.under (𝓞 F) ∧ ∀ y : E, w'.valuation E y = w.valuation E (σ y)) ∧
    ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      w' = w ∨ ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by
  intro F E _ _ _ _ _ δ θ σ hq
  set e := RingOfIntegers.mapRingEquiv (σ : E ≃+* E) with he
  refine ⟨fun w => ?_, fun w w' hunder => ?_⟩
  · refine ⟨HeightOneSpectrum.comap (e : 𝓞 E →+* 𝓞 E) e.surjective w, ?_, fun y =>
      _root_.GlobalTheory.QNorm.valuation_of_eq_comap (σ : E ≃+* E) w _ rfl y⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    ext n
    change e (algebraMap (𝓞 F) (𝓞 E) n) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) n ∈ w.asIdeal
    rw [he, ringOfIntegers_mapRingEquiv_algebraMap]
  · by_cases hw : w' = w
    · exact Or.inl hw
    right
    refine _root_.GlobalTheory.QNorm.valuation_of_eq_comap (σ : E ≃+* E) w w' ?_
    by_contra hne
    have h1 : ¬ w'.asIdeal ≤ w.asIdeal := fun hle =>
      hw (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle))
    have h2 : ¬ w'.asIdeal ≤ w.asIdeal.comap e := fun hle =>
      hne (w'.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) hle)
    have hns : ¬ ((w'.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ (w.asIdeal.comap e)) :=
      fun hs => (Ideal.subset_union.mp hs).elim h1 h2
    rw [Set.not_subset] at hns
    obtain ⟨x, hx, hxn⟩ := hns
    simp only [Set.mem_union, SetLike.mem_coe, Ideal.mem_comap, not_or] at hxn
    obtain ⟨n, hn⟩ := exists_algebraMap_eq_mul_conj_of_isQuad hq x
    have hnw' : n ∈ (w'.under (𝓞 F)).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal]
      change algebraMap (𝓞 F) (𝓞 E) n ∈ w'.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [hunder, HeightOneSpectrum.under_asIdeal] at hnw'
    change algebraMap (𝓞 F) (𝓞 E) n ∈ w.asIdeal at hnw'
    rw [hn] at hnw'
    rcases w.isPrime.mem_or_mem hnw' with h | h
    · exact hxn.1 h
    · exact hxn.2 h
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
