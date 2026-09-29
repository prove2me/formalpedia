-- Prove2me | solution 1 for NumberField.AdeleRing.exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/511d970d-651f-535c-a692-3adebfb3d7ea

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top

set_option autoImplicit false

namespace R4H90U

def UnitSelect (R : Type*) [CommRing R] : Prop :=
  ∀ (n : ℕ) (t c : Fin n → R), ∑ i, c i * t i = 1 →
    ∃ (e : Fin n → R) (w : R), CompleteOrthogonalIdempotents e ∧ (∑ i, e i * t i) * w = 1

theorem completeOrthogonalIdempotents_single {R : Type*} [CommRing R] {n : ℕ} (i₀ : Fin n) :
    CompleteOrthogonalIdempotents (Pi.single (M := fun _ : Fin n => R) i₀ 1) := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · by_cases h : i = i₀
    · subst h; simp [IsIdempotentElem]
    · simp [IsIdempotentElem, h]
  · change Pi.single (M := fun _ : Fin n => R) i₀ 1 i * Pi.single (M := fun _ : Fin n => R) i₀ 1 j = 0
    by_cases hi : i = i₀
    · subst hi
      rw [Pi.single_eq_of_ne (Ne.symm hij), mul_zero]
    · rw [Pi.single_eq_of_ne hi, zero_mul]
  · exact Fintype.sum_pi_single' i₀ 1

theorem unitSelect_of_isLocalRing (R : Type*) [CommRing R] [IsLocalRing R] : UnitSelect R := by
  intro n t c h
  classical
  have hex : ∃ i, IsUnit (t i) := by
    by_contra hcon
    push Not at hcon
    have hmem : ∀ i, c i * t i ∈ IsLocalRing.maximalIdeal R := fun i =>
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon i))
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      rw [← h]; exact Ideal.sum_mem _ fun i _ => hmem i
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      ((Ideal.eq_top_iff_one _).2 h1)
  obtain ⟨i₀, hi₀⟩ := hex
  refine ⟨Pi.single i₀ 1, ↑hi₀.unit⁻¹, completeOrthogonalIdempotents_single i₀, ?_⟩
  have hsum : ∑ i, Pi.single (M := fun _ : Fin n => R) i₀ (1 : R) i * t i = t i₀ := by
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  exact hi₀.mul_val_inv

theorem unitSelect_pi {ι : Type*} (R : ι → Type*) [∀ k, CommRing (R k)]
    (h : ∀ k, UnitSelect (R k)) : UnitSelect (∀ k, R k) := by
  intro n t c hsum
  have H : ∀ k, ∃ (e : Fin n → R k) (w : R k),
      CompleteOrthogonalIdempotents e ∧ (∑ i, e i * t i k) * w = 1 := by
    intro k
    refine h k n (fun i => t i k) (fun i => c i k) ?_
    have := congrFun hsum k
    simpa [Finset.sum_apply] using this
  choose e w he hw using H
  refine ⟨fun i k => e k i, fun k => w k, ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, ?_⟩
  · funext k; exact (he k).idem i
  · funext k; exact (he k).ortho hij
  · funext k
    simp only [Finset.sum_apply, Pi.one_apply]
    exact (he k).complete
  · funext k
    simp only [Pi.mul_apply, Finset.sum_apply, Pi.one_apply]
    exact hw k

theorem unitSelect_prod (R S : Type*) [CommRing R] [CommRing S]
    (hR : UnitSelect R) (hS : UnitSelect S) : UnitSelect (R × S) := by
  intro n t c hsum
  have h1 : ∑ i, (c i).1 * (t i).1 = 1 := by
    have := congrArg Prod.fst hsum
    simpa [Prod.fst_sum] using this
  have h2 : ∑ i, (c i).2 * (t i).2 = 1 := by
    have := congrArg Prod.snd hsum
    simpa [Prod.snd_sum] using this
  obtain ⟨e₁, w₁, he₁, hw₁⟩ := hR n _ _ h1
  obtain ⟨e₂, w₂, he₂, hw₂⟩ := hS n _ _ h2
  refine ⟨fun i => (e₁ i, e₂ i), (w₁, w₂), ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, ?_⟩
  · exact Prod.ext (he₁.idem i) (he₂.idem i)
  · exact Prod.ext (he₁.ortho hij) (he₂.ortho hij)
  · exact Prod.ext (by simpa [Prod.fst_sum] using he₁.complete)
      (by simpa [Prod.snd_sum] using he₂.complete)
  · exact Prod.ext (by simpa [Prod.fst_sum] using hw₁) (by simpa [Prod.snd_sum] using hw₂)

section Restricted

open scoped RestrictedProduct
open Filter

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
variable {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubringClass (S i) (R i)]
variable {B : ∀ i, S i}

theorem unitSelect_restrictedProduct
    (hR : ∀ i, UnitSelect (R i)) (hB : ∀ i, UnitSelect (B i)) :
    UnitSelect (Πʳ i, [R i, B i]) := by
  intro n t c hsum
  classical
  let good : ι → Prop := fun i => (∀ k, t k i ∈ B i) ∧ (∀ k, c k i ∈ B i)
  have hgood : ∀ᶠ i in cofinite, good i :=
    (Filter.eventually_all.2 fun k => (t k).2).and (Filter.eventually_all.2 fun k => (c k).2)
  let φ : ∀ i, (Πʳ i, [R i, B i]) →+* R i := fun i => RestrictedProduct.evalRingHom R i
  have hφsum : ∀ i, ∑ k, c k i * t k i = 1 := fun i => by
    have := congrArg (φ i) hsum
    simpa [φ, map_sum, map_mul] using this
  have H : ∀ i, ∃ (e : Fin n → R i) (w : R i),
      CompleteOrthogonalIdempotents e ∧ (∑ k, e k * t k i) * w = 1 ∧
        (good i → (∀ k, e k ∈ B i) ∧ w ∈ B i) := by
    intro i
    by_cases hg : good i
    · obtain ⟨hgt, hgc⟩ := hg
      let t₀ : Fin n → B i := fun k => ⟨t k i, hgt k⟩
      let c₀ : Fin n → B i := fun k => ⟨c k i, hgc k⟩
      have h₀ : ∑ k, c₀ k * t₀ k = 1 := by
        apply Subtype.ext
        have hc : ((∑ k, c₀ k * t₀ k : B i) : R i) = ∑ k, c k i * t k i := by
          rw [show ((∑ k, c₀ k * t₀ k : B i) : R i) =
              SubringClass.subtype (B i) (∑ k, c₀ k * t₀ k) from rfl, map_sum]
          rfl
        rw [hc, hφsum i]
        rfl
      obtain ⟨e₀, w₀, he₀, hw₀⟩ := hB i n t₀ c₀ h₀
      refine ⟨fun k => (e₀ k : R i), (w₀ : R i), ?_, ?_, fun _ => ⟨fun k => (e₀ k).2, w₀.2⟩⟩
      · exact he₀.map (SubringClass.subtype (B i))
      · have := congrArg (SubringClass.subtype (B i)) hw₀
        simpa [map_sum, map_mul] using this
    · obtain ⟨e, w, he, hw⟩ := hR i n (fun k => t k i) (fun k => c k i) (hφsum i)
      exact ⟨e, w, he, hw, fun hg' => absurd hg' hg⟩
  choose e w he hw hint using H
  refine ⟨fun k => RestrictedProduct.mk (fun i => e i k) (hgood.mono fun i hi => (hint i hi).1 k),
    RestrictedProduct.mk (fun i => w i) (hgood.mono fun i hi => (hint i hi).2),
    ⟨⟨fun k => ?_, fun k l hkl => ?_⟩, ?_⟩, ?_⟩
  · exact RestrictedProduct.ext _ _ fun i => (he i).idem k
  · exact RestrictedProduct.ext _ _ fun i => (he i).ortho hkl
  · refine RestrictedProduct.ext _ _ fun i => ?_
    have := (he i).complete
    change (φ i) _ = (φ i) 1
    rw [map_sum, map_one]
    exact this
  · refine RestrictedProduct.ext _ _ fun i => ?_
    have h1 := hw i
    have h2 : (φ i) ((∑ k, RestrictedProduct.mk (fun i => e i k)
        (hgood.mono fun i hi => (hint i hi).1 k) * t k) *
        RestrictedProduct.mk (fun i => w i) (hgood.mono fun i hi => (hint i hi).2)) = (φ i) 1 := by
      rw [map_mul, map_sum, map_one]
      simp only [map_mul]
      exact h1
    exact h2

end Restricted

section Adelic

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in

theorem unitSelect_infiniteAdeleRing : UnitSelect (InfiniteAdeleRing K) :=
  unitSelect_pi (fun v : InfinitePlace K => v.Completion) fun _ => unitSelect_of_isLocalRing _

theorem unitSelect_finiteAdeleRing : UnitSelect (FiniteAdeleRing (𝓞 K) K) :=
  unitSelect_restrictedProduct (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
    (fun _ => unitSelect_of_isLocalRing _) (fun _ => unitSelect_of_isLocalRing _)

theorem unitSelect_adeleRing : UnitSelect (AdeleRing (𝓞 K) K) :=
  unitSelect_prod _ _ (unitSelect_infiniteAdeleRing K) (unitSelect_finiteAdeleRing K)

end Adelic

theorem main {R : Type*} [CommRing R] (hR : UnitSelect R) {ι : Type*} [Fintype ι] (t : ι → R)
    (h : Ideal.span (Set.range t) = ⊤) :
    ∃ e : ι → R, CompleteOrthogonalIdempotents e ∧ IsUnit (∑ i, e i * t i) := by
  classical
  have h1 : (1 : R) ∈ Ideal.span (Set.range t) := by rw [h]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h1
  simp only [smul_eq_mul] at hc
  set σ := Fintype.equivFin ι with hσ
  obtain ⟨e', w, he', hw⟩ := hR (Fintype.card ι) (t ∘ σ.symm) (c ∘ σ.symm) (by
    rw [← hc]
    exact Equiv.sum_comp σ.symm (fun i => c i * t i))
  refine ⟨e' ∘ σ, (CompleteOrthogonalIdempotents.equiv σ).2 he', ?_⟩
  have hs : ∑ i, (e' ∘ σ) i * t i = ∑ k, e' k * (t ∘ σ.symm) k := by
    rw [← Equiv.sum_comp σ.symm (fun i => (e' ∘ σ) i * t i)]
    simp
  rw [hs]
  exact isUnit_iff_exists_inv.2 ⟨w, hw⟩

end R4H90U

open NumberField in
theorem solution
    (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (t : ι → AdeleRing (𝓞 K) K)
    (h : Ideal.span (Set.range t) = ⊤) :
    ∃ e : ι → AdeleRing (𝓞 K) K, CompleteOrthogonalIdempotents e ∧ IsUnit (∑ i, e i * t i) :=
  R4H90U.main (R4H90U.unitSelect_adeleRing K) t h

end S_NumberField_AdeleRing_exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top
end P2MW
export P2MW.S_NumberField_AdeleRing_exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top (solution)
