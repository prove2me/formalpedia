-- Prove2me | solution 1 for NoetherianScheme.not_isNoetherianRing_adeleRing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:07:50.912685+00:00
-- url     : https://prove2.me/submissions/68452c29-f9ea-422d-ad2d-85e4a9275d85

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

namespace S215AD

lemma not_noeth_of_idem {R ι : Type*} [CommRing R] [Infinite ι] (e : ι → R)
    (h1 : ∀ i j, i ≠ j → e i * e j = 0) (h2 : ∀ i, e i * e i = e i) (h3 : ∀ i, e i ≠ 0) :
    ¬ IsNoetherianRing R := by
  intro hR
  let g : ℕ ↪ ι := Infinite.natEmbedding ι
  let f : ℕ →o Ideal R := ⟨fun n => Ideal.span ((e ∘ g) '' {m | m < n}), by
    intro a b hab
    apply Ideal.span_mono
    apply Set.image_mono
    intro m hm; simp only [Set.mem_ofPred_eq] at hm ⊢; omega⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).2 hR f
  have hmem : e (g N) ∈ f N := by
    rw [hN (N+1) (by omega)]
    exact Ideal.subset_span ⟨N, by simp, rfl⟩
  have key : ∀ x ∈ f N, x * e (g N) = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨m, hm, rfl⟩
      simp only [Set.mem_ofPred_eq] at hm
      exact h1 _ _ (fun h => by have := g.injective h; omega)
    · simp
    · intro a b _ _ ha hb; rw [add_mul, ha, hb, add_zero]
    · intro a b _ hb; rw [smul_eq_mul, mul_assoc, hb, mul_zero]
  exact h3 (g N) ((h2 (g N)).symm.trans (key _ hmem))

lemma infinite_hos (K : Type u) [Field K] [NumberField K] :
    Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  classical
  have hP : ∀ p : Nat.Primes, ∃ Q : Ideal (𝓞 K), Q.IsMaximal ∧
      Q.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
    intro p
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal := by
      exact PrincipalIdealRing.isMaximal_of_irreducible
        (Prime.irreducible (Nat.prime_iff_prime_int.mp p.2))
    apply Ideal.exists_ideal_over_maximal_of_isIntegral
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by simpa using hx)
    simp [this]
  choose Q hQm hQc using hP
  let F : Nat.Primes → IsDedekindDomain.HeightOneSpectrum (𝓞 K) := fun p =>
    ⟨Q p, (hQm p).isPrime, by
      intro h
      have := hQc p
      rw [h, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at this
      have h' := this.symm
      rw [Ideal.span_singleton_eq_bot] at h'
      exact p.2.ne_zero (by exact_mod_cast h')⟩
  have hF : Function.Injective F := by
    intro p q hpq
    have : Q p = Q q := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hpq
    have h := (hQc p).symm.trans (this ▸ hQc q)
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
    exact Subtype.ext (by simpa using h)
  exact Infinite.of_injective F hF

end S215AD

open RestrictedProduct in
theorem solution (K : Type u) [Field K] [NumberField K] :
    ¬ IsNoetherianRing (AdeleRing (𝓞 K) K) := by
  classical
  intro hA
  haveI : IsNoetherianRing (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
    isNoetherianRing_of_surjective (AdeleRing (𝓞 K) K) _
      (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
      (fun x => ⟨(0, x), rfl⟩)
  haveI := S215AD.infinite_hos K
  let P := Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    [v.adicCompletion K, v.adicCompletionIntegers K]
  have hP : IsNoetherianRing P := by assumption
  let e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → P :=
    fun v => RestrictedProduct.single (fun w => w.adicCompletionIntegers K) v 1
  refine S215AD.not_noeth_of_idem e ?_ ?_ ?_ hP
  · intro i j hij
    apply RestrictedProduct.ext
    intro w
    rw [RestrictedProduct.mul_apply]
    by_cases hw : w = i
    · subst hw
      simp [e, RestrictedProduct.single_eq_of_ne _ _ hij]
    · simp [e, RestrictedProduct.single_eq_of_ne _ _ hw]
  · intro i
    apply RestrictedProduct.ext
    intro w
    rw [RestrictedProduct.mul_apply]
    by_cases hw : w = i
    · subst hw; simp [e]
    · simp [e, RestrictedProduct.single_eq_of_ne _ _ hw]
  · intro i h
    have h2 := congrFun (congrArg Subtype.val h) i
    have h3 : (e i).val i = 1 := by
      show (Pi.single (M := fun w => w.adicCompletion K) i 1 : _) i = 1
      exact Pi.single_eq_same _ _
    rw [h3] at h2
    exact one_ne_zero h2
