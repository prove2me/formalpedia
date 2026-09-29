-- Prove2me | solution 1 for IsLocalRing.map_comap_eq_of_minimalPrimes_span_of_ringEquiv_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b69c5afa-7ee6-573b-8629-0a9a862a654b

import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_map_comap_eq_of_minimalPrimes_span_of_ringEquiv_adicCompletion

set_option autoImplicit false

open IsLocalRing

namespace B1aSol

open TensorProduct

theorem main
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (S : Type) [CommRing S] [IsNoetherianRing S]
    (e : AdicCompletion (maximalIdeal R) R ≃+* S)
    (r : R) (π : S) (hπ : e (algebraMap R (AdicCompletion (maximalIdeal R) R) r) = π)
    (hrad : (Ideal.span {π}).IsRadical)
    (P : Ideal S) (hP : P ∈ (Ideal.span {π}).minimalPrimes)
    (huniq : ∀ P' ∈ (Ideal.span {π}).minimalPrimes,
      P'.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
        P.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) →
      P' = P) :
    (P.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R)))).map
      ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) = P := by
  classical

  set Rh := AdicCompletion (maximalIdeal R) R with hRh
  set φ : R →+* S := (e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R)) with hφdef
  letI algRS : Algebra R S := φ.toAlgebra
  have hφ : algebraMap R S = φ := rfl
  have hφr : φ r = π := hπ
  haveI hPprime : P.IsPrime := hP.1.1
  have hπP : π ∈ P := hP.1.2 (Ideal.mem_span_singleton_self π)
  set Q : Ideal R := P.comap φ with hQdef
  haveI hQprime : Q.IsPrime := Ideal.comap_isPrime φ P

  haveI : Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
    refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal R (AdicCompletion (maximalIdeal R) R)).mpr
      ⟨inferInstance, fun I hI htop => ?_⟩
    have hle : I • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤ (maximalIdeal R) • ⊤ :=
      Submodule.smul_mono_left (le_maximalIdeal hI)
    rw [htop, top_le_iff, Ideal.smul_top_eq_map, ← AdicCompletion.maximalIdeal_eq_map] at hle
    have h1 : (1 : AdicCompletion (maximalIdeal R) R) ∈
        (maximalIdeal (AdicCompletion (maximalIdeal R) R)).restrictScalars R := by rw [hle]; trivial
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  let eL : (AdicCompletion (maximalIdeal R) R) ≃ₗ[R] S :=
    { e.toAddEquiv with
      map_smul' := fun c x => by
        show e (c • x) = c • e x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ]
        rfl }
  haveI : Module.Flat R S := Module.Flat.of_linearEquiv eL.symm

  have h1 : ∀ P' ∈ (Ideal.span {π}).minimalPrimes, P' ≠ P → ¬ (P'.comap φ ≤ Q) := by
    intro P' hP' hne hle
    haveI : P'.IsPrime := hP'.1.1
    haveI : (P'.comap φ).IsPrime := Ideal.comap_isPrime φ P'
    rcases eq_or_ne (P'.comap φ) Q with heq | hne'
    · exact hne (huniq P' hP' heq)
    · haveI : P.LiesOver Q := ⟨rfl⟩
      obtain ⟨P'', hP''le, hP''prime, hP''over⟩ :=
        Ideal.exists_ideal_le_liesOver_of_le (p := P'.comap φ) (q := Q) P hle
      have hunder : P''.comap φ = P'.comap φ := hP''over.over.symm
      have hπP'' : π ∈ P'' := by
        have hr' : r ∈ P'.comap φ := by
          rw [Ideal.mem_comap, hφr]; exact hP'.1.2 (Ideal.mem_span_singleton_self π)
        rw [← hunder, Ideal.mem_comap, hφr] at hr'
        exact hr'
      have hPle : P ≤ P'' := hP.2 ⟨hP''prime, (Ideal.span_singleton_le_iff_mem _).mpr hπP''⟩ hP''le
      have hPeq : P'' = P := le_antisymm hP''le hPle
      exact hne' (by rw [← hunder, hPeq])

  have hfin : (Ideal.span {π}).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing (R := S) (Ideal.span {π})
  let T : Finset (Ideal S) := hfin.toFinset.erase P
  have hTiff : ∀ P' : Ideal S, P' ∈ T ↔ P' ≠ P ∧ P' ∈ (Ideal.span {π}).minimalPrimes := fun P' => by
    simp only [T, Finset.mem_erase, Set.Finite.mem_toFinset]
  have hT : ∀ P' ∈ T, P' ∈ (Ideal.span {π}).minimalPrimes ∧ P' ≠ P := fun P' h =>
    ⟨((hTiff P').mp h).2, ((hTiff P').mp h).1⟩
  have hsP' : ∀ P' : Ideal S, ∃ s : R, P' ∈ T → (s ∈ P'.comap φ ∧ s ∉ Q) := by
    intro P'
    by_cases hP'T : P' ∈ T
    · obtain ⟨hm, hne⟩ := hT P' hP'T
      by_contra h
      push Not at h
      exact h1 P' hm hne (fun s hs => (h s).2 hs)
    · exact ⟨1, fun h => absurd h hP'T⟩
  choose sf hsf using hsP'
  let s : R := ∏ P' ∈ T, sf P'
  have hsQ : s ∉ Q := by
    intro hs
    obtain ⟨P', hP'T, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (p := Q)).mp hs
    exact (hsf P' hP'T).2 hmem
  have hsP : ∀ P' ∈ T, φ s ∈ P' := fun P' h => by
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem sf h
    show φ (∏ P' ∈ T, sf P') ∈ P'
    rw [ht, map_mul]
    exact Ideal.mul_mem_right _ _ (hsf P' h).1
  have hσP : φ s ∉ P := fun h => hsQ (by rw [hQdef, Ideal.mem_comap]; exact h)

  have hrad' : Ideal.span {π} = sInf (Ideal.span {π}).minimalPrimes := by
    rw [Ideal.sInf_minimalPrimes]; exact hrad.radical.symm
  have h3 : ∀ x : S, x * φ s ∈ Ideal.span {π} ↔ x ∈ P := by
    intro x
    constructor
    · intro hx
      exact (hPprime.mem_or_mem (hP.1.2 hx)).resolve_right hσP
    · intro hx
      rw [hrad', Ideal.mem_sInf]
      intro P' hP'
      by_cases hP'P : P' = P
      · subst hP'P; exact Ideal.mul_mem_right _ _ hx
      · have hP'T : P' ∈ T := (hTiff P').mpr ⟨hP'P, hP'⟩
        exact Ideal.mul_mem_left _ _ (hsP P' hP'T)

  apply le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl)
  intro x hx

  have hxs : φ s * x ∈ Q.map φ := by
    rw [mul_comm]
    have : Ideal.span {π} ≤ Q.map φ := by
      rw [Ideal.span_singleton_le_iff_mem, ← hφr]
      apply Ideal.mem_map_of_mem
      show r ∈ Q
      rw [hQdef, Ideal.mem_comap, hφr]; exact hπP
    exact this ((h3 x).mpr hx)

  let ε := TensorProduct.quotTensorEquivQuotSMul S Q
  have hQS : (Q • (⊤ : Submodule R S)) = (Q.map φ).restrictScalars R := Ideal.smul_top_eq_map Q
  have hzero : ∀ y : S, y ∈ Q.map φ → ((1 : R ⧸ Q) ⊗ₜ[R] y : (R ⧸ Q) ⊗[R] S) = 0 := by
    intro y hy
    apply ε.injective
    rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hQS]
    exact hy
  have hsbar : (Ideal.Quotient.mk Q s) ≠ 0 := fun h => hsQ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hreg : IsSMulRegular ((R ⧸ Q) ⊗[R] S) (Ideal.Quotient.mk Q s) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (M := (R ⧸ Q) ⊗[R] S) (mem_nonZeroDivisors_of_ne_zero hsbar)
  have hkey : (Ideal.Quotient.mk Q s) • ((1 : R ⧸ Q) ⊗ₜ[R] x : (R ⧸ Q) ⊗[R] S) = 0 := by
    have e1 : (Ideal.Quotient.mk Q s) • ((1 : R ⧸ Q) ⊗ₜ[R] x : (R ⧸ Q) ⊗[R] S) =
        ((s • (1 : R ⧸ Q)) ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one]
    rw [e1, TensorProduct.smul_tmul, Algebra.smul_def, hφ]
    exact hzero _ hxs
  have h10 : ((1 : R ⧸ Q) ⊗ₜ[R] x : (R ⧸ Q) ⊗[R] S) = 0 :=
    hreg (show (Ideal.Quotient.mk Q s) • ((1 : R ⧸ Q) ⊗ₜ[R] x : (R ⧸ Q) ⊗[R] S) =
      (Ideal.Quotient.mk Q s) • (0 : (R ⧸ Q) ⊗[R] S) by rw [hkey, smul_zero])
  have hx0 : ε ((1 : R ⧸ Q) ⊗ₜ[R] x) = 0 := by rw [h10, map_zero]
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hQS] at hx0
  exact hx0

end B1aSol

theorem solution
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (S : Type) [CommRing S] [IsNoetherianRing S]
    (e : AdicCompletion (maximalIdeal R) R ≃+* S)
    (r : R) (π : S) (hπ : e (algebraMap R (AdicCompletion (maximalIdeal R) R) r) = π)
    (hrad : (Ideal.span {π}).IsRadical)
    (P : Ideal S) (hP : P ∈ (Ideal.span {π}).minimalPrimes)
    (huniq : ∀ P' ∈ (Ideal.span {π}).minimalPrimes,
      P'.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
        P.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) →
      P' = P) :
    (P.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R)))).map
      ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) = P :=
  B1aSol.main R S e r π hπ hrad P hP huniq

end S_IsLocalRing_map_comap_eq_of_minimalPrimes_span_of_ringEquiv_adicCompletion
end P2MW
export P2MW.S_IsLocalRing_map_comap_eq_of_minimalPrimes_span_of_ringEquiv_adicCompletion (solution)
