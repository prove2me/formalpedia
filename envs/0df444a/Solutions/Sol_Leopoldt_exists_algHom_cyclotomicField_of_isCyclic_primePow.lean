-- Prove2me | solution 1 for Leopoldt.exists_algHom_cyclotomicField_of_isCyclic_primePow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:30:33.57195+00:00
-- url     : https://prove2.me/submissions/be894372-7ae8-4933-a1a6-8284134f4248
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Theorems.Thm_NumberField_exists_algHom_cyclotomicField_of_sup
import Theorems.Thm_NumberField_exists_isUnramifiedIn_le_sup_of_prime_ne
import Theorems.Thm_NumberField_exists_algHom_cyclotomicField_prime_pow_of_isUnramifiedIn_of_ne_two
import Theorems.Thm_NumberField_exists_algHom_cyclotomicField_two_pow_of_isUnramifiedIn

open NumberField

theorem NumberField.exists_finset_forall_isUnramifiedIn (K : Type*) [Field K] [NumberField K] :
    ∃ S : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)}) := by
  refine ⟨(discr K).natAbs.primeFactors, fun ℓ hℓ hS => ?_⟩
  rw [← not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hℓ)]
  intro hdvd
  exact hS (Nat.mem_primeFactors.mpr
    ⟨hℓ, Int.natCast_dvd.mp hdvd, by simpa using discr_ne_zero K⟩)

theorem solution (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)] (p k : ℕ) (hp : p.Prime)
    (hK : Module.finrank ℚ K = p ^ k) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  have key : ∀ (S : Finset ℕ) (E : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ E → IsAbelianGalois ℚ E → (∃ m : ℕ, Module.finrank ℚ E = p ^ m) →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ℓ ∉ S →
        Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(ℓ : ℤ)})) →
      ∃ n : ℕ, 0 < n ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro E hfd hab hdeg hunr
      obtain ⟨m, hm⟩ := hdeg
      have : NumberField E := ⟨⟩
      have hunr' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
          Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(ℓ : ℤ)}) :=
        fun ℓ hℓ hne => hunr ℓ hℓ hne (Finset.notMem_empty ℓ)
      rcases eq_or_ne p 2 with rfl | hp2
      · obtain ⟨N, hN⟩ :=
          NumberField.exists_algHom_cyclotomicField_two_pow_of_isUnramifiedIn E m hm hunr'
        exact ⟨2 ^ N, by positivity, hN⟩
      · obtain ⟨N, hN⟩ :=
          NumberField.exists_algHom_cyclotomicField_prime_pow_of_isUnramifiedIn_of_ne_two
            E p m hp hp2 hm hunr'
        exact ⟨p ^ N, pow_pos hp.pos N, hN⟩
    | insert q S hqS ih =>
      intro E hfd hab hdeg hunr
      obtain ⟨m, hm⟩ := hdeg
      by_cases hq : q.Prime ∧ q ≠ p
      · obtain ⟨E', F, hfd', hab', hm', hq', hℓ', hF, hle⟩ :=
          NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne p q hp hq.1 hq.2 E m hm
        have h1 := ih E' hfd' hab' hm' (fun ℓ hℓ hne hS => by
          by_cases hℓq : ℓ = q
          · subst hℓq; exact hq'
          · exact hℓ' ℓ hℓ (hunr ℓ hℓ hne (by simp [hℓq, hS])))
        obtain ⟨n, hn, ⟨g⟩⟩ :=
          NumberField.exists_algHom_cyclotomicField_of_sup E' F h1 ⟨q, hq.1.pos, hF⟩
        exact ⟨n, hn, ⟨g.comp (IntermediateField.inclusion hle)⟩⟩
      · refine ih E hfd hab ⟨m, hm⟩ (fun ℓ hℓ hne hS => hunr ℓ hℓ hne ?_)
        rw [Finset.mem_insert, not_or]
        refine ⟨?_, hS⟩
        rintro rfl
        exact hq ⟨hℓ, hne⟩
  let f : K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let e : K ≃ₐ[ℚ] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : IsAbelianGalois ℚ K := IsAbelianGalois.of_isCyclic ℚ K
  have : FiniteDimensional ℚ f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : IsAbelianGalois ℚ f.fieldRange := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have : NumberField f.fieldRange := ⟨⟩
  have hfr : Module.finrank ℚ f.fieldRange = p ^ k := by
    rw [← hK]; exact e.toLinearEquiv.finrank_eq.symm
  obtain ⟨S, hS⟩ := NumberField.exists_finset_forall_isUnramifiedIn f.fieldRange
  obtain ⟨n, hn, ⟨g⟩⟩ := key S f.fieldRange inferInstance inferInstance ⟨k, hfr⟩
    (fun ℓ hℓ _ hℓS => hS ℓ hℓ hℓS)
  exact ⟨n, hn, ⟨g.comp e.toAlgHom⟩⟩
