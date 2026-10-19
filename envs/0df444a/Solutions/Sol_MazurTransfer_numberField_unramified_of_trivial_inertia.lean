-- Prove2me | solution 1 for MazurTransfer.numberField_unramified_of_trivial_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T11:10:21.147025+00:00
-- url     : https://prove2.me/submissions/5928eefe-d5ab-4758-9564-6321b0b94a3c

/- Copyright (c) 2026 Vas and contributors. Apache-2.0. Design boundary: original number-field integer rings are unramified from trivial ideal inertia. Named downstream consumer: the same cyclic19 character cutout in pi descent. -/
import Theorems.Thm_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable
noncomputable section
open scoped NumberField

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (hI : ∀ (Q : Ideal (𝓞 L)) [Q.IsMaximal], Q.inertia (L ≃ₐ[K] L) = ⊥) :
    Algebra.Unramified (𝓞 K) (𝓞 L) := by
  letI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ K L
  apply Algebra.unramified_iff_forall.mpr
  intro Q
  letI := Q.isPrime
  by_cases hQ : Q.asIdeal = ⊥
  · simpa only [hQ] using (Algebra.isUnramifiedAt_bot (R := 𝓞 K) (S := 𝓞 L))
  letI : Q.asIdeal.IsMaximal := Q.isPrime.isMaximal hQ
  let p := Q.asIdeal.under (𝓞 K)
  letI : p.IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q.asIdeal
  have hp : p ≠ ⊥ := (p.bot_lt_of_maximal (NumberField.RingOfIntegers.not_isField K)).ne'
  have he := (Ideal.inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable (L ≃ₐ[K] L) hp Q.asIdeal).mp (hI Q.asIdeal)
  have hram : Q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p Q.asIdeal (L ≃ₐ[K] L)]
    exact he.1
  exact Ideal.ramificationIdx_eq_one_iff.mp hram


#print axioms solution
