-- Prove2me | solution 1 for Ideal.exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/42a56841-7cb5-57e1-8726-abf32b9bf3b9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType

set_option autoImplicit false

universe u v

open IsLocalRing

namespace PointChoice

theorem isJacobsonRing_of_field (K : Type u) [Field K] : IsJacobsonRing K := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  have hPbot : P = ⊥ := by
    rcases Ideal.eq_bot_or_top P with h | h
    · exact h
    · exact absurd h hP.ne_top
  subst hPbot
  refine le_antisymm ?_ Ideal.le_jacobson
  exact sInf_le ⟨le_rfl, Ideal.bot_isMaximal⟩

theorem mem_of_forall_isMaximal_mem
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (𝔪₀ : Ideal R) [𝔪₀.IsMaximal] (𝔮 : Ideal A) [𝔮.IsPrime] (h𝔮 : Ideal.map (algebraMap R A) 𝔪₀ ≤ 𝔮)
    (a : A) (ha : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔮 ≤ 𝔪 → a ∈ 𝔪) : a ∈ 𝔮 := by
  classical

  have hcm : 𝔮.comap (algebraMap R A) = 𝔪₀ := by
    have hle : 𝔪₀ ≤ 𝔮.comap (algebraMap R A) := by
      rw [← Ideal.map_le_iff_le_comap]; exact h𝔮
    exact ((Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _ Ideal.IsPrime.ne_top') hle)).symm
  haveI : (𝔮.comap (algebraMap R A)).IsMaximal := hcm ▸ inferInstance
  letI : Field (R ⧸ 𝔮.comap (algebraMap R A)) := Ideal.Quotient.field _
  haveI : IsJacobsonRing (R ⧸ 𝔮.comap (algebraMap R A)) := isJacobsonRing_of_field _
  haveI : Algebra.FiniteType R (A ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R 𝔮) (Ideal.Quotient.mkₐ_surjective R 𝔮)
  haveI : Algebra.FiniteType (R ⧸ 𝔮.comap (algebraMap R A)) (A ⧸ 𝔮) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ 𝔮.comap (algebraMap R A)) (A ⧸ 𝔮)
  haveI hJ : IsJacobsonRing (A ⧸ 𝔮) := isJacobsonRing_of_finiteType (A := R ⧸ 𝔮.comap (algebraMap R A))

  have hbot : (⊥ : Ideal (A ⧸ 𝔮)).jacobson = ⊥ :=
    (isJacobsonRing_iff_prime_eq.mp hJ) ⊥ Ideal.isPrime_bot
  have hmk : Ideal.Quotient.mk 𝔮 a ∈ (⊥ : Ideal (A ⧸ 𝔮)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    have hM' : (M.comap (Ideal.Quotient.mk 𝔮)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hle : 𝔮 ≤ M.comap (Ideal.Quotient.mk 𝔮) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact M.zero_mem
    exact ha _ hM' hle
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmk
  exact hmk

end PointChoice

open PointChoice in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (𝔪₀ : Ideal R) [𝔪₀.IsMaximal]
    (I : Ideal A) (hI : Ideal.map (algebraMap R A) 𝔪₀ ≤ I)
    (𝔮 : Ideal A) (h𝔮 : 𝔮 ∈ I.minimalPrimes) (hnm : ¬ 𝔮.IsMaximal)

    (hdim : ∀ P : Ideal A, P.IsPrime → 𝔮 < P → P.IsMaximal) :
    ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ 𝔮 ≤ 𝔪 ∧ ∀ 𝔮' ∈ I.minimalPrimes, 𝔮' ≤ 𝔪 → 𝔮' = 𝔮 := by
  classical
  haveI h𝔮p : 𝔮.IsPrime := h𝔮.1.1
  have hI𝔮 : I ≤ 𝔮 := h𝔮.1.2

  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing A I
  let S : Finset (Ideal A) := hfin.toFinset.erase 𝔮
  have hS : ∀ 𝔮' ∈ S, 𝔮' ∈ I.minimalPrimes ∧ 𝔮' ≠ 𝔮 := by
    intro 𝔮' h
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at h
    exact ⟨h.2, h.1⟩
  by_contra hcon

  have hbad : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔮 ≤ 𝔪 → ∃ 𝔮' ∈ S, 𝔮' ≤ 𝔪 := by
    intro 𝔪 h𝔪 hle
    by_contra hno
    apply hcon
    refine ⟨𝔪, h𝔪, hle, fun 𝔮' h𝔮' hle' => ?_⟩
    by_contra hne
    apply hno
    refine ⟨𝔮', ?_, hle'⟩
    rw [Finset.mem_erase, Set.Finite.mem_toFinset]
    exact ⟨hne, h𝔮'⟩

  let J : Ideal A := ∏ 𝔮' ∈ S, 𝔮'
  have hJle : ∀ 𝔮' ∈ S, J ≤ 𝔮' := fun 𝔮' h => Ideal.prod_le_inf.trans (Finset.inf_le h)
  have hJ𝔮 : J ≤ 𝔮 := by
    intro a haJ
    refine mem_of_forall_isMaximal_mem 𝔪₀ 𝔮 (hI.trans hI𝔮) a ?_
    intro 𝔪 h𝔪 hle
    obtain ⟨𝔮', h𝔮'S, h𝔮'𝔪⟩ := hbad 𝔪 h𝔪 hle
    exact h𝔮'𝔪 (hJle 𝔮' h𝔮'S haJ)

  obtain ⟨𝔮', h𝔮'S, h𝔮'le⟩ := (Ideal.IsPrime.prod_le h𝔮p).mp hJ𝔮
  obtain ⟨h𝔮'min, hne⟩ := hS 𝔮' h𝔮'S
  apply hne
  exact le_antisymm h𝔮'le (h𝔮.2 ⟨h𝔮'min.1.1, h𝔮'min.1.2⟩ h𝔮'le)

end S_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType
end P2MW
export P2MW.S_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType (solution)
