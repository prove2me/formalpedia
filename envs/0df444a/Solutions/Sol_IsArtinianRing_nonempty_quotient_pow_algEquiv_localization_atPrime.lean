-- Prove2me | solution 1 for IsArtinianRing.nonempty_quotient_pow_algEquiv_localization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c20c21f9-34b9-57cd-9d7a-8311ac57f320

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsArtinianRing_nonempty_quotient_pow_algEquiv_localization_atPrime

set_option autoImplicit false

open scoped TensorProduct

namespace Ws23
namespace CB4b

theorem main (A : Type*) [CommRing A] [IsArtinianRing A] (𝔫 : Ideal A) [h𝔫 : 𝔫.IsMaximal]
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    Nonempty ((A ⧸ 𝔫 ^ N) ≃ₐ[A] Localization.AtPrime 𝔫) := by
  classical
  let f : A →ₐ[A] Localization.AtPrime 𝔫 := Algebra.ofId A _
  have hf : Function.Surjective f := IsArtinianRing.localization_surjective 𝔫.primeCompl _

  have hcomax : ∀ s : A, s ∉ 𝔫 → Ideal.span {s} ⊔ 𝔫 ^ N = ⊤ := by
    intro s hs
    apply Ideal.sup_pow_eq_top
    have hlt : 𝔫 < Ideal.span {s} ⊔ 𝔫 := by
      refine lt_of_le_of_ne le_sup_right fun h => hs ?_
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self s)
    exact h𝔫.out.2 _ hlt
  have hker : RingHom.ker f = 𝔫 ^ N := by
    ext a
    rw [RingHom.mem_ker]
    change algebraMap A (Localization.AtPrime 𝔫) a = 0 ↔ _
    rw [IsLocalization.map_eq_zero_iff 𝔫.primeCompl]
    constructor
    · rintro ⟨⟨s, hs⟩, hsa⟩
      have h1 : (1 : A) ∈ Ideal.span {s} ⊔ 𝔫 ^ N := by rw [hcomax s hs]; trivial
      obtain ⟨u, hu, n, hn, hun⟩ := Submodule.mem_sup.1 h1
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
      have : a = a * n := by
        calc a = a * (c * s + n) := by rw [hun, mul_one]
          _ = c * (s * a) + a * n := by ring
          _ = a * n := by rw [hsa, mul_zero, zero_add]
      rw [this]
      exact Ideal.mul_mem_left _ _ hn
    · intro ha

      let T : Finset (Ideal A) := (IsArtinianRing.setOf_isMaximal_finite A).toFinset.erase 𝔫
      have hT : ∀ M ∈ T, M.IsMaximal ∧ M ≠ 𝔫 := fun M hM => by
        rw [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hM
        exact ⟨hM.2, hM.1⟩

      have hcop : IsCoprime (∏ M ∈ T, M ^ N) 𝔫 := by
        refine IsCoprime.prod_left fun M hM => ?_
        refine IsCoprime.pow_left ?_
        rw [Ideal.isCoprime_iff_sup_eq]
        exact (hT M hM).1.coprime_of_ne h𝔫 (hT M hM).2
      rw [Ideal.isCoprime_iff_sup_eq] at hcop
      have h1 : (1 : A) ∈ (∏ M ∈ T, M ^ N) ⊔ 𝔫 := by rw [hcop]; trivial
      obtain ⟨s, hs, n, hn, hsn⟩ := Submodule.mem_sup.1 h1
      have hs𝔫 : s ∉ 𝔫 := fun h => h𝔫.ne_top ((Ideal.eq_top_iff_one _).2 (by rw [← hsn]; exact Ideal.add_mem _ h hn))
      refine ⟨⟨s, hs𝔫⟩, ?_⟩

      have hall : (∏ M ∈ T, M ^ N) * 𝔫 ^ N ≤ Ideal.jacobson (⊥ : Ideal A) ^ N := by
        have hprod : (∏ M ∈ T, M ^ N) * 𝔫 ^ N = (∏ M ∈ insert 𝔫 T, M) ^ N := by
          rw [Finset.prod_insert (Finset.notMem_erase 𝔫 _), mul_pow, Finset.prod_pow, mul_comm]
        rw [hprod]
        refine Ideal.pow_right_mono ?_ N
        refine le_trans Ideal.prod_le_inf ?_
        rw [Ideal.jacobson]
        refine le_sInf fun J hJ => Finset.inf_le ?_
        rw [Finset.mem_insert]
        by_cases hJ𝔫 : J = 𝔫
        · exact Or.inl hJ𝔫
        · refine Or.inr ?_
          rw [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
          exact ⟨hJ𝔫, hJ.2⟩
      have hmem : s * a ∈ Ideal.jacobson (⊥ : Ideal A) ^ N := hall (Ideal.mul_mem_mul hs ha)
      rw [hN, Ideal.mem_bot] at hmem
      simpa using hmem
  exact ⟨(Ideal.quotientEquivAlgOfEq A hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hf)⟩

end Ws23.CB4b

theorem solution
    (A : Type*) [CommRing A] [IsArtinianRing A] (𝔫 : Ideal A) [𝔫.IsMaximal]
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    Nonempty ((A ⧸ 𝔫 ^ N) ≃ₐ[A] Localization.AtPrime 𝔫) :=
  Ws23.CB4b.main A 𝔫 N hN

end S_IsArtinianRing_nonempty_quotient_pow_algEquiv_localization_atPrime
end P2MW
export P2MW.S_IsArtinianRing_nonempty_quotient_pow_algEquiv_localization_atPrime (solution)
