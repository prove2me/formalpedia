-- Prove2me | solution 1 for IsLocalRing.exists_ideal_finite_quotient_forall_mem_span_singleton_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/56270bc3-bfc1-5c64-a0a1-3132185a0363

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ideal_finite_quotient_forall_mem_span_singleton_of_mem_maximalIdeal

set_option autoImplicit false

private theorem K4Aux.finite_quotient_of_maximalIdeal_pow_le
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Finite (IsLocalRing.ResidueField A)] (n : ℕ) (I : Ideal A)
    (hle : IsLocalRing.maximalIdeal A ^ n ≤ I) : Finite (A ⧸ I) := by
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) := ‹Finite (IsLocalRing.ResidueField A)›
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A)) n
  let g : A ⧸ IsLocalRing.maximalIdeal A ^ n →+* A ⧸ I :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A ^ n) (Ideal.Quotient.mk I)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha))
  have hg : (g ∘ Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) = Ideal.Quotient.mk I := by
    funext a
    rfl
  have hsurj : Function.Surjective g := by
    apply Function.Surjective.of_comp (g := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n))
    rw [hg]
    exact Ideal.Quotient.mk_surjective
  exact Finite.of_surjective g hsurj

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Finite (IsLocalRing.ResidueField A)]
    {ι : Type} (f : ι → A) (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal A) (hf0 : ∃ i, f i ≠ 0) :
    ∃ (I : Ideal A) (t : A ⧸ I), I ≤ IsLocalRing.maximalIdeal A ∧ Finite (A ⧸ I) ∧ t ≠ 0 ∧
      (∃ a ∈ IsLocalRing.maximalIdeal A, Ideal.Quotient.mk I a = t) ∧
      (∀ m ∈ IsLocalRing.maximalIdeal A, t * Ideal.Quotient.mk I m = 0) ∧
      (∀ i, Ideal.Quotient.mk I (f i) ∈ Ideal.span {t}) ∧
      (∃ i, Ideal.Quotient.mk I (f i) ≠ 0) := by
  classical
  set m := IsLocalRing.maximalIdeal A with hm_def

  have hKrull : ⨅ k : ℕ, m ^ k = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing m (IsLocalRing.maximalIdeal.isMaximal A).ne_top

  have hP : ∃ k : ℕ, ∃ i, f i ∉ m ^ (k + 2) := by
    obtain ⟨i, hi⟩ := hf0
    by_contra h
    push Not at h
    apply hi
    have hmem : f i ∈ ⨅ k : ℕ, m ^ k := by
      refine Submodule.mem_iInf _ |>.mpr fun k => ?_
      exact Ideal.pow_le_pow_right (by omega) (h k i)
    rwa [hKrull, Submodule.mem_bot] at hmem

  obtain ⟨n, hall, i₀, hi₀⟩ : ∃ n : ℕ, (∀ i, f i ∈ m ^ (n + 1)) ∧ ∃ i, f i ∉ m ^ (n + 2) := by
    refine ⟨Nat.find hP, ?_, Nat.find_spec hP⟩
    intro i
    rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hP) with h0 | hs
    · rw [h0, zero_add, pow_one]
      exact hf i
    · have hlt : Nat.find hP - 1 < Nat.find hP := by omega
      have hmin := Nat.find_min hP hlt
      push Not at hmin
      have := hmin i
      rwa [show Nat.find hP - 1 + 2 = Nat.find hP + 1 by omega] at this

  obtain ⟨I, ⟨hleI, hIm, hi₀I⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian A A)
      {I : Ideal A | m ^ (n + 2) ≤ I ∧ I ≤ m ∧ f i₀ ∉ I}
      ⟨m ^ (n + 2), le_rfl, Ideal.pow_le_self (by omega), hi₀⟩
  have hfin : Finite (A ⧸ I) := K4Aux.finite_quotient_of_maximalIdeal_pow_le (n + 2) I hleI
  refine ⟨I, Ideal.Quotient.mk I (f i₀), hIm, hfin, ?_, ⟨f i₀, hf i₀, rfl⟩, ?_, ?_, ⟨i₀, ?_⟩⟩
  · exact fun h => hi₀I (Ideal.Quotient.eq_zero_iff_mem.mp h)
  · intro x hx
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply hleI
    rw [pow_succ]
    exact Ideal.mul_mem_mul (hall i₀) hx
  · intro j
    by_cases hj : f j ∈ I
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr hj]
      exact Submodule.zero_mem _
    ·
      have hJ : f i₀ ∈ I ⊔ Ideal.span {f j} := by
        by_contra hcon
        apply hmax (I ⊔ Ideal.span {f j})
          ⟨le_trans hleI le_sup_left,
            sup_le hIm ((Ideal.span_singleton_le_iff_mem _).mpr (hf j)), hcon⟩
        refine SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, f j, ?_, hj⟩
        exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hJ
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz

      have ha : IsUnit a := by
        by_contra hna
        apply hi₀I
        rw [← hyz]
        refine I.add_mem hy (hleI ?_)
        rw [pow_succ']
        exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal a).mpr hna) (hall j)
      obtain ⟨u, rfl⟩ := ha
      have hq : Ideal.Quotient.mk I (f i₀) =
          Ideal.Quotient.mk I ↑u * Ideal.Quotient.mk I (f j) := by
        rw [← hyz, map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_add]
      refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk I ↑u⁻¹, ?_⟩
      rw [hq, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · exact fun h => hi₀I (Ideal.Quotient.eq_zero_iff_mem.mp h)

end S_IsLocalRing_exists_ideal_finite_quotient_forall_mem_span_singleton_of_mem_maximalIdeal
end P2MW
export P2MW.S_IsLocalRing_exists_ideal_finite_quotient_forall_mem_span_singleton_of_mem_maximalIdeal (solution)
