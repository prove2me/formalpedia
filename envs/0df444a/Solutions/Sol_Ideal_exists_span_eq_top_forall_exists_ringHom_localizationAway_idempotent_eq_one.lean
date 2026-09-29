-- Prove2me | solution 1 for Ideal.exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b2467738-006b-5f73-9ecb-feb6ff740ebe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one

set_option autoImplicit false

open scoped BigOperators

namespace CoverRefine29

theorem eq_one_of_idem_unit {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) (hu : IsUnit e) : e = 1 := by
  have : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have := hu.mul_left_cancel (this.trans (mul_zero e).symm)
  exact sub_eq_zero.mp this

end CoverRefine29

open CoverRefine29 in
theorem solution
    {S : Type} [CommRing S] {m : ℕ} (r : Fin m → S) (hr : Ideal.span (Set.range r) = ⊤)
    (k : Fin m → ℕ) (ε : ∀ a : Fin m, Fin (k a) → Localization.Away (r a))
    (hε₁ : ∀ a i, IsIdempotentElem (ε a i)) (hε₂ : ∀ a, ∑ i, ε a i = 1)
    (hε₃ : ∀ a i j, i ≠ j → ε a i * ε a j = 0) :
    ∃ (m' : ℕ) (t : Fin m' → S), Ideal.span (Set.range t) = ⊤ ∧
      ∀ b : Fin m', ∃ (a : Fin m) (i : Fin (k a)) (ρ : Localization.Away (r a) →+* Localization.Away (t b)),
        ρ.comp (algebraMap S (Localization.Away (r a))) = algebraMap S (Localization.Away (t b)) ∧
        ρ (ε a i) = 1 ∧ ∀ j : Fin (k a), j ≠ i → ρ (ε a j) = 0 := by
  classical

  let s : ∀ a : Fin m, Fin (k a) → S := fun a i => (IsLocalization.Away.sec (r a) (ε a i)).1
  let n : ∀ a : Fin m, Fin (k a) → ℕ := fun a i => (IsLocalization.Away.sec (r a) (ε a i)).2
  have hsec : ∀ a i, ε a i * algebraMap S (Localization.Away (r a)) (r a ^ n a i) =
      algebraMap S (Localization.Away (r a)) (s a i) := fun a i => IsLocalization.Away.sec_spec (r a) (ε a i)

  let ι := Σ a : Fin m, Fin (k a)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let t : Fin (Fintype.card ι) → S := fun b => r (e.symm b).1 * s (e.symm b).1 (e.symm b).2
  have ht : ∀ a i, t (e ⟨a, i⟩) = r a * s a i := fun a i => by
    show r (e.symm (e ⟨a, i⟩)).1 * s (e.symm (e ⟨a, i⟩)).1 (e.symm (e ⟨a, i⟩)).2 = r a * s a i
    rw [Equiv.symm_apply_apply]

  have hpow : ∀ a : Fin m, ∃ N : ℕ, r a ^ N ∈ Ideal.span (Set.range t) := by
    intro a
    set L := Localization.Away (r a) with hL
    set M : ℕ := ∑ i, n a i with hM
    have hle : ∀ i, n a i ≤ M := fun i => by
      rw [hM]; exact Finset.single_le_sum (f := fun i => n a i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h1 : ∀ i, ε a i * algebraMap S L (r a ^ M) = algebraMap S L (s a i * r a ^ (M - n a i)) := by
      intro i
      rw [map_mul, ← hsec a i, mul_assoc, ← map_mul, ← pow_add, Nat.add_sub_cancel' (hle i)]
    have h2 : algebraMap S L (r a ^ M) = algebraMap S L (∑ i, s a i * r a ^ (M - n a i)) := by
      rw [map_sum, ← Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_mul, hε₂ a, one_mul]
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (r a)) L).mp h2
    obtain ⟨K, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hc
    refine ⟨K + M + 1, ?_⟩
    have : r a ^ (K + M + 1) = ∑ i, (r a * s a i) * (r a ^ K * r a ^ (M - n a i)) := by
      rw [pow_succ, pow_add, show r a ^ K * r a ^ M = r a ^ K * ∑ i, s a i * r a ^ (M - n a i) from hc',
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨e ⟨a, i⟩, ht a i⟩)

  have hspan : Ideal.span (Set.range t) = ⊤ := by
    choose N hN using hpow
    set Nmax := Finset.univ.sup N with hNmax
    have hNle : ∀ a, N a ≤ Nmax := fun a => Finset.le_sup (f := N) (Finset.mem_univ a)
    rw [eq_top_iff, ← Ideal.span_pow_eq_top (Set.range r) hr Nmax]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    show r a ^ Nmax ∈ Ideal.span (Set.range t)
    have : r a ^ Nmax = r a ^ (Nmax - N a) * r a ^ N a := by rw [← pow_add, Nat.sub_add_cancel (hNle a)]
    rw [this]
    exact Ideal.mul_mem_left _ _ (hN a)
  refine ⟨Fintype.card ι, t, hspan, fun b => ?_⟩
  set a := (e.symm b).1 with ha
  set i := (e.symm b).2 with hi
  have htb : t b = r a * s a i := rfl
  set L := Localization.Away (r a) with hL
  set T := Localization.Away (t b) with hT
  have hunit_t : IsUnit (algebraMap S T (t b)) := IsLocalization.Away.algebraMap_isUnit (t b)
  have hunit_rs : IsUnit (algebraMap S T (r a) * algebraMap S T (s a i)) := by
    rw [← map_mul, ← htb]; exact hunit_t
  have hunit_r : IsUnit (algebraMap S T (r a)) := isUnit_of_mul_isUnit_left hunit_rs
  have hunit_s : IsUnit (algebraMap S T (s a i)) := isUnit_of_mul_isUnit_right hunit_rs
  let ρ : L →+* T := IsLocalization.Away.lift (r a) (g := algebraMap S T) hunit_r
  have hρ : ∀ x : S, ρ (algebraMap S L x) = algebraMap S T x := fun x => IsLocalization.Away.lift_eq (r a) hunit_r x
  have hρcomp : ρ.comp (algebraMap S L) = algebraMap S T := RingHom.ext hρ

  have hρi : ρ (ε a i) = 1 := by
    apply eq_one_of_idem_unit ((hε₁ a i).map ρ)
    have h := congrArg ρ (hsec a i)
    rw [map_mul, hρ, hρ, map_pow] at h
    have hu : IsUnit (ρ (ε a i) * algebraMap S T (r a) ^ n a i) := by rw [h]; exact hunit_s
    exact isUnit_of_mul_isUnit_left hu
  refine ⟨a, i, ρ, hρcomp, hρi, fun j hj => ?_⟩
  rw [← mul_one (ρ (ε a j)), ← hρi, ← map_mul, hε₃ a j i hj, map_zero]

end S_Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one
end P2MW
export P2MW.S_Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one (solution)
