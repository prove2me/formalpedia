-- Prove2me | solution 1 for IsLocalization.Away.exists_span_range_mul_eq_top_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/42dd973f-61d9-5294-9adc-e64c442b7602

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalization_Away_exists_span_range_mul_eq_top_of_span_eq_top

set_option autoImplicit false

universe u

theorem solution
    {B : Type u} [CommRing B] {n : ℕ} (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
    (m : Fin n → ℕ) (g : ∀ i, Fin (m i) → L i) (hg : ∀ i, Ideal.span (Set.range (g i)) = ⊤) :
    ∃ (b : ∀ i, Fin (m i) → B) (e : ∀ i, Fin (m i) → ℕ),
      (∀ i k, algebraMap B (L i) (b i k) = g i k * algebraMap B (L i) (f i) ^ (e i k)) ∧
      Ideal.span (Set.range (fun ik : (Σ i : Fin n, Fin (m i)) => f ik.1 * b ik.1 ik.2)) = ⊤ := by
  classical

  choose e b hb using fun (i : Fin n) (k : Fin (m i)) => IsLocalization.Away.surj (f i) (g i k)
  refine ⟨b, e, fun i k => (hb i k).symm, ?_⟩
  set J : Ideal B := Ideal.span (Set.range (fun ik : (Σ i : Fin n, Fin (m i)) => f ik.1 * b ik.1 ik.2)) with hJ

  have hmap : ∀ i, Ideal.map (algebraMap B (L i)) (Ideal.span (Set.range (b i))) = ⊤ := by
    intro i
    rw [eq_top_iff, ← hg i, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have hu : IsUnit (algebraMap B (L i) (f i) ^ (e i k)) :=
      (IsLocalization.Away.algebraMap_isUnit (f i)).pow _
    rw [SetLike.mem_coe, ← Ideal.mul_unit_mem_iff_mem _ hu, hb i k]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨k, rfl⟩)

  have hpow : ∀ i, ∃ N : ℕ, f i ^ N ∈ J := by
    intro i
    have h1 : (1 : L i) ∈ Ideal.map (algebraMap B (L i)) (Ideal.span (Set.range (b i))) := by
      rw [hmap i]; trivial
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (f i)) (L i)).mp h1
    obtain ⟨t, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
    simp only [one_mul] at h

    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f i)) (L i)).mp h
    obtain ⟨v, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hc

    refine ⟨v + t + 1, ?_⟩
    have hmem : f i ^ v * f i ^ t ∈ Ideal.span (Set.range (b i)) := by
      simp only at hc'
      rw [hc']
      exact Ideal.mul_mem_left _ _ ha
    have hprod : Ideal.span {f i} * Ideal.span (Set.range (b i)) ≤ J := by
      rw [Ideal.span_mul_span']
      apply Ideal.span_le.mpr
      rintro _ ⟨x, hx, y, ⟨k, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff.mp hx]
      exact Ideal.subset_span ⟨⟨i, k⟩, rfl⟩
    have : f i ^ (v + t + 1) = f i * (f i ^ v * f i ^ t) := by ring
    rw [this]
    exact hprod (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hmem)

  choose N hN using hpow
  let M : ℕ := Finset.univ.sup N
  have hNM : ∀ i, f i ^ M ∈ J := by
    intro i
    have hle : N i ≤ M := Finset.le_sup (Finset.mem_univ i)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add]
    exact Ideal.mul_mem_right _ _ (hN i)
  have htop := Ideal.span_pow_eq_top (Set.range f) hf M
  rw [eq_top_iff, ← htop, Ideal.span_le]
  rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
  exact hNM i

end S_IsLocalization_Away_exists_span_range_mul_eq_top_of_span_eq_top
end P2MW
export P2MW.S_IsLocalization_Away_exists_span_range_mul_eq_top_of_span_eq_top (solution)
