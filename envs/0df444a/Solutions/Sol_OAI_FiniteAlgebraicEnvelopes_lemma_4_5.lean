-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T16:16:15.559981+00:00
-- url     : https://prove2.me/submissions/e492e64b-61be-493d-bac4-7a6d58eee281

import Mathlib
import Definitions.Def_BooneHigman_Steinberg
import Definitions.Def_BooneHigman_cornerSub

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

theorem steinberg_x_add (i j : Fin n) (hij : i ≠ j) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x i j hij b = SteinbergGroup.x i j hij (a + b) := by
  have hmem : steinAddRelator (⟨i, j, hij, a, b⟩ : SteinAddParam n R) ∈ steinRelations n R :=
    Or.inl (Or.inl (Set.mem_range_self _))
  have h1 := PresentedGroup.one_of_mem hmem
  unfold steinAddRelator at h1
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem steinberg_x_chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x j k hjk b *
        (SteinbergGroup.x i j hij a)⁻¹ * (SteinbergGroup.x j k hjk b)⁻¹ =
      SteinbergGroup.x i k hik (a * b) := by
  have hmem : steinChainRelator (⟨i, j, k, hij, hjk, hik, a, b⟩ : SteinChainParam n R) ∈
      steinRelations n R := Or.inl (Or.inr (Set.mem_range_self _))
  have h1 := PresentedGroup.one_of_mem hmem
  unfold steinChainRelator at h1
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem steinberg_x_zero (i j : Fin n) (hij : i ≠ j) :
    SteinbergGroup.x i j hij (0 : R) = 1 := by
  have h := steinberg_x_add i j hij (0 : R) (0 : R)
  rw [add_zero] at h
  calc SteinbergGroup.x i j hij (0 : R)
      = (SteinbergGroup.x i j hij (0 : R))⁻¹ *
        (SteinbergGroup.x i j hij (0 : R) * SteinbergGroup.x i j hij (0 : R)) := by group
    _ = (SteinbergGroup.x i j hij (0 : R))⁻¹ * SteinbergGroup.x i j hij (0 : R) := by rw [h]
    _ = 1 := by group

theorem commute_of_comm_eq_one {G : Type*} [Group G] {u v : G} (h : u * v * u⁻¹ * v⁻¹ = 1) :
    Commute u v := by
  show u * v = v * u
  calc u * v = u * v * u⁻¹ * v⁻¹ * v * u := by group
    _ = v * u := by rw [h]; group

theorem commute_of_comm_eq_one' {G : Type*} [Group G] {u v : G} (h : v * u * v⁻¹ * u⁻¹ = 1) :
    Commute u v := (commute_of_comm_eq_one h).symm

/-- Commuting with both factors of a commutator implies commuting with the commutator. -/
theorem commute_commutator {G : Type*} [Group G] {u v w : G} (h1 : Commute u v) (h2 : Commute u w) :
    Commute u (v * w * v⁻¹ * w⁻¹) :=
  ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right

section Lemma45

variable (E F : R) (hEF : E * F = 0) (hFE : F * E = 0) (hE : E * E = E)
  (hex : ∀ i j : Fin n, i ≠ j → ∃ k0 : Fin n, k0 ≠ i ∧ k0 ≠ j)

include hEF hFE hE hex in
/-- Generators `x_ij(EsE)` and `x_i'j'(FtF)` commute, for any index pairs. -/
theorem x_commute_corner (i j : Fin n) (hij : i ≠ j) (i' j' : Fin n) (hi'j' : i' ≠ j')
    (s t : R) :
    Commute (SteinbergGroup.x i j hij (E * s * E)) (SteinbergGroup.x i' j' hi'j' (F * t * F)) := by
  set a := E * s * E with ha_def
  set c := F * t * F with hc_def
  have hac : a * c = 0 := by
    have step : a * c = E * s * (E * F) * t * F := by rw [ha_def, hc_def]; noncomm_ring
    rw [step, hEF]; noncomm_ring
  have hca : c * a = 0 := by
    have step : c * a = F * t * (F * E) * s * E := by rw [ha_def, hc_def]; noncomm_ring
    rw [step, hFE]; noncomm_ring
  rcases eq_or_ne i j' with hij' | hij'
  · rcases eq_or_ne j i' with hji | hji
    · -- full reversal: i' = j, j' = i
      subst hij'
      subst hji
      obtain ⟨k0, hk0i, hk0j⟩ := hex i j hij
      have haE : a * E = a := by
        have step : a * E = E * s * (E * E) := by rw [ha_def]; noncomm_ring
        rw [step, hE, ← ha_def]
      have hEc : E * c = 0 := by
        have step : E * c = (E * F) * t * F := by rw [hc_def]; noncomm_ring
        rw [step, hEF]; noncomm_ring
      have hdecomp : SteinbergGroup.x i j hij a =
          SteinbergGroup.x i k0 hk0i.symm a * SteinbergGroup.x k0 j hk0j E *
            (SteinbergGroup.x i k0 hk0i.symm a)⁻¹ * (SteinbergGroup.x k0 j hk0j E)⁻¹ := by
        rw [steinberg_x_chain i k0 j hk0i.symm hk0j hij a E, haE]
      have hc1 : Commute (SteinbergGroup.x j i hi'j' c) (SteinbergGroup.x i k0 hk0i.symm a) := by
        apply commute_of_comm_eq_one
        rw [steinberg_x_chain j i k0 hij.symm hk0i.symm hk0j.symm c a, hca, steinberg_x_zero]
      have hc2 : Commute (SteinbergGroup.x j i hi'j' c) (SteinbergGroup.x k0 j hk0j E) := by
        apply commute_of_comm_eq_one'
        have h1 := steinberg_x_chain k0 j i hk0j hij.symm hk0i E c
        rw [h1, hEc, steinberg_x_zero]
      rw [hdecomp]
      exact (commute_commutator hc1 hc2).symm
    · -- backward chain: i = j', j ≠ i'
      subst hij'
      apply commute_of_comm_eq_one'
      rw [steinberg_x_chain i' i j hi'j' hij hji.symm c a, hca, steinberg_x_zero]
  · rcases eq_or_ne j i' with hji | hji
    · -- forward chain: j = i', i ≠ j'
      subst hji
      apply commute_of_comm_eq_one
      rw [steinberg_x_chain i j j' hij hi'j' hij' a c, hac, steinberg_x_zero]
    · -- disjoint
      exact steinberg_x_commute i j i' j' hij hi'j' hij' hji a c

include hEF hFE hE hex in
theorem commute_gen_cornerSub_F (i j : Fin n) (hij : i ≠ j) (s : R)
    (y : SteinbergGroup n R) (hy : y ∈ cornerSub F) :
    Commute (SteinbergGroup.x i j hij (E * s * E)) y := by
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨i', j', hi'j', t, rfl⟩ := hz
      exact x_commute_corner E F hEF hFE hE hex i j hij i' j' hi'j' s t
  | one => exact Commute.one_right _
  | mul z w _ _ ihz ihw => exact ihz.mul_right ihw
  | inv z _ ihz => exact ihz.inv_right

include hEF hFE hE hex in
theorem lemma_4_5 (x : SteinbergGroup n R) (hx : x ∈ cornerSub E)
    (y : SteinbergGroup n R) (hy : y ∈ cornerSub F) :
    x * y = y * x := by
  suffices h : Commute x y from h
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨i, j, hij, s, rfl⟩ := hz
      exact commute_gen_cornerSub_F E F hEF hFE hE hex i j hij s y hy
  | one => exact Commute.one_left _
  | mul z w _ _ ihz ihw => exact ihz.mul_left ihw
  | inv z _ ihz => exact ihz.inv_left

end Lemma45

end FiniteAlgebraicEnvelopes
end OAI

open OAI.FiniteAlgebraicEnvelopes

universe u

theorem solution {n : ℕ} {R : Type u} [Ring R] (E F : R) (hEF : E * F = 0) (hFE : F * E = 0)
    (hE : E * E = E)
    (hex : ∀ i j : Fin n, i ≠ j → ∃ k0 : Fin n, k0 ≠ i ∧ k0 ≠ j)
    (x : SteinbergGroup n R) (hx : x ∈ cornerSub E)
    (y : SteinbergGroup n R) (hy : y ∈ cornerSub F) :
    x * y = y * x :=
  OAI.FiniteAlgebraicEnvelopes.lemma_4_5 E F hEF hFE hE hex x hx y hy
