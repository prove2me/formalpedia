-- Prove2me | solution 1 for GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:41.856615+00:00
-- url     : https://prove2.me/submissions/c12e7d2d-3a12-4155-bba0-28153b4f14ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitFrobeniusIterateProductEq
import Theorems.Thm_GlobalTheory_FrobeniusProduct_exists_adic_limit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrobeniusProduct
namespace GlobalTheory.FrobeniusProduct
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A →
      ∀ (φ : A →+* A) (u : A), IsUnit u →
        (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) →
          ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  intro A _ p hc φ u hu hconv n hn
  haveI := hc
  set I : Ideal A := Ideal.span {(p : A)} with hI
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  obtain ⟨w, hw⟩ : ∃ w : ℕ → A, w = fun k => (⇑φ)^[n * k + (n - 1)] u := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → A, s = fun N => ∏ k ∈ Finset.range N, w k := ⟨_, rfl⟩
  have hwconv : ∀ r, ∃ M, ∀ k ≥ M, w k - 1 ∈ I ^ r := fun r => by
    obtain ⟨M, hM⟩ := hconv r
    exact ⟨M, fun k hk => by rw [hw]; exact hM _ (by nlinarith)⟩
  have hcauchy : ∀ r, ∃ N, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r := by
    intro r
    obtain ⟨M, hM⟩ := hwconv r
    refine ⟨M, fun m hm => ?_⟩
    have e : s (m + 1) - s m = s m * (w m - 1) := by
      simp only [hs, Finset.prod_range_succ]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (hM m hm)
  obtain ⟨c, hc'⟩ := exists_adic_limit I s hcauchy
  have haus : ∀ x : A, (∀ r : ℕ, x ∈ I ^ r) → x = 0 := fun x hx =>
    IsHausdorff.haus (I := I) (M := A) inferInstance x (fun r => by rw [SModEq.zero, hsm]; exact hx r)
  have hmap : ∀ k (x : A) r, x ∈ I ^ r → (⇑φ)^[k] x ∈ I ^ r := by
    intro k x r hx
    have := Ideal.mem_map_of_mem (φ ^ k) hx
    rwa [Ideal.map_pow, hI, Ideal.map_span, Set.image_singleton, map_natCast,
      RingHom.coe_pow] at this
  have hsub : ∀ x y : A, (⇑φ)^[n] (x - y) = (⇑φ)^[n] x - (⇑φ)^[n] y := by
    intro x y; rw [← RingHom.coe_pow]; exact map_sub _ _ _
  have key : ∀ N, (⇑φ)^[n] (s N) * (⇑φ)^[n - 1] u = s (N + 1) := by
    intro N
    simp only [hs, Finset.prod_range_succ']
    rw [← RingHom.coe_pow, map_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      simp only [RingHom.coe_pow, hw]
      rw [← Function.iterate_add_apply]
      congr 1
      ring
    · simp [hw]
  have hwunit : ∀ k, IsUnit (w k) := fun k => by
    rw [hw]; show IsUnit ((⇑φ)^[n * k + (n - 1)] u)
    rw [← RingHom.coe_pow]; exact hu.map _
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hc' 1
    have h1 : s N - c ∈ I := by simpa using hN N le_rfl
    have hsN : IsUnit (s N) := by
      rw [hs]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun k _ => hwunit k)
    obtain ⟨v, hv⟩ := hsN
    have hy : -(s N - c) ∈ (⊥ : Ideal A).jacobson :=
      IsAdicComplete.le_jacobson_bot I (I.neg_mem h1)
    have hu' := (Ideal.mem_jacobson_bot.mp hy) (↑v⁻¹ : A)
    have heq : c = (-(s N - c) * (↑v⁻¹ : A) + 1) * ↑v := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hv]; ring
    rw [heq]
    exact hu'.mul v.isUnit
  · refine sub_eq_zero.mp (haus _ fun r => ?_)
    obtain ⟨N, hN⟩ := hc' r
    have e : (⇑φ)^[n] c * (⇑φ)^[n - 1] u - c =
        -((⇑φ)^[n] (s N - c) * (⇑φ)^[n - 1] u) + (s (N + 1) - c) := by
      rw [← key N, hsub]; ring
    rw [e]
    exact (I ^ r).add_mem ((I ^ r).neg_mem (Ideal.mul_mem_right _ _ (hmap n _ r (hN N le_rfl))))
      (hN (N + 1) (by omega))
end GlobalTheory.FrobeniusProduct
