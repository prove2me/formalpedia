-- Prove2me | solution 1 for GlobalTheory.fg_localizationAway_span_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:04.808582+00:00
-- url     : https://prove2.me/submissions/3e4c5723-3bbb-49ba-aa06-2191ea1bb854

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Submodule
namespace GlobalTheory
theorem _root_.solution
    {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R)
    [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A']
    (N : Submodule R' A') (hN : N.FG) :
    ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N →
      ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  classical
  obtain ⟨S, rfl⟩ := hN
  have hA : ∀ (c : R) (z : A),
      algebraMap A A' (c • z) = algebraMap R A' c * algebraMap A A' z := by
    intro c z
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have hsurj : ∀ n : A', ∃ e : A, ∃ k : ℕ,
      n * algebraMap R A' g ^ k = algebraMap A A' e := by
    intro n
    obtain ⟨k, e, h⟩ := IsLocalization.Away.surj (algebraMap R A g) n
    exact ⟨e, k, by rw [IsScalarTower.algebraMap_apply R A A']; exact h⟩
  choose e k he using hsurj
  refine ⟨S.image e, ?_⟩
  have key : ∀ y ∈ Submodule.span R' (S : Set A'), ∃ m : ℕ,
      ∃ z ∈ Submodule.span R ((S.image e : Finset A) : Set A),
        algebraMap A A' z = algebraMap R A' g ^ m * y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      refine ⟨k x, e x, Submodule.subset_span ?_, ?_⟩
      · simp only [Finset.coe_image]
        exact Set.mem_image_of_mem e hx
      · rw [← he, mul_comm]
    | zero => exact ⟨0, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m1, z1, hz1, h1⟩ := hx
      obtain ⟨m2, z2, hz2, h2⟩ := hy
      refine ⟨m1 + m2, g ^ m2 • z1 + g ^ m1 • z2,
        add_mem (smul_mem _ _ hz1) (smul_mem _ _ hz2), ?_⟩
      rw [map_add, hA, hA, h1, h2, map_pow, map_pow]
      ring
    | smul r' x _ hx =>
      obtain ⟨m, z, hz, h⟩ := hx
      obtain ⟨l, r, hr⟩ := IsLocalization.Away.surj g r'
      refine ⟨m + l, r • z, smul_mem _ _ hz, ?_⟩
      have hr' : algebraMap R A' r = algebraMap R' A' r' * algebraMap R A' g ^ l := by
        rw [IsScalarTower.algebraMap_apply R R' A', ← hr, map_mul, map_pow,
          ← IsScalarTower.algebraMap_apply]
      rw [hA, h, Algebra.smul_def, hr']
      ring
  intro b hb
  obtain ⟨m, z, hz, h⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ m * b) = 0 := by
    rw [map_sub, h, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, sub_self]
  obtain ⟨⟨x, hx⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  obtain ⟨c, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hx
  refine ⟨c + m, ?_⟩
  have hc' : algebraMap R A g ^ c * (z - algebraMap R A g ^ m * b) = 0 := hc
  have : algebraMap R A g ^ (c + m) * b = g ^ c • z := by
    rw [Algebra.smul_def, map_pow]
    linear_combination -hc'
  rw [this]
  exact smul_mem _ _ hz
end GlobalTheory
