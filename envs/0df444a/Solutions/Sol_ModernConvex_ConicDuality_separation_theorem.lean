-- Prove2me | solution 1 for ModernConvex.ConicDuality.separation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:29:59.518438+00:00
-- url     : https://prove2.me/submissions/7a36a012-4827-4c1a-8284-d5bdf8429595

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

theorem g69a1_vec {κ : Type*} [Fintype κ] [DecidableEq κ] (g : (κ → ℝ) →ₗ[ℝ] ℝ) :
    ∀ z : κ → ℝ, g z = (fun j => g (Pi.single j 1)) ⬝ᵥ z := by
  intro z
  conv_lhs => rw [show z = ∑ j, z j • Pi.single j (1:ℝ) by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, dotProduct, mul_comm]

theorem g69a1_sep_zero {κ : Type} [Fintype κ] [DecidableEq κ] (D : Set (κ → ℝ))
    (hD : D.Nonempty) (hDc : Convex ℝ D) (h0 : (0 : κ → ℝ) ∉ D) :
    ∃ g : (κ → ℝ) →ₗ[ℝ] ℝ, g ≠ 0 ∧ ∀ d ∈ D, g d ≤ 0 := by
  by_cases hint : (interior D).Nonempty
  · have hdisj : Disjoint (interior D) {0} := by
      rw [Set.disjoint_singleton_right]
      exact fun h => h0 (interior_subset h)
    obtain ⟨f, u, hf0, hfD, hfu⟩ := geometric_hahn_banach_of_nonempty_interior hDc
      (convex_singleton 0) hdisj hint (Set.singleton_nonempty 0)
    refine ⟨f.toLinearMap, ?_, ?_⟩
    · intro h; apply hf0; ext x; exact LinearMap.congr_fun h x
    · intro d hd
      have := hfu 0 rfl
      have := hfD d hd
      simp only [map_zero] at *
      show f d ≤ 0
      linarith
  · rw [hDc.interior_nonempty_iff_affineSpan_eq_top] at hint
    have hvs : vectorSpan ℝ D < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hint
      rw [← AffineSubspace.direction_eq_top_iff_of_nonempty (hD.mono (subset_affineSpan ℝ D)),
        direction_affineSpan, htop]
    obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hvs
    obtain ⟨d0, hd0⟩ := hD
    have hconst : ∀ d ∈ D, f d = f d0 := by
      intro d hd
      have := hker (vsub_mem_vectorSpan ℝ hd hd0)
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
      exact this
    by_cases hs : f d0 ≤ 0
    · exact ⟨f, hf0, fun d hd => by rw [hconst d hd]; exact hs⟩
    · refine ⟨-f, neg_ne_zero.mpr hf0, fun d hd => ?_⟩
      rw [LinearMap.neg_apply, hconst d hd]; linarith

open ModernConvex.ConicDuality
open scoped Pointwise

theorem solution {m : ℕ} (S T : Set (Fin m → ℝ)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hSc : Convex ℝ S) (hTc : Convex ℝ T) (hST : Disjoint S T) :
    ∃ l : Fin m → ℝ, l ≠ 0 ∧ ∀ u ∈ S, ∀ v ∈ T, l ⬝ᵥ u ≤ l ⬝ᵥ v := by
  set D : Set (Fin m → ℝ) := S - T with hD
  have hDne : D.Nonempty := hS.sub hT
  have hDc : Convex ℝ D := hSc.sub hTc
  have h0 : (0 : Fin m → ℝ) ∉ D := by
    rintro ⟨u, hu, v, hv, huv⟩
    rw [sub_eq_zero] at huv
    subst huv
    exact Set.disjoint_left.mp hST hu hv
  obtain ⟨g, hg0, hgD⟩ := g69a1_sep_zero D hDne hDc h0
  refine ⟨fun j => g (Pi.single j 1), ?_, ?_⟩
  · intro hl
    apply hg0
    apply LinearMap.ext; intro z
    rw [g69a1_vec g z, hl]
    simp
  · intro u hu v hv
    have := hgD (u - v) ⟨u, hu, v, hv, rfl⟩
    rw [g69a1_vec g, dotProduct_sub] at this
    linarith
