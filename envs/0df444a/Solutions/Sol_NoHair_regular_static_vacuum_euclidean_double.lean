-- Prove2me | solution 1 for NoHair.regular_static_vacuum_euclidean_double
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:18:55.565817+00:00
-- url     : https://prove2.me/submissions/26b4f14d-6ea9-47e3-8971-986e1f5adc27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_regular_static_vacuum_flat_double_chart
import Theorems.Thm_NoHair_signed_static_lapse_harmonic_factor

open Set NoHair InnerProductSpace
open scoped Manifold ContDiff

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (hslice : HasRegularStaticVacuumSlice g φ D) :
    ∃ (U : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)),
      HasConformalVacuumExterior g D U ∧ HarmonicOnNhd U ({0}ᶜ) ∧
      (∀ x, x ≠ 0 → 0 ≤ U x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε) ∧ p ≠ 0 ∧ U p = 2 := by
  obtain ⟨V,p,hc,hr,hl,hfar,hp,hzero,hflux⟩ :=
    regular_static_vacuum_flat_double_chart g φ D hslice
  let U := fun x : EuclideanSpace ℝ (Fin 3) => 2 / (1 + V x)
  refine ⟨U, p, hc, signed_static_lapse_harmonic_factor V hr hl hflux, ?_, ?_, hp, ?_⟩
  · intro x hx
    exact div_nonneg (by norm_num) (by linarith only [hl x hx])
  · intro ε hε
    obtain ⟨L, hL⟩ := hfar (min ε (1/2)) (lt_min hε (by norm_num))
    refine ⟨L, fun x hx => ?_⟩
    have bound := hL x hx
    have nonneg : 0 ≤ V x := by
      have lower := (abs_le.mp bound).1
      have small : min ε (1/2) ≤ 1/2 := min_le_right _ _
      linarith
    have dn : 0 < 1 + V x := by linarith
    have eq : U x - 1 = -(V x - 1) / (1 + V x) := by
      dsimp only [U]
      field_simp [dn.ne']
      <;> ring
    rw [eq,abs_div,abs_neg,abs_of_pos dn]
    apply (div_le_iff₀ dn).mpr
    have hε' := bound.trans (min_le_left _ _)
    nlinarith only [hε', mul_nonneg hε.le nonneg]
  · simp only [U,hzero,add_zero,div_one]
