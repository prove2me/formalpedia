-- Prove2me | solution 1 for NearEnemy.circPoly_ne_zero_of_coplanar
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:03:23.001421+00:00
-- url     : https://prove2.me/submissions/cb52e2b5-0362-4bdc-a8bb-d2a15548fc20

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_eval_innerPoly_rows
import Theorems.Thm_NearEnemy_exists_smul_eq_of_forall_inner_det_eq_zero

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

/-- A difference proportionality `c - a = t • (b - a)` puts the triple on
the line through `a` with direction `b - a`. -/
 theorem collinear_triple_of_smul
    {a b c : EuclideanSpace ℝ ι} {t : ℝ}
    (ht : c - a = t • (b - a)) :
    Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)) := by
  rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
  refine ⟨b - a, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by rw [vadd_eq_add]; module⟩
  · exact ⟨t, by rw [vadd_eq_add]; linear_combination (norm := module) ht⟩

/-- **Frame trichotomy**: if the three second-moment determinants `A`, `B`,
`C` are not all zero, one of the explicit frames `id`, `diag(2,1)`, shear
produces a nonzero value of the projected-circle combination
`(αδ - βγ)((α² + γ²)A + 2(αβ + γδ)B + (β² + δ²)C)`. -/
 theorem exists_frame_combo_ne_zero {A B C : ℝ}
    (h : ¬ (A = 0 ∧ B = 0 ∧ C = 0)) :
    ∃ α β γ δ : ℝ,
      (α * δ - β * γ) *
        ((α ^ 2 + γ ^ 2) * A + 2 * (α * β + γ * δ) * B +
          (β ^ 2 + δ ^ 2) * C) ≠ 0 := by
  by_cases hAC : A + C = 0
  · by_cases hA : A = 0
    · have hC : C = 0 := by linarith
      have hB : B ≠ 0 := fun hB => h ⟨hA, hB, hC⟩
      refine ⟨1, 1, 0, 1, fun h0 => hB ?_⟩
      linear_combination (1 / 2 : ℝ) * h0 - (1 / 2 : ℝ) * hA - hC
    · refine ⟨2, 0, 0, 1, fun h0 => hA ?_⟩
      linear_combination (1 / 6 : ℝ) * h0 - (1 / 3 : ℝ) * hAC
  · refine ⟨1, 0, 0, 1, fun h0 => hAC ?_⟩
    linear_combination h0

/-- **Planar concyclicity witness core**: four planar points given by
coordinates, with the triple `{1,2,3}` non-collinear (`hcr`), the triple
`{2,3,4}` non-collinear (`hm`), and `ζ₁ ≠ ζ₄` (`hs`), admit an invertible
linear frame under which the four image points are neither concyclic nor
collinear.  The second-moment determinants are not all zero — witnessed by
the line-pair conic through `ζ₂, ζ₃, ζ₄` missing `ζ₁` — and the frame
trichotomy finishes. -/
 theorem exists_planar_frame_circleDet_ne_zero
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ}
    (hcr : (x₁ - x₂) * (y₃ - y₂) - (y₁ - y₂) * (x₃ - x₂) ≠ 0)
    (hm : x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃) ≠ 0)
    (hs : (x₁ - x₄) ^ 2 + (y₁ - y₄) ^ 2 ≠ 0) :
    ∃ α β γ δ : ℝ,
      (α * δ - β * γ) *
        ((α ^ 2 + γ ^ 2) *
            (x₁ ^ 2 * (x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) -
              x₂ ^ 2 * (x₁ * (y₃ - y₄) - y₁ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) +
              x₃ ^ 2 * (x₁ * (y₂ - y₄) - y₁ * (x₂ - x₄) + (x₂ * y₄ - x₄ * y₂)) -
              x₄ ^ 2 * (x₁ * (y₂ - y₃) - y₁ * (x₂ - x₃) + (x₂ * y₃ - x₃ * y₂))) +
          2 * (α * β + γ * δ) *
            (x₁ * y₁ * (x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) -
              x₂ * y₂ * (x₁ * (y₃ - y₄) - y₁ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) +
              x₃ * y₃ * (x₁ * (y₂ - y₄) - y₁ * (x₂ - x₄) + (x₂ * y₄ - x₄ * y₂)) -
              x₄ * y₄ * (x₁ * (y₂ - y₃) - y₁ * (x₂ - x₃) + (x₂ * y₃ - x₃ * y₂))) +
          (β ^ 2 + δ ^ 2) *
            (y₁ ^ 2 * (x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) -
              y₂ ^ 2 * (x₁ * (y₃ - y₄) - y₁ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) +
              y₃ ^ 2 * (x₁ * (y₂ - y₄) - y₁ * (x₂ - x₄) + (x₂ * y₄ - x₄ * y₂)) -
              y₄ ^ 2 * (x₁ * (y₂ - y₃) - y₁ * (x₂ - x₃) + (x₂ * y₃ - x₃ * y₂)))) ≠
        0 := by
  refine exists_frame_combo_ne_zero ?_
  rintro ⟨hA, hB, hC⟩
  have key : ((x₁ - x₂) * (y₃ - y₂) - (y₁ - y₂) * (x₃ - x₂)) *
      ((x₁ - x₄) ^ 2 + (y₁ - y₄) ^ 2) *
      (x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) =
      (y₃ - y₂) * (x₁ - x₄) *
          (x₁ ^ 2 * (x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) -
            x₂ ^ 2 * (x₁ * (y₃ - y₄) - y₁ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) +
            x₃ ^ 2 * (x₁ * (y₂ - y₄) - y₁ * (x₂ - x₄) + (x₂ * y₄ - x₄ * y₂)) -
            x₄ ^ 2 * (x₁ * (y₂ - y₃) - y₁ * (x₂ - x₃) + (x₂ * y₃ - x₃ * y₂))) +
        ((y₃ - y₂) * (y₁ - y₄) - (x₃ - x₂) * (x₁ - x₄)) *
          (x₁ * y₁ * (x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) -
            x₂ * y₂ * (x₁ * (y₃ - y₄) - y₁ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) +
            x₃ * y₃ * (x₁ * (y₂ - y₄) - y₁ * (x₂ - x₄) + (x₂ * y₄ - x₄ * y₂)) -
            x₄ * y₄ * (x₁ * (y₂ - y₃) - y₁ * (x₂ - x₃) + (x₂ * y₃ - x₃ * y₂))) +
        (-(x₃ - x₂) * (y₁ - y₄)) *
          (y₁ ^ 2 * (x₂ * (y₃ - y₄) - y₂ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) -
            y₂ ^ 2 * (x₁ * (y₃ - y₄) - y₁ * (x₃ - x₄) + (x₃ * y₄ - x₄ * y₃)) +
            y₃ ^ 2 * (x₁ * (y₂ - y₄) - y₁ * (x₂ - x₄) + (x₂ * y₄ - x₄ * y₂)) -
            y₄ ^ 2 * (x₁ * (y₂ - y₃) - y₁ * (x₂ - x₃) + (x₂ * y₃ - x₃ * y₂))) := by
    ring
  rw [hA, hB, hC] at key
  simp only [mul_zero, add_zero] at key
  rcases mul_eq_zero.mp key with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact hcr h''
    · exact hs h''
  · exact hm h'

end NearEnemy

open NearEnemy in
theorem solution {a b c e : EuclideanSpace ℝ ι}
    (hab : a ≠ b) (hae : a ≠ e)
    (habc : ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)))
    (hbce : ¬ Collinear ℝ ({b, c, e} : Set (EuclideanSpace ℝ ι)))
    (hdep : e - a ∈ Submodule.span ℝ ({b - a, c - a} :
      Set (EuclideanSpace ℝ ι))) :
    circPoly a b c e ≠ 0 := by
  -- Gram–Schmidt frame of the plane of the quadruple.
  have hv0 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hnv : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  set e₁ : EuclideanSpace ℝ ι := ‖b - a‖⁻¹ • (b - a) with he₁
  have h11 : ⟪e₁, e₁⟫ = 1 := by
    rw [he₁, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
  have hv1 : b - a = ‖b - a‖ • e₁ := by
    rw [he₁, smul_smul, mul_inv_cancel₀ hnv, one_smul]
  set u : EuclideanSpace ℝ ι := c - a - ⟪e₁, c - a⟫ • e₁ with hu
  have hu0 : u ≠ 0 := by
    intro h
    apply habc
    have hc : c - a = ⟪e₁, c - a⟫ • e₁ := by rwa [hu, sub_eq_zero] at h
    refine collinear_triple_of_smul (t := ⟪e₁, c - a⟫ * ‖b - a‖⁻¹) ?_
    calc c - a = ⟪e₁, c - a⟫ • e₁ := hc
      _ = (⟪e₁, c - a⟫ * ‖b - a‖⁻¹) • (b - a) := by rw [he₁, smul_smul]
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  set e₂ : EuclideanSpace ℝ ι := ‖u‖⁻¹ • u with he₂
  have h22 : ⟪e₂, e₂⟫ = 1 := by
    rw [he₂, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
  have he₁u : ⟪e₁, u⟫ = 0 := by
    rw [hu, inner_sub_right, real_inner_smul_right, h11, mul_one, sub_self]
  have h12 : ⟪e₁, e₂⟫ = 0 := by
    rw [he₂, real_inner_smul_right, he₁u, mul_zero]
  have h21 : ⟪e₂, e₁⟫ = 0 := by rw [real_inner_comm]; exact h12
  have hu1 : u = ‖u‖ • e₂ := by
    rw [he₂, smul_smul, mul_inv_cancel₀ hnu, one_smul]
  have hcu : c - a = ⟪e₁, c - a⟫ • e₁ + u := by rw [hu]; module
  -- The frame is now characterized by its recorded properties; make it
  -- opaque so that rewriting and ring normalization treat it atomically.
  clear_value e₁ u e₂
  -- Coordinate expansions of the three difference vectors.
  have hba : b - a = (⟪e₁, b⟫ - ⟪e₁, a⟫) • e₁ + (⟪e₂, b⟫ - ⟪e₂, a⟫) • e₂ := by
    have hx : ⟪e₁, b⟫ - ⟪e₁, a⟫ = ‖b - a‖ := by
      rw [← inner_sub_right]
      conv_lhs => rw [hv1]
      rw [real_inner_smul_right, h11, mul_one]
    have hy : ⟪e₂, b⟫ - ⟪e₂, a⟫ = 0 := by
      rw [← inner_sub_right]
      conv_lhs => rw [hv1]
      rw [real_inner_smul_right, h21, mul_zero]
    rw [hx, hy, zero_smul, add_zero]
    exact hv1
  have hca : c - a = (⟪e₁, c⟫ - ⟪e₁, a⟫) • e₁ + (⟪e₂, c⟫ - ⟪e₂, a⟫) • e₂ := by
    have hx : ⟪e₁, c⟫ - ⟪e₁, a⟫ = ⟪e₁, c - a⟫ := (inner_sub_right _ _ _).symm
    have hy : ⟪e₂, c⟫ - ⟪e₂, a⟫ = ‖u‖ := by
      rw [← inner_sub_right]
      conv_lhs => rw [hcu]
      rw [inner_add_right, real_inner_smul_right, h21, mul_zero, zero_add]
      conv_lhs => rw [hu1]
      rw [real_inner_smul_right, h22, mul_one]
    rw [hx, hy, ← hu1]
    exact hcu
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hdep
  have hea : e - a = (⟪e₁, e⟫ - ⟪e₁, a⟫) • e₁ + (⟪e₂, e⟫ - ⟪e₂, a⟫) • e₂ := by
    have hx : ⟪e₁, e⟫ - ⟪e₁, a⟫ =
        s * (⟪e₁, b⟫ - ⟪e₁, a⟫) + t * (⟪e₁, c⟫ - ⟪e₁, a⟫) := by
      rw [← inner_sub_right, ← inner_sub_right, ← inner_sub_right, ← hst,
        inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hy : ⟪e₂, e⟫ - ⟪e₂, a⟫ =
        s * (⟪e₂, b⟫ - ⟪e₂, a⟫) + t * (⟪e₂, c⟫ - ⟪e₂, a⟫) := by
      rw [← inner_sub_right, ← inner_sub_right, ← inner_sub_right, ← hst,
        inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [hx, hy, ← hst]
    conv_lhs => rw [hba, hca]
    module
  have hcb : c - b = (⟪e₁, c⟫ - ⟪e₁, b⟫) • e₁ + (⟪e₂, c⟫ - ⟪e₂, b⟫) • e₂ := by
    linear_combination (norm := module) hca - hba
  have heb : e - b = (⟪e₁, e⟫ - ⟪e₁, b⟫) • e₁ + (⟪e₂, e⟫ - ⟪e₂, b⟫) • e₂ := by
    linear_combination (norm := module) hea - hba
  -- Inner products against expanded vectors.
  have hexp : ∀ (z : EuclideanSpace ℝ ι) (X Y : ℝ),
      z = X • e₁ + Y • e₂ → ∀ p : EuclideanSpace ℝ ι,
      ⟪p, z⟫ = X * ⟪p, e₁⟫ + Y * ⟪p, e₂⟫ := by
    intro z X Y hz p
    rw [hz, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  -- Transfer the three planar hypotheses.
  have hcr : (⟪e₁, a⟫ - ⟪e₁, b⟫) * (⟪e₂, c⟫ - ⟪e₂, b⟫) -
      (⟪e₂, a⟫ - ⟪e₂, b⟫) * (⟪e₁, c⟫ - ⟪e₁, b⟫) ≠ 0 := by
    intro hzero
    apply habc
    have hdet : ∀ p q : EuclideanSpace ℝ ι,
        ⟪p, b - a⟫ * ⟪q, c - a⟫ - ⟪p, c - a⟫ * ⟪q, b - a⟫ = 0 := by
      intro p q
      rw [hexp _ _ _ hba p, hexp _ _ _ hba q, hexp _ _ _ hca p,
        hexp _ _ _ hca q]
      linear_combination
        (-(⟪p, e₁⟫ * ⟪q, e₂⟫ - ⟪p, e₂⟫ * ⟪q, e₁⟫)) * hzero
    rcases exists_smul_eq_of_forall_inner_det_eq_zero hdet with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact collinear_triple_of_smul hr
    · have := collinear_triple_of_smul (a := a) (b := c) (c := b) hr
      rwa [Set.pair_comm c b] at this
  have hm : ⟪e₁, b⟫ * (⟪e₂, c⟫ - ⟪e₂, e⟫) - ⟪e₂, b⟫ * (⟪e₁, c⟫ - ⟪e₁, e⟫) +
      (⟪e₁, c⟫ * ⟪e₂, e⟫ - ⟪e₁, e⟫ * ⟪e₂, c⟫) ≠ 0 := by
    intro hzero
    apply hbce
    have hdet : ∀ p q : EuclideanSpace ℝ ι,
        ⟪p, c - b⟫ * ⟪q, e - b⟫ - ⟪p, e - b⟫ * ⟪q, c - b⟫ = 0 := by
      intro p q
      rw [hexp _ _ _ hcb p, hexp _ _ _ hcb q, hexp _ _ _ heb p,
        hexp _ _ _ heb q]
      linear_combination (⟪p, e₁⟫ * ⟪q, e₂⟫ - ⟪p, e₂⟫ * ⟪q, e₁⟫) * hzero
    rcases exists_smul_eq_of_forall_inner_det_eq_zero hdet with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact collinear_triple_of_smul hr
    · have := collinear_triple_of_smul (a := b) (b := e) (c := c) hr
      rwa [Set.pair_comm e c] at this
  have hs : (⟪e₁, a⟫ - ⟪e₁, e⟫) ^ 2 + (⟪e₂, a⟫ - ⟪e₂, e⟫) ^ 2 ≠ 0 := by
    intro hzero
    apply hae
    have h1 : (⟪e₁, a⟫ - ⟪e₁, e⟫) ^ 2 = 0 := by
      nlinarith [sq_nonneg (⟪e₁, a⟫ - ⟪e₁, e⟫), sq_nonneg (⟪e₂, a⟫ - ⟪e₂, e⟫)]
    have h2 : (⟪e₂, a⟫ - ⟪e₂, e⟫) ^ 2 = 0 := by
      nlinarith [sq_nonneg (⟪e₁, a⟫ - ⟪e₁, e⟫), sq_nonneg (⟪e₂, a⟫ - ⟪e₂, e⟫)]
    have hx0 : ⟪e₁, e⟫ - ⟪e₁, a⟫ = 0 := by
      have := sq_eq_zero_iff.mp h1
      linarith
    have hy0 : ⟪e₂, e⟫ - ⟪e₂, a⟫ = 0 := by
      have := sq_eq_zero_iff.mp h2
      linarith
    have hez : e - a = 0 := by
      rw [hea, hx0, hy0, zero_smul, zero_smul, add_zero]
    exact (sub_eq_zero.mp hez).symm
  -- The planar core gives an explicit frame; read it as a row pair.
  obtain ⟨α, β, γ, δ, hne⟩ := exists_planar_frame_circleDet_ne_zero hcr hm hs
  intro h0
  have heval := congrArg
    (eval fun ki ↦ ![α • e₁ + β • e₂, γ • e₁ + δ • e₂] ki.1 ki.2) h0
  rw [map_zero] at heval
  simp only [circPoly, map_add, map_sub, map_mul, map_pow, eval_innerPoly_rows,
    Matrix.cons_val_zero, Matrix.cons_val_one] at heval
  have hrow : ∀ (s' t' : ℝ) (p : EuclideanSpace ℝ ι),
      ⟪s' • e₁ + t' • e₂, p⟫ = s' * ⟪e₁, p⟫ + t' * ⟪e₂, p⟫ := by
    intro s' t' p
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp only [hrow] at heval
  exact hne (by linear_combination heval)
