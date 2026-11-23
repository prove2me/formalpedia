-- Prove2me | solution 1 for KernelRank.exists_rank_le_five_tendstoUniformlyOn_radial_sq_mul_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:49:07.831996+00:00
-- url     : https://prove2.me/submissions/58c2dd91-1a59-4a4b-b71b-5e5b0a00475f

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution :
    ∃ F : ℝ → (Fin 3 → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (5 : ℕ)) ∧
      ∀ C : Set (Fin 3 → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by
  let r3 : ℝ := Real.sqrt 3 / 2
  let p₁ (u : ℝ) : ℝ := 1 / 2 * Real.cos (u ^ 2) - r3 * Real.sin (u ^ 2)
  let q₁ (u : ℝ) : ℝ := (u ^ 2) * p₁ u
  let p₂ (u : ℝ) : ℝ := -1 / 2 * Real.cos (u ^ 2) - r3 * Real.sin (u ^ 2)
  let q₂ (u : ℝ) : ℝ := (u ^ 2) * p₂ u
  let f1d (h : ℝ) : Fin 5 → ℝ → ℝ
    | 0, u => Real.cos (u ^ 2) + 4 * h * ((u ^ 2) * Real.cos (u ^ 2))
    | 1, u => Real.sin (u ^ 2) + h ^ 2 * Real.cos (u ^ 2)
    | 2, u => Real.sin (u ^ 2)
    | 3, u => p₁ u + h * q₁ u
    | 4, u => p₂ u + h * q₂ u
  let w (h : ℝ) : Fin 5 → ℝ
    | 0 => 1 / (3 * h)
    | 1 => 1 / h ^ 3
    | 2 => -1 / h ^ 3
    | 3 => -4 / (3 * h)
    | 4 => 4 / (3 * h)
  let fac (h : ℝ) (k : Fin 5) (j : Fin 3) (u : ℝ) : ℝ :=
    if j = 0 then w h k * f1d h k u else f1d h k u
  let F (h : ℝ) (x : Fin 3 → ℝ) : ℝ := ∑ k : Fin 5, ∏ j : Fin 3, fac h k j (x j)
  let Rem (x : Fin 3 → ℝ) (h : ℝ) : ℝ :=
    let t0 := x 0 ^ 2; let t1 := x 1 ^ 2; let t2 := x 2 ^ 2
    let c0 := Real.cos t0; let c1 := Real.cos t1; let c2 := Real.cos t2
    let s0 := Real.sin t0; let s1 := Real.sin t1; let s2 := Real.sin t2
    16 / 3 * (t0 * t1 + t0 * t2 + t1 * t2) * c0 * c1 * c2 +
      64 / 3 * h * t0 * t1 * t2 * c0 * c1 * c2 +
      (c0 * c1 * s2 + c0 * s1 * c2 + s0 * c1 * c2) +
      h ^ 2 * c0 * c1 * c2 -
      4 / 3 * (p₁ (x 0) * q₁ (x 1) * q₁ (x 2) + q₁ (x 0) * p₁ (x 1) * q₁ (x 2) +
        q₁ (x 0) * q₁ (x 1) * p₁ (x 2)) -
      4 / 3 * h * q₁ (x 0) * q₁ (x 1) * q₁ (x 2) +
      4 / 3 * (p₂ (x 0) * q₂ (x 1) * q₂ (x 2) + q₂ (x 0) * p₂ (x 1) * q₂ (x 2) +
        q₂ (x 0) * q₂ (x 1) * p₂ (x 2)) +
      4 / 3 * h * q₂ (x 0) * q₂ (x 1) * q₂ (x 2)
  have hident (h : ℝ) (hh0 : h ≠ 0) (x : Fin 3 → ℝ) :
      F h x - (∑ j : Fin 3, x j ^ 2) * Real.cos (∑ j : Fin 3, x j ^ 2) = h * Rem x h := by
    have hcos_sum : Real.cos (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) =
        Real.cos (x 0 ^ 2) * Real.cos (x 1 ^ 2) * Real.cos (x 2 ^ 2) -
          Real.cos (x 0 ^ 2) * Real.sin (x 1 ^ 2) * Real.sin (x 2 ^ 2) -
          Real.sin (x 0 ^ 2) * Real.cos (x 1 ^ 2) * Real.sin (x 2 ^ 2) -
          Real.sin (x 0 ^ 2) * Real.sin (x 1 ^ 2) * Real.cos (x 2 ^ 2) := by
      rw [Real.cos_add, Real.cos_add, Real.sin_add]
      ring
    dsimp only [F, fac, Rem, w, f1d, q₁, q₂, p₁, p₂]
    rw [Fin.sum_univ_five, Fin.sum_univ_three]
    simp only [Fin.prod_univ_three, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    rw [hcos_sum]
    have hh3 : 3 * h ^ 3 ≠ 0 := by positivity
    apply mul_left_cancel₀ hh3
    field_simp [hh0]
    dsimp only [r3]
    ring_nf
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3)]
    ring
  refine ⟨F, fun h => iInf₂_le 5 ⟨fac h, fun _ => rfl⟩, fun C hC => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hRem_cont : Continuous (fun p : (Fin 3 → ℝ) × ℝ => Rem p.1 p.2) := by
    dsimp only [Rem, q₁, q₂, p₁, p₂]
    fun_prop
  obtain ⟨B, hB⟩ := (hC.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := C ×ˢ Set.Icc (-1 : ℝ) 1) hRem_cont.continuousOn
  let M : ℝ := max B 0 + 1
  have hM_pos : 0 < M := by positivity
  let δ : ℝ := min 1 (ε / M)
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hε hM_pos)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ_pos)] with h hh0 hball x hxC
  have hhδ : |h| < δ := by simpa [Real.dist_eq] using hball
  have hh1 : |h| ≤ 1 := le_of_lt (lt_of_lt_of_le hhδ (min_le_left _ _))
  have hh_in : h ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hh1
  have hRem_le : |Rem x h| ≤ M := by
    have hb : ‖Rem x h‖ ≤ B := hB (x, h) ⟨hxC, hh_in⟩
    rw [Real.norm_eq_abs] at hb
    linarith [le_max_left B 0]
  rw [Real.dist_eq, abs_sub_comm, hident h hh0 x, abs_mul]
  calc
    |h| * |Rem x h| ≤ |h| * M := mul_le_mul_of_nonneg_left hRem_le (abs_nonneg h)
    _ < δ * M := mul_lt_mul_of_pos_right hhδ hM_pos
    _ ≤ (ε / M) * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM_pos.le
    _ = ε := div_mul_cancel₀ ε hM_pos.ne'
end KernelRank
