-- Prove2me | solution 1 for KatyushaNs.lemma_2_5_proximal_mirror_descent
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:24:00.816537+00:00
-- url     : https://prove2.me/submissions/ed2acb28-0e14-488b-92c0-3bca9e77eaa1

import Definitions.Def_KatyushaNs_IsQuadProxMin
import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Module

open Set Filter Topology
open scoped InnerProductSpace

private lemma quad_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : Set E} {ψ : E → ℝ} {σ κ : ℝ} (hψ : StrongConvexOn D σ ψ)
    {p c g : E} (hp : p ∈ D)
    (hmin : ∀ w ∈ D, κ / 2 * ‖p-c‖^2 + inner ℝ g p + ψ p ≤
      κ / 2 * ‖w-c‖^2 + inner ℝ g w + ψ w) {u : E} (hu : u ∈ D) :
    κ / 2 * ‖p-c‖^2 + inner ℝ g p + ψ p +
        (κ+σ)/2 * ‖p-u‖^2 ≤ κ / 2 * ‖u-c‖^2 + inner ℝ g u + ψ u := by
  have hseg (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
      κ / 2 * ‖p-c‖^2 + inner ℝ g p + ψ p +
        (κ+σ)/2 * (1-t) * ‖p-u‖^2 ≤ κ / 2 * ‖u-c‖^2 + inner ℝ g u + ψ u := by
    have hm := hmin ((1-t) • p + t • u)
      (hψ.1 hp hu (by linarith) ht0.le (by ring))
    have hc := hψ.2 hp hu (show 0 ≤ 1-t by linarith) ht0.le (show 1-t+t=1 by ring)
    simp only [smul_eq_mul] at hc
    have hv : (1-t) • p + t • u - c = (1-t) • (p-c) + t • (u-c) := by module
    have hnorm : ‖(1-t) • p + t • u - c‖^2 =
        (1-t) * ‖p-c‖^2 + t * ‖u-c‖^2 - (1-t)*t*‖p-u‖^2 := by
      rw [hv, norm_add_sq_real, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 1-t by linarith),
        abs_of_pos ht0, real_inner_smul_left, inner_smul_right]
      have hdiff : ‖p-u‖^2 = ‖p-c‖^2 - 2 * inner ℝ (p-c) (u-c) + ‖u-c‖^2 := by
        have heq : p-u = (p-c)-(u-c) := by abel
        calc
          ‖p-u‖^2 = ‖(p-c)-(u-c)‖^2 := by rw [heq]
          _ = _ := norm_sub_sq_real _ _
      rw [hdiff]
      ring
    rw [hnorm, inner_add_right, inner_smul_right, inner_smul_right] at hm
    have hm' : 0 ≤ t * ((κ / 2 * ‖u-c‖^2 + inner ℝ g u + ψ u) -
        (κ / 2 * ‖p-c‖^2 + inner ℝ g p + ψ p + (κ+σ)/2 * (1-t) * ‖p-u‖^2)) := by
      nlinarith
    have := nonneg_of_mul_nonneg_right hm' ht0
    linarith
  have htend : Tendsto (fun t : ℝ => κ / 2 * ‖p-c‖^2 + inner ℝ g p + ψ p +
      (κ+σ)/2 * (1-t) * ‖p-u‖^2) (𝓝[>] 0)
      (𝓝 (κ / 2 * ‖p-c‖^2 + inner ℝ g p + ψ p + (κ+σ)/2 * ‖p-u‖^2)) := by
    have hc : Continuous (fun t : ℝ => κ / 2 * ‖p-c‖^2 + inner ℝ g p + ψ p +
      (κ+σ)/2 * (1-t) * ‖p-u‖^2) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply le_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  exact hseg t ht0 ht1

open KatyushaNs

theorem solution {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {σ : ℝ} (hσ : 0 ≤ σ) (hψσ : StrongConvexOn D σ ψ)
    {α : ℝ} (hα : 0 < α) {g zk zplus : EuclideanSpace ℝ (Fin d)}
    (hz : IsQuadProxMin D ψ α⁻¹ zk g zplus) :
    ∀ u ∈ D, α * inner ℝ g (zplus - u) + α * ψ zplus - α * ψ u ≤
      -(1 / 2) * ‖zk - zplus‖ ^ 2 + 1 / 2 * ‖zk - u‖ ^ 2 -
        (1 + α * σ) / 2 * ‖zplus - u‖ ^ 2 := by
  intro u hu
  have hg := quad_gap hψσ hz.1 hz.2 hu
  have hmul := mul_le_mul_of_nonneg_left hg hα.le
  have hid : α * α⁻¹ = 1 := mul_inv_cancel₀ hα.ne'
  rw [inner_sub_right, norm_sub_rev zk zplus, norm_sub_rev zk u]
  nlinarith [show α * (α⁻¹ * ‖zplus-zk‖^2) = ‖zplus-zk‖^2 by rw [← mul_assoc, hid, one_mul],
    show α * (α⁻¹ * ‖u-zk‖^2) = ‖u-zk‖^2 by rw [← mul_assoc, hid, one_mul],
    show α * α⁻¹ * ‖zplus-u‖^2 = ‖zplus-u‖^2 by rw [hid, one_mul]]

#print axioms solution
