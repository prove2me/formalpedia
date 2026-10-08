-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.ineq16_value_gap_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:52:32.821428+00:00
-- url     : https://prove2.me/submissions/b7402a06-0be6-4998-a983-495c3f087cb2

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

set_option autoImplicit false

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization
open scoped InnerProductSpace

namespace Cbfa1125

lemma reg_global {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (hconv : EConvex f) (x v : X)
    (hreg : IsRegularSubgrad f x v) (z : X) (hz : f z ≠ ⊤) :
    (f x).toReal + ⟪v, z - x⟫_ℝ ≤ (f z).toReal := by
  obtain ⟨hxtop, hloc⟩ := hreg
  set a := (f x).toReal with ha
  set b := (f z).toReal with hb
  have hfx : f x = (a : EReal) := (EReal.coe_toReal hxtop (hbot x)).symm
  have hfz : f z = (b : EReal) := (EReal.coe_toReal hz (hbot z)).symm
  have key : ∀ ε : ℝ, 0 < ε → ⟪v, z - x⟫_ℝ - ε * ‖z - x‖ ≤ b - a := by
    intro ε hε
    have hev := hloc ε hε
    have hcont : Continuous (fun t : ℝ => x + t • (z - x)) := by fun_prop
    have htend : Tendsto (fun t : ℝ => x + t • (z - x)) (𝓝[>] 0) (𝓝 x) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), f x + ((⟪v, (x + t • (z - x)) - x⟫_ℝ
        - ε * ‖(x + t • (z - x)) - x‖ : ℝ) : EReal) ≤ f (x + t • (z - x)) :=
      htend.eventually hev
    have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    have h3 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht1, ht2, ht3⟩ := (h1.and (h2.and h3)).exists
    have hmem := hconv (x := (x, a)) (y := (z, b)) (by simp [hfx]) (by simp [hfz])
      (a := 1 - t) (b := t) (by linarith) ht3.le (by ring)
    simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hmem
    have hpt : (1 - t) • x + t • z = x + t • (z - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hpt] at hmem
    have h4 := ht1.trans hmem
    rw [hfx] at h4
    simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht3] at h4
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h4
    have h5 : t * (⟪v, z - x⟫_ℝ - ε * ‖z - x‖) ≤ t * (b - a) := by nlinarith
    exact le_of_mul_le_mul_left h5 ht3
  have hc : ⟪v, z - x⟫_ℝ ≤ b - a := by
    by_contra hcon
    push_neg at hcon
    set N := ‖z - x‖
    have hN : 0 ≤ N := norm_nonneg _
    set δ := ⟪v, z - x⟫_ℝ - (b - a)
    have hδ : 0 < δ := by simp only [δ]; linarith
    have hε : 0 < δ / (N + 1) := div_pos hδ (by linarith)
    have hk := key _ hε
    have : δ / (N + 1) * N < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    simp only [δ] at this hk
    linarith
  linarith

lemma lim_global {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (hconv : EConvex f) (x v : X)
    (hv : v ∈ LimitingSubdiff f x) (z : X) (hz : f z ≠ ⊤) :
    (f x).toReal + ⟪v, z - x⟫_ℝ ≤ (f z).toReal := by
  obtain ⟨hxtop, xs, vs, hxs, hfxs, hvs, hreg⟩ := hv
  have h1 : Tendsto (fun t => (f (xs t)).toReal) atTop (𝓝 (f x).toReal) :=
    (EReal.tendsto_toReal hxtop (hbot x)).comp hfxs
  have h2 : Tendsto (fun t => ⟪vs t, z - xs t⟫_ℝ) atTop (𝓝 ⟪v, z - x⟫_ℝ) :=
    hvs.inner (tendsto_const_nhds.sub hxs)
  exact le_of_tendsto' (h1.add h2) (fun t => reg_global f hbot hconv _ _ (hreg t) z hz)

lemma crit_min {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (hconv : EConvex f) (p : X)
    (hp : (0 : X) ∈ LimitingSubdiff f p) : ∀ z, f p ≤ f z := by
  intro z
  have hptop : f p ≠ ⊤ := hp.1
  by_cases hz : f z = ⊤
  · rw [hz]; exact le_top
  have h := lim_global f hbot hconv p 0 hp z hz
  simp only [inner_zero_left, add_zero] at h
  rw [← EReal.coe_toReal hptop (hbot p), ← EReal.coe_toReal hz (hbot z)]
  exact EReal.coe_le_coe_iff.2 h

end Cbfa1125

open Filter Topology NonconvexSplitting.Shared MoreauProx.Characterization NonsmoothLojasiewicz.Convex in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hcrit : (crit f).Nonempty)
    (x : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ LimitingSubdiff f x) :
    |(f x).toReal - (⨅ y, f y).toReal| ≤ ‖v‖ * Metric.infDist x (crit f) := by
  obtain ⟨hbot, -, hconv, -⟩ := hf
  obtain ⟨p, hp⟩ := hcrit
  have hpmin := Cbfa1125.crit_min f hbot hconv p hp
  have hinf : (⨅ y, f y) = f p := le_antisymm (iInf_le _ _) (le_iInf hpmin)
  rw [hinf]
  have hxtop : f x ≠ ⊤ := hv.1
  have hptop : f p ≠ ⊤ := hp.1
  have hxp : (f p).toReal ≤ (f x).toReal := by
    have := hpmin x
    rw [← EReal.coe_toReal hptop (hbot p), ← EReal.coe_toReal hxtop (hbot x)] at this
    exact EReal.coe_le_coe_iff.1 this
  rw [abs_of_nonneg (by linarith)]
  -- for every q ∈ crit f: f x - f p ≤ ‖v‖ * dist x q
  have hq : ∀ q ∈ NonsmoothLojasiewicz.Convex.crit f,
      (f x).toReal - (f p).toReal ≤ ‖v‖ * dist x q := by
    intro q hq
    have hqtop : f q ≠ ⊤ := hq.1
    have hqp : (f q).toReal ≤ (f p).toReal := by
      have := Cbfa1125.crit_min f hbot hconv q hq p
      rw [← EReal.coe_toReal hptop (hbot p), ← EReal.coe_toReal hqtop (hbot q)] at this
      exact EReal.coe_le_coe_iff.1 this
    have h := Cbfa1125.lim_global f hbot hconv x v hv q hqtop
    have hcs : -⟪v, q - x⟫_ℝ ≤ ‖v‖ * ‖q - x‖ := by
      have := abs_real_inner_le_norm v (q - x)
      linarith [neg_abs_le ⟪v, q - x⟫_ℝ]
    rw [dist_comm, dist_eq_norm]
    linarith
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · have := hq p hp
    rw [← h0] at this ⊢
    simpa using this
  · have hle : ((f x).toReal - (f p).toReal) / ‖v‖ ≤ Metric.infDist x (NonsmoothLojasiewicz.Convex.crit f) := by
      rw [Metric.le_infDist ⟨p, hp⟩]
      intro q hq'
      rw [div_le_iff₀ hpos]
      have := hq q hq'
      linarith
    rw [div_le_iff₀ hpos] at hle
    linarith
