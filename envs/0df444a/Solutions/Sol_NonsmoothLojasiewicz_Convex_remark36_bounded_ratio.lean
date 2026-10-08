-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.remark36_bounded_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:36:09.999287+00:00
-- url     : https://prove2.me/submissions/d717826a-2604-4517-b974-1346c6711d8f

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

set_option autoImplicit false

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace P0909e1e9

open scoped InnerProductSpace

/-- A regular subgradient of a convex function is a global subgradient (real form). -/
theorem reg_global {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (hconv : EConvex f) (x v : X) (r : ℝ) (hr : f x = (r : EReal))
    (hv : IsRegularSubgrad f x v) (z : X) (s : ℝ) (hs : f z = (s : EReal)) :
    r + ⟪v, z - x⟫_ℝ ≤ s := by
  have key : ∀ ε : ℝ, 0 < ε → ⟪v, z - x⟫_ℝ - ε * ‖z - x‖ ≤ s - r := by
    intro ε hε
    have h1 : Tendsto (fun t : ℝ => x + t • (z - x)) (𝓝[>] 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => x + t • (z - x)) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    obtain ⟨t, ht1, ht2⟩ :=
      ((h1.eventually (hv.2 ε hε)).and (Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1))).exists
    obtain ⟨ht0, ht1'⟩ := ht2
    -- convexity
    have hmem1 : (x, r) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
      simp [hr]
    have hmem2 : (z, s) ∈ {p : X × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
      simp [hs]
    have hcv := hconv hmem1 hmem2 (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    simp only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hcv
    have hw : (1 - t) • x + t • z = x + t • (z - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hw] at hcv
    have hsub : x + t • (z - x) - x = t • (z - x) := by abel
    rw [hsub, hr, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at ht1
    have h3 := ht1.trans hcv
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    have h4 : t * (⟪v, z - x⟫_ℝ - ε * ‖z - x‖) ≤ t * (s - r) := by nlinarith
    exact le_of_mul_le_mul_left h4 ht0
  have hn : 0 ≤ ‖z - x‖ := norm_nonneg _
  have : ⟪v, z - x⟫_ℝ ≤ s - r := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hp : 0 < ‖z - x‖ + 1 := by linarith
    have := key (ε / (‖z - x‖ + 1)) (div_pos hε hp)
    have h5 : ε / (‖z - x‖ + 1) * ‖z - x‖ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hp]; nlinarith
    linarith
  linarith

/-- A limiting subgradient of a convex never-`⊥` function is a global subgradient. -/
theorem lim_global {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (hconv : EConvex f) (x v : X)
    (hv : v ∈ LimitingSubdiff f x) (z : X) (hz : f z ≠ ⊤) :
    (f x).toReal + ⟪v, z - x⟫_ℝ ≤ (f z).toReal := by
  obtain ⟨hxtop, xs, vs, hxs, hfxs, hvs, hreg⟩ := hv
  have hzs : f z = ((f z).toReal : EReal) := (EReal.coe_toReal hz (hbot z)).symm
  have hle : ∀ t, (f (xs t)).toReal + ⟪vs t, z - xs t⟫_ℝ ≤ (f z).toReal := by
    intro t
    exact reg_global f hconv (xs t) (vs t) _
      (EReal.coe_toReal (hreg t).1 (hbot _)).symm (hreg t) z _ hzs
  have hT1 : Tendsto (fun t => (f (xs t)).toReal) atTop (𝓝 (f x).toReal) :=
    (EReal.tendsto_toReal hxtop (hbot x)).comp hfxs
  have hT2 : Tendsto (fun t => ⟪vs t, z - xs t⟫_ℝ) atTop (𝓝 ⟪v, z - x⟫_ℝ) :=
    hvs.inner (tendsto_const_nhds.sub hxs)
  exact le_of_tendsto' (hT1.add hT2) hle

end P0909e1e9

open Filter Topology NonconvexSplitting.Shared MoreauProx.Characterization NonsmoothLojasiewicz.Convex InnerProductSpace in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ crit f) :
    ∃ C : ℝ, ∃ U ∈ 𝓝 a, ∀ x ∈ U, ∀ v ∈ LimitingSubdiff f x,
      |(f x).toReal - (⨅ y, f y).toReal| ≤ C * ‖v‖ := by
  obtain ⟨hbot, -, hconv, -⟩ := hf
  have ha' : (0 : EuclideanSpace ℝ (Fin n)) ∈ LimitingSubdiff f a := ha
  have hatop : f a ≠ ⊤ := ha'.1
  have hmin : ∀ z, f a ≤ f z := by
    intro z
    by_cases hz : f z = ⊤
    · rw [hz]; exact le_top
    · have h := P0909e1e9.lim_global f hbot hconv a 0 ha' z hz
      simp only [inner_zero_left, add_zero] at h
      rw [← EReal.coe_toReal hatop (hbot a), ← EReal.coe_toReal hz (hbot z)]
      exact EReal.coe_le_coe_iff.mpr h
  have hinf : (⨅ y, f y) = f a := le_antisymm (iInf_le _ a) (le_iInf hmin)
  refine ⟨1, Metric.ball a 1, Metric.ball_mem_nhds a one_pos, ?_⟩
  intro x hx v hv
  have hxtop : f x ≠ ⊤ := hv.1
  have h := P0909e1e9.lim_global f hbot hconv x v hv a hatop
  have hax : (f a).toReal ≤ (f x).toReal :=
    EReal.toReal_le_toReal (hmin x) (hbot a) hxtop
  rw [hinf, abs_of_nonneg (by linarith)]
  have hd : ‖a - x‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hx
    rwa [norm_sub_rev]
  have hi : -⟪v, a - x⟫_ℝ ≤ ‖v‖ * ‖a - x‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith
