-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.eq5_subdiff_eq_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:36:20.772451+00:00
-- url     : https://prove2.me/submissions/613a5bed-6b28-4187-8f88-8ace17fc6b73

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero

set_option autoImplicit false

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace Pcf93d61b

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

/-- A global (EReal) subgradient inequality gives a regular subgradient. -/
theorem global_reg {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x v : X) (hx : f x ≠ ⊤)
    (hg : ∀ z, f x + ((⟪v, z - x⟫_ℝ : ℝ) : EReal) ≤ f z) : IsRegularSubgrad f x v := by
  refine ⟨hx, fun ε hε => Filter.Eventually.of_forall fun z => ?_⟩
  refine le_trans ?_ (hg z)
  have : ⟪v, z - x⟫_ℝ - ε * ‖z - x‖ ≤ ⟪v, z - x⟫_ℝ := by
    have := mul_nonneg hε.le (norm_nonneg (z - x)); linarith
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr this)

/-- A regular subgradient of a convex never-`⊥` function satisfies the global inequality. -/
theorem reg_global' {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (hconv : EConvex f) (x v : X)
    (hv : IsRegularSubgrad f x v) (z : X) :
    f x + ((⟪v, z - x⟫_ℝ : ℝ) : EReal) ≤ f z := by
  by_cases hz : f z = ⊤
  · rw [hz]; exact le_top
  · have h := reg_global f hconv x v (f x).toReal (EReal.coe_toReal hv.1 (hbot x)).symm hv z
      (f z).toReal (EReal.coe_toReal hz (hbot z)).symm
    rw [← EReal.coe_toReal hv.1 (hbot x), ← EReal.coe_toReal hz (hbot z), ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr h

end Pcf93d61b

open Filter Topology NonconvexSplitting.Shared MoreauProx.Characterization in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (x : EuclideanSpace ℝ (Fin n)) :
    LimitingSubdiff f x = {v | IsRegularSubgrad f x v} ∧
      {v | IsRegularSubgrad f x v} = subgrad f x := by
  obtain ⟨hbot, -, hconv, -⟩ := hf
  refine ⟨?_, ?_⟩
  · ext v
    constructor
    · intro hv
      refine Pcf93d61b.global_reg f x v hv.1 (fun z => ?_)
      by_cases hz : f z = ⊤
      · rw [hz]; exact le_top
      · have h := Pcf93d61b.lim_global f hbot hconv x v hv z hz
        rw [← EReal.coe_toReal hv.1 (hbot x), ← EReal.coe_toReal hz (hbot z), ← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr h
    · intro hv
      exact ⟨hv.1, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
        tendsto_const_nhds, fun _ => hv⟩
  · ext v
    constructor
    · intro hv
      refine ⟨hbot x, hv.1, fun u => ?_⟩
      have := Pcf93d61b.reg_global' f hbot hconv x v hv u
      rwa [real_inner_comm] at this
    · intro hv
      refine Pcf93d61b.global_reg f x v hv.2.1 (fun z => ?_)
      have := hv.2.2 z
      rwa [real_inner_comm] at this
