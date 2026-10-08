-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.crit_closed_convex_eq_argmin
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:07:47.882613+00:00
-- url     : https://prove2.me/submissions/49322114-0c90-46da-9b4f-f444c6b8934a

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

set_option autoImplicit false

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace B8ce02bdAux

open scoped InnerProductSpace

/-- Sublevel sets of an `EConvex` function at real levels are convex. -/
theorem sublevel_convex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} (hf : EConvex f) (c : ℝ) : Convex ℝ {x | f x ≤ (c : EReal)} := by
  intro x hx y hy a b ha hb hab
  have h := hf (x := (x, c)) (y := (y, c)) hx hy ha hb hab
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at h
  rw [← add_mul, hab, one_mul] at h
  exact h

/-- The convexity inequality along a segment, for finite values. -/
theorem seg_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} (hf : EConvex f) {x y : H} {a b : ℝ} (hx : f x = a) (hy : f y = b)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (x + t • (y - x)) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hxm : (x, a) ∈ {p : H × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
    simp [hx]
  have hym : (y, b) ∈ {p : H × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
    simp [hy]
  have h := hf hxm hym (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at h
  have he : (1 - t) • x + t • y = x + t • (y - x) := by
    rw [sub_smul, smul_sub, one_smul]; abel
  rw [he] at h
  exact h

/-- For a convex function, a regular subgradient is a global subgradient. -/
theorem reg_global {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} (hf : EConvex f) (hbot : ∀ z, f z ≠ ⊥) {x v : H}
    (hreg : IsRegularSubgrad f x v) (y : H) :
    f x + ((⟪v, y - x⟫_ℝ : ℝ) : EReal) ≤ f y := by
  by_cases hyt : f y = ⊤
  · rw [hyt]; exact le_top
  obtain ⟨hxt, hr⟩ := hreg
  set a := (f x).toReal with ha
  set b := (f y).toReal with hb
  have hxa : f x = (a : EReal) := (EReal.coe_toReal hxt (hbot x)).symm
  have hyb : f y = (b : EReal) := (EReal.coe_toReal hyt (hbot y)).symm
  -- key real inequality: for each ε > 0
  have key : ∀ ε : ℝ, 0 < ε → ⟪v, y - x⟫_ℝ - ε * ‖y - x‖ ≤ b - a := by
    intro ε hε
    have hev := hr ε hε
    have hcont : Tendsto (fun t : ℝ => x + t • (y - x)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
      have h0 := this.tendsto 0
      simp only [zero_smul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have h1 := hcont.eventually hev
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := by
      have : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
      exact this.filter_mono nhdsWithin_le_nhds
    have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht, ht1, ht0⟩ := (h1.and (h2.and h3)).exists
    have hseg := seg_le hf hxa hyb ht0.le ht1.le
    have hc := ht.trans hseg
    have hzx : x + t • (y - x) - x = t • (y - x) := by abel
    rw [hzx, hxa, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hc
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hc
    have : t * (⟪v, y - x⟫_ℝ - ε * ‖y - x‖) ≤ t * (b - a) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  have hreal : ⟪v, y - x⟫_ℝ ≤ b - a := by
    by_contra hcon
    push_neg at hcon
    set d := ⟪v, y - x⟫_ℝ - (b - a) with hd
    have hdpos : 0 < d := by linarith
    have hn : 0 ≤ ‖y - x‖ := norm_nonneg _
    have hεpos : 0 < d / (2 * (‖y - x‖ + 1)) := by positivity
    have hk := key _ hεpos
    have hlt : d / (2 * (‖y - x‖ + 1)) * ‖y - x‖ < d := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hxa, hyb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

end B8ce02bdAux

open Filter Topology NonconvexSplitting.Shared MoreauProx.Characterization NonsmoothLojasiewicz.Convex in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) :
    IsClosed (crit f) ∧ Convex ℝ (crit f) ∧
      crit f = {x | ∀ y, f x ≤ f y} := by
  obtain ⟨hbot, ⟨y0, hy0⟩, hconv, hlsc⟩ := hf
  have hEq : crit f = {x | ∀ y, f x ≤ f y} := by
    ext x
    constructor
    · rintro ⟨hxt, xs, vs, hxs, hfx, hvs, hreg⟩ y
      by_cases hyt : f y = ⊤
      · rw [hyt]; exact le_top
      have glob : ∀ t, f (xs t) + ((inner ℝ (vs t) (y - xs t) : ℝ) : EReal) ≤ f y :=
        fun t => B8ce02bdAux.reg_global hconv hbot (hreg t) y
      have hin : Tendsto (fun t => inner ℝ (vs t) (y - xs t)) atTop
          (𝓝 (inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (y - x))) :=
        hvs.inner (tendsto_const_nhds.sub hxs)
      rw [inner_zero_left] at hin
      have hin' : Tendsto (fun t => ((inner ℝ (vs t) (y - xs t) : ℝ) : EReal)) atTop
          (𝓝 ((0 : ℝ) : EReal)) :=
        (continuous_coe_real_ereal.tendsto _).comp hin
      have hsum : Tendsto (fun t => f (xs t) + ((inner ℝ (vs t) (y - xs t) : ℝ) : EReal))
          atTop (𝓝 (f x + ((0 : ℝ) : EReal))) := by
        have hca := EReal.continuousAt_add (p := (f x, ((0 : ℝ) : EReal)))
          (Or.inl hxt) (Or.inl (hbot x))
        exact hca.tendsto.comp (hfx.prodMk_nhds hin')
      have := le_of_tendsto' hsum glob
      simpa using this
    · intro hx
      have hxt : f x ≠ ⊤ := ne_top_of_le_ne_top hy0 (hx y0)
      refine ⟨hxt, fun _ => x, fun _ => 0, tendsto_const_nhds, tendsto_const_nhds,
        tendsto_const_nhds, fun _ => ⟨hxt, fun ε hε => Eventually.of_forall fun z => ?_⟩⟩
      have hle : ((inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (z - x) - ε * ‖z - x‖ : ℝ) : EReal)
          ≤ 0 := by
        rw [inner_zero_left]
        have : (0 : ℝ) - ε * ‖z - x‖ ≤ 0 := by
          have := mul_nonneg hε.le (norm_nonneg (z - x)); linarith
        exact_mod_cast this
      calc f x + ((inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (z - x) - ε * ‖z - x‖ : ℝ) : EReal)
          ≤ f x + 0 := add_le_add le_rfl hle
        _ = f x := add_zero _
        _ ≤ f z := hx z
  have hset : {x : EuclideanSpace ℝ (Fin n) | ∀ y, f x ≤ f y} = ⋂ y, f ⁻¹' Set.Iic (f y) := by
    ext x; simp
  refine ⟨?_, ?_, hEq⟩
  · rw [hEq, hset]
    exact isClosed_iInter fun y => hlsc.isClosed_preimage (f y)
  · rw [hEq, hset]
    refine convex_iInter fun y => ?_
    by_cases hyt : f y = ⊤
    · have : f ⁻¹' Set.Iic (f y) = Set.univ := by
        ext z; simp [hyt]
      rw [this]; exact convex_univ
    · have hyr : f y = (((f y).toReal : ℝ) : EReal) := (EReal.coe_toReal hyt (hbot y)).symm
      rw [hyr]
      exact B8ce02bdAux.sublevel_convex hconv _
