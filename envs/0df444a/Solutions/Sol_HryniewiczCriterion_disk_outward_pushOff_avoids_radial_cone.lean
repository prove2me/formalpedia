-- Prove2me | solution 1 for HryniewiczCriterion.disk_outward_pushOff_avoids_radial_cone
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T02:35:13.384322+00:00
-- url     : https://prove2.me/submissions/3242eb71-32b2-4759-b8e1-c6cccabc5120

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Algebra.Order.Round

open HryniewiczCriterion
open scoped ContDiff
open scoped ContDiff Topology
open Set Filter Topology

/-- A smooth map whose differential at `p` is injective has a smooth local left inverse
near `e p`: there is `g`, smooth at `e p`, with `g (e q) = q` for all `q` near `p`. -/
theorem exists_contDiffAt_leftInverse_of_injective_fderiv_aux
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : E → F} {p : E} (he : ContDiffAt ℝ ∞ e p)
    (hinj : Function.Injective (fderiv ℝ e p)) :
    ∃ g : F → E, ContDiffAt ℝ ∞ g (e p) ∧ ∀ᶠ q in 𝓝 p, g (e q) = q := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨L, hL⟩ := ((fderiv ℝ e p : E →L[ℝ] F) : E →ₗ[ℝ] F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  let Lc : F →L[ℝ] E := LinearMap.toContinuousLinearMap L
  let f : E → E := fun q => Lc (e q)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hcomp : Lc.comp (fderiv ℝ e p) = ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) := by
    ext v
    have := congrArg (fun φ : E →ₗ[ℝ] E => φ v) hL
    simpa [Lc] using this
  have hfd : HasFDerivAt f ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) p := by
    rw [← hcomp]
    exact Lc.hasFDerivAt.comp p (he.differentiableAt (by simp)).hasFDerivAt
  have hf : ContDiffAt ℝ ∞ f p := Lc.contDiff.contDiffAt.comp p he
  refine ⟨fun y => hf.localInverse hfd hn (Lc y), ?_, ?_⟩
  · exact (hf.to_localInverse hfd hn).comp (e p) Lc.contDiff.contDiffAt
  · exact (hf.hasStrictFDerivAt' hfd hn).eventually_left_inverse

/-!
# Seifert push-off: the outward push-off misses the cone over the disk

For a smooth disk `e` transverse to the radial direction along `D`, and a loop `u` on the
boundary circle with an outward field `a` (`⟨u, a⟩ > 0`), the points
`e(u) + ε de(u) a` miss the cone `{μ e(v) : v ∈ D, μ ≥ 0}` for all small `ε > 0`.
-/


noncomputable section

namespace HryniewiczCriterion

lemma sf_disk_compact : IsCompact closedUnitDisk := by
  have hcl : IsClosed closedUnitDisk :=
    isClosed_le (by fun_prop) continuous_const
  have hsub : closedUnitDisk ⊆ Metric.closedBall (0 : Plane) 1 := by
    intro v hv
    simp only [closedUnitDisk, mem_setOf_eq] at hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    have h0 : |v 0| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (v 1)])
    have h1 : |v 1| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (v 0)])
    revert i
    exact Fin.forall_fin_two.2 ⟨h0, h1⟩
  exact Metric.isCompact_of_isClosed_isBounded hcl (Metric.isBounded_closedBall.subset hsub)

/-- Local picture at a boundary point: a function `f`, strictly differentiable at `e u₀`,
with `f (μ e v) = |v|²` near `(u₀, 1)` and `f' (de(u₀) a₀) = 2 ⟨u₀, a₀⟩ > 0`. -/
lemma sf_local (e : Plane → R4) (hE : ContDiff ℝ ∞ e) (u₀ a₀ : Plane)
    (hinj : Function.Injective (fderiv ℝ e u₀)) (htr : e u₀ ∉ range (fderiv ℝ e u₀))
    (hua : 0 < u₀ 0 * a₀ 0 + u₀ 1 * a₀ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (f : R4 → ℝ) (f' : R4 →L[ℝ] ℝ), HasStrictFDerivAt f f' (e u₀) ∧
      0 < f' (fderiv ℝ e u₀ a₀) ∧
      ∀ (v : Plane) (μ : ℝ), ‖v - u₀‖ < δ → |μ - 1| < δ → f (μ • e v) = v 0 ^ 2 + v 1 ^ 2 := by
  set G : Plane × ℝ → R4 := fun p => p.2 • e p.1 with hGdef
  set p₀ : Plane × ℝ := (u₀, 1) with hp₀
  have hG : ContDiff ℝ ∞ G := contDiff_snd.smul (hE.comp contDiff_fst)
  have hde : HasFDerivAt e (fderiv ℝ e u₀) u₀ := ((hE.differentiable (by simp)) u₀).hasFDerivAt
  have hGd : HasFDerivAt G (p₀.2 • (fderiv ℝ e u₀).comp (ContinuousLinearMap.fst ℝ Plane ℝ) +
      (ContinuousLinearMap.snd ℝ Plane ℝ).smulRight (e p₀.1)) p₀ :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀)).smul (hde.comp p₀ (hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)))
  have hGq : ∀ q : Plane × ℝ, fderiv ℝ G p₀ q = fderiv ℝ e u₀ q.1 + q.2 • e u₀ := by
    intro q; rw [hGd.fderiv]; simp [p₀]
  have hGinj : Function.Injective (fderiv ℝ G p₀) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    rw [hGq] at hq
    have hde1 : fderiv ℝ e u₀ q.1 = -(q.2 • e u₀) := eq_neg_of_add_eq_zero_left hq
    by_cases hm : q.2 = 0
    · rw [hm, zero_smul, neg_zero] at hde1
      have h1 : q.1 = 0 := hinj (by rw [hde1, map_zero])
      exact Prod.ext h1 hm
    · exfalso
      apply htr
      refine ⟨-(q.2)⁻¹ • q.1, ?_⟩
      rw [map_smul, hde1, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hm, one_smul]
  obtain ⟨L, hL, hLG⟩ := exists_contDiffAt_leftInverse_of_injective_fderiv_aux
    (hG.contDiffAt (x := p₀)) hGinj
  have hGp : G p₀ = e u₀ := by simp [G, p₀]
  rw [hGp] at hL
  set f : R4 → ℝ := fun y => (L y).1 0 ^ 2 + (L y).1 1 ^ 2 with hfdef
  have hfC : ContDiffAt ℝ ∞ f (e u₀) := by
    have h0 : ContDiffAt ℝ ∞ (fun y => (L y).1 0) (e u₀) :=
      ((contDiff_apply ℝ ℝ (0 : Fin 2)).comp contDiff_fst).contDiffAt.comp _ hL
    have h1 : ContDiffAt ℝ ∞ (fun y => (L y).1 1) (e u₀) :=
      ((contDiff_apply ℝ ℝ (1 : Fin 2)).comp contDiff_fst).contDiffAt.comp _ hL
    exact (h0.pow 2).add (h1.pow 2)
  have hfs : HasStrictFDerivAt f (fderiv ℝ f (e u₀)) (e u₀) := hfC.hasStrictFDerivAt (by simp)
  obtain ⟨δ, hδ, hδL⟩ := Metric.eventually_nhds_iff.1 hLG
  have hfG : ∀ (v : Plane) (μ : ℝ), ‖v - u₀‖ < δ → |μ - 1| < δ →
      f (μ • e v) = v 0 ^ 2 + v 1 ^ 2 := by
    intro v μ hv hμ
    have hd : dist (v, μ) p₀ < δ := by
      rw [Prod.dist_eq]
      exact max_lt (by rwa [dist_eq_norm]) (by rwa [Real.dist_eq])
    have := hδL hd
    simp only [G] at this
    simp only [f, this]
  refine ⟨δ, hδ, f, fderiv ℝ f (e u₀), hfs, ?_, hfG⟩
  -- the derivative along the curve `t ↦ e (u₀ + t a₀)`
  have hl : HasDerivAt (fun t : ℝ => u₀ + t • a₀) a₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a₀).const_add u₀
  have hc : HasDerivAt (fun t : ℝ => e (u₀ + t • a₀)) (fderiv ℝ e u₀ a₀) 0 :=
    hde.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h1 : HasDerivAt (fun t : ℝ => f (e (u₀ + t • a₀))) (fderiv ℝ f (e u₀) (fderiv ℝ e u₀ a₀)) 0 :=
    hfs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hp0 : HasDerivAt (fun t : ℝ => u₀ 0 + t * a₀ 0) (a₀ 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a₀ 0)).const_add (u₀ 0)
  have hp1 : HasDerivAt (fun t : ℝ => u₀ 1 + t * a₀ 1) (a₀ 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a₀ 1)).const_add (u₀ 1)
  have h2 := (hp0.pow 2).add (hp1.pow 2)
  have hev : (fun t : ℝ => f (e (u₀ + t • a₀))) =ᶠ[𝓝 0]
      fun t : ℝ => (u₀ 0 + t * a₀ 0) ^ 2 + (u₀ 1 + t * a₀ 1) ^ 2 := by
    have ht : Tendsto (fun t : ℝ => u₀ + t • a₀) (𝓝 0) (𝓝 u₀) := by
      have : Continuous (fun t : ℝ => u₀ + t • a₀) := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [ht (Metric.ball_mem_nhds u₀ hδ)] with t htb
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at htb
    have := hfG (u₀ + t • a₀) 1 htb (by simpa using hδ)
    rw [one_smul] at this
    exact this.trans (by simp [smul_eq_mul])
  have := h1.unique (h2.congr_of_eventuallyEq hev)
  rw [this]
  norm_num
  linarith

lemma sf_periodic_fract {α : Type*} {u : ℝ → α} (huper : ∀ s, u (s + 1) = u s) (x : ℝ) :
    u (Int.fract x) = u x := by
  rw [← Int.self_sub_floor, show x - (⌊x⌋ : ℝ) = x - ((⌊x⌋ : ℤ) : ℝ) * 1 by ring]
  exact Function.Periodic.sub_int_mul_eq (f := u) (c := (1 : ℝ)) huper ⌊x⌋

/-- The outward push-off of the boundary misses the cone over the disk. -/
theorem sf_separation (e : Plane → R4) (hE : ContDiff ℝ ∞ e)
    (hinjD : InjOn e closedUnitDisk)
    (hinj : ∀ v ∈ closedUnitDisk, Function.Injective (fderiv ℝ e v))
    (htr : ∀ v ∈ closedUnitDisk, e v ∉ range (fderiv ℝ e v))
    (h0 : ∀ v ∈ closedUnitDisk, e v ≠ 0)
    (hrad : ∀ v ∈ closedUnitDisk, ∀ v' ∈ closedUnitDisk, ∀ μ : ℝ, 0 < μ → μ • e v = e v' → μ = 1)
    (u a : ℝ → Plane) (hu : Continuous u) (ha : Continuous a)
    (huper : ∀ s, u (s + 1) = u s) (haper : ∀ s, a (s + 1) = a s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hua : ∀ s, 0 < u s 0 * a s 0 + u s 1 * a s 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s, ∀ v ∈ closedUnitDisk, ∀ μ : ℝ, 0 ≤ μ →
      e (u s) + ε • fderiv ℝ e (u s) (a s) ≠ μ • e v := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε < 1 / ((n : ℝ) + 1) ∧ ∃ s, ∃ v ∈ closedUnitDisk,
      ∃ μ : ℝ, 0 ≤ μ ∧ e (u s) + ε • fderiv ℝ e (u s) (a s) = μ • e v :=
    fun n => hcon _ (by positivity)
  choose ε hε hεlt s v hv μ hμ heq using hseq
  set t : ℕ → ℝ := fun n => Int.fract (s n)
  have heq' : ∀ n, e (u (t n)) + ε n • fderiv ℝ e (u (t n)) (a (t n)) = μ n • e (v n) := by
    intro n; simp only [t, sf_periodic_fract huper, sf_periodic_fract haper]; exact heq n
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedUnitDisk) := isCompact_Icc.prod sf_disk_compact
  have hmem : ∀ n, (t n, v n) ∈ Icc (0 : ℝ) 1 ×ˢ closedUnitDisk :=
    fun n => ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hv n⟩
  obtain ⟨⟨s₀, v₀⟩, ⟨_, hv₀⟩, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have ht : Tendsto (fun n => t (φ n)) atTop (𝓝 s₀) := (continuous_fst.tendsto _).comp hlim
  have hvl : Tendsto (fun n => v (φ n)) atTop (𝓝 v₀) := (continuous_snd.tendsto _).comp hlim
  have hεl : Tendsto (fun n => ε (φ n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hε _).le) (fun n => ?_)
    refine (hεlt (φ n)).le.trans ?_
    have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  set x₀ := e (u s₀)
  set z₀ := fderiv ℝ e (u s₀) (a s₀)
  have hcz : Continuous fun s => fderiv ℝ e (u s) (a s) :=
    ((hE.continuous_fderiv (by simp)).comp hu).clm_apply ha
  have hxl : Tendsto (fun n => e (u (t (φ n)))) atTop (𝓝 x₀) :=
    ((hE.continuous.comp hu).tendsto s₀).comp ht
  have hzl : Tendsto (fun n => fderiv ℝ e (u (t (φ n))) (a (t (φ n)))) atTop (𝓝 z₀) :=
    (hcz.tendsto s₀).comp ht
  have hyl : Tendsto (fun n => e (u (t (φ n))) + ε (φ n) • fderiv ℝ e (u (t (φ n))) (a (t (φ n))))
      atTop (𝓝 x₀) := by simpa using hxl.add (hεl.smul hzl)
  have hμeq : ∀ n, μ n = ‖e (u (t n)) + ε n • fderiv ℝ e (u (t n)) (a (t n))‖ / ‖e (v n)‖ := by
    intro n
    rw [heq' n, norm_smul, Real.norm_of_nonneg (hμ n), mul_div_assoc,
      div_self (norm_ne_zero_iff.2 (h0 _ (hv n))), mul_one]
  have hev : Tendsto (fun n => e (v (φ n))) atTop (𝓝 (e v₀)) := (hE.continuous.tendsto v₀).comp hvl
  have hμl : Tendsto (fun n => μ (φ n)) atTop (𝓝 (‖x₀‖ / ‖e v₀‖)) := by
    simp_rw [hμeq]
    exact hyl.norm.div hev.norm (norm_ne_zero_iff.2 (h0 v₀ hv₀))
  set μ₀ := ‖x₀‖ / ‖e v₀‖
  have hyl' : Tendsto (fun n => e (u (t (φ n))) + ε (φ n) • fderiv ℝ e (u (t (φ n))) (a (t (φ n))))
      atTop (𝓝 (μ₀ • e v₀)) := by
    simp_rw [heq']; exact hμl.smul hev
  have hx₀eq : x₀ = μ₀ • e v₀ := tendsto_nhds_unique hyl hyl'
  have hu₀D : u s₀ ∈ closedUnitDisk := le_of_eq (hucirc s₀)
  have hx₀ne : x₀ ≠ 0 := h0 _ hu₀D
  have hμ₀pos : 0 < μ₀ := div_pos (norm_pos_iff.2 hx₀ne) (norm_pos_iff.2 (h0 v₀ hv₀))
  have hμ₀1 : μ₀ = 1 := hrad v₀ hv₀ (u s₀) hu₀D μ₀ hμ₀pos hx₀eq.symm
  have hvu : v₀ = u s₀ := hinjD hv₀ hu₀D (by rw [show e (u s₀) = x₀ from rfl, hx₀eq, hμ₀1, one_smul])
  rw [hμ₀1] at hμl
  rw [hvu] at hvl
  obtain ⟨δ, hδ, f, f', hf, hf'pos, hfG⟩ :=
    sf_local e hE (u s₀) (a s₀) (hinj _ hu₀D) (htr _ hu₀D) (hua s₀)
  rw [hasStrictFDerivAt_iff_isLittleO] at hf
  set κ := f' z₀
  have hκ : 0 < κ := hf'pos
  set c := κ / (4 * (‖z₀‖ + 1))
  have hc : 0 < c := by positivity
  have E1 := (hyl.prodMk_nhds hxl).eventually (hf.def hc)
  have E2 := hvl.eventually (Metric.ball_mem_nhds (u s₀) hδ)
  have E3 := hμl.eventually (Metric.ball_mem_nhds 1 hδ)
  have E4 := (((hu.tendsto s₀).comp ht)).eventually (Metric.ball_mem_nhds (u s₀) hδ)
  have E5 := ((f'.continuous.tendsto z₀).comp hzl).eventually (lt_mem_nhds (half_lt_self hκ))
  have E6 := hzl.norm.eventually (gt_mem_nhds (lt_add_one ‖z₀‖))
  obtain ⟨n, h1, h2, h3, h4, h5, h6⟩ := (E1.and (E2.and (E3.and (E4.and (E5.and E6))))).exists
  simp only [Function.comp_apply, Metric.mem_ball, dist_eq_norm, Real.dist_eq] at h1 h2 h3 h4 h5 h6
  set m := φ n
  set Z := fderiv ℝ e (u (t m)) (a (t m))
  have hfy : f (e (u (t m)) + ε m • Z) = v m 0 ^ 2 + v m 1 ^ 2 := by
    rw [heq' m]; exact hfG _ _ h2 h3
  have hfx : f (e (u (t m))) = 1 := by
    have := hfG (u (t m)) 1 h4 (by simpa using hδ)
    rw [one_smul] at this
    rw [this]; exact hucirc (t m)
  have hvle : v m 0 ^ 2 + v m 1 ^ 2 ≤ 1 := hv m
  rw [hfy, hfx, add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul,
    Real.norm_of_nonneg (hε m).le, Real.norm_eq_abs] at h1
  have hlow := neg_abs_le (v m 0 ^ 2 + v m 1 ^ 2 - 1 - ε m * f' Z)
  have hcz' : c * ‖Z‖ ≤ κ / 4 := by
    have : c * ‖Z‖ ≤ c * (‖z₀‖ + 1) := mul_le_mul_of_nonneg_left h6.le hc.le
    calc c * ‖Z‖ ≤ c * (‖z₀‖ + 1) := this
      _ = κ / 4 := by simp only [c]; field_simp
  have hεm := hε m
  nlinarith [mul_le_mul_of_nonneg_left hcz' hεm.le, mul_lt_mul_of_pos_left h5 hεm]

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (e : Plane → R4) (hE : ContDiff ℝ ∞ e)
    (hinjD : Set.InjOn e closedUnitDisk)
    (hinj : ∀ v ∈ closedUnitDisk, Function.Injective (fderiv ℝ e v))
    (htr : ∀ v ∈ closedUnitDisk, e v ∉ Set.range (fderiv ℝ e v))
    (h0 : ∀ v ∈ closedUnitDisk, e v ≠ 0)
    (hrad : ∀ v ∈ closedUnitDisk, ∀ v' ∈ closedUnitDisk, ∀ μ : ℝ, 0 < μ → μ • e v = e v' → μ = 1)
    (u a : ℝ → Plane) (hu : Continuous u) (ha : Continuous a)
    (huper : ∀ s, u (s + 1) = u s) (haper : ∀ s, a (s + 1) = a s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hua : ∀ s, 0 < u s 0 * a s 0 + u s 1 * a s 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s, ∀ v ∈ closedUnitDisk, ∀ μ : ℝ, 0 ≤ μ →
      e (u s) + ε • fderiv ℝ e (u s) (a s) ≠ μ • e v :=
  sf_separation e hE hinjD hinj htr h0 hrad u a hu ha huper haper hucirc hua
