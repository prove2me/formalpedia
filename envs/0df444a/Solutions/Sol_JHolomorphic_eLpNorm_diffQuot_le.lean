-- Prove2me | solution 1 for JHolomorphic.eLpNorm_diffQuot_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T20:23:58.363389+00:00
-- url     : https://prove2.me/submissions/441f7b04-1ee3-4889-9a3f-da15646de76c

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_ae_sub_eq_integral_segment
import Theorems.Thm_JHolomorphic_eLpNorm_segment_average_le
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic



namespace JHolomorphic

open MeasureTheory Metric Filter
open scoped ContDiff

theorem eLpNorm_diffQuot_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (q : ENNReal) (hq : 1 ≤ q) {U : Set ℂ} (hU : IsOpen U)
    {f fs ft : ℂ → E} (hw : HasWeakPartialsOn U f fs ft)
    (hi : ∀ K ⊆ U, IsCompact K → IntegrableOn f K ∧ IntegrableOn fs K ∧ IntegrableOn ft K)
    (v : ℂ) (hv : ‖v‖ = 1) (c : ℂ) (r h : ℝ) (hh : h ≠ 0) (hb : ball c (r + |h|) ⊆ U) :
    eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) q (volume.restrict (ball c r)) ≤
      eLpNorm (fun z => v.re • fs z + v.im • ft z) q (volume.restrict (ball c (r + |h|))) := by
  set W := ball c (r + |h|) with hW
  set g : ℂ → E := fun z => v.re • fs z + v.im • ft z with hg
  set a : ℂ := (h : ℂ) * v with ha
  have hna : ‖a‖ = |h| := by rw [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, hv, mul_one]
  have hgK : ∀ K ⊆ U, IsCompact K → IntegrableOn g K := fun K hK hKc =>
    ((hi K hK hKc).2.1.smul v.re).add ((hi K hK hKc).2.2.smul v.im)
  -- `g` is a.e. strongly measurable on `W`
  have hgm : AEStronglyMeasurable g (volume.restrict W) := by
    have hWU : W = ⋃ n : ℕ, closedBall c (r + |h| - 1 / ((n:ℝ) + 1)) := by
      ext z
      simp only [hW, mem_ball, Set.mem_iUnion, mem_closedBall]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n:ℝ) + 1) := by positivity
        linarith
    rw [hWU, aestronglyMeasurable_iUnion_iff]
    intro n
    refine (hgK _ ?_ (isCompact_closedBall _ _)).aestronglyMeasurable
    refine ((closedBall_subset_ball ?_).trans hb)
    have : 0 < 1 / ((n:ℝ) + 1) := by positivity
    linarith
  set g₀ := W.indicator (hgm.mk g) with hg₀
  have hg₀m : StronglyMeasurable g₀ := hgm.stronglyMeasurable_mk.indicator measurableSet_ball
  have hg₀e : g₀ =ᵐ[volume.restrict W] g := by
    have h1 : g₀ =ᵐ[volume.restrict W] hgm.mk g := indicator_ae_eq_restrict measurableSet_ball
    exact h1.trans hgm.ae_eq_mk.symm
  have hWsub : W ⊆ U := hb
  -- the directional weak derivative of `f` in the direction `a`
  have hd : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ z, fderiv ℝ φ z a • f z = -∫ z, φ z • (h • g₀ z) := by
    intro φ hφ hφc hφW
    have hφU : tsupport φ ⊆ U := hφW.trans hWsub
    have hfi : ∀ K ⊆ U, IsCompact K → IntegrableOn f K := fun K hK hKc => (hi K hK hKc).1
    have hfsi : ∀ K ⊆ U, IsCompact K → IntegrableOn fs K := fun K hK hKc => (hi K hK hKc).2.1
    have hfti : ∀ K ⊆ U, IsCompact K → IntegrableOn ft K := fun K hK hKc => (hi K hK hKc).2.2
    obtain ⟨hs1, hs2, hs3⟩ := fderiv_apply_isTestFunction hφ hφc hφU 1
    obtain ⟨ht1, ht2, ht3⟩ := fderiv_apply_isTestFunction hφ hφc hφU Complex.I
    have i1 := integrable_smul_of_integrableOn_compact hfi hs1.continuous.continuousOn hs2 hs3
    have i2 := integrable_smul_of_integrableOn_compact hfi ht1.continuous.continuousOn ht2 ht3
    have i3 := integrable_smul_of_integrableOn_compact hfsi hφ.continuous.continuousOn hφc hφU
    have i4 := integrable_smul_of_integrableOn_compact hfti hφ.continuous.continuousOn hφc hφU
    obtain ⟨w1, w2⟩ := hw φ hφ hφc hφU
    have hdec : a = (h * v.re) • (1:ℂ) + (h * v.im) • Complex.I := by
      apply Complex.ext <;> simp [ha]
    have hL : ∀ z, fderiv ℝ φ z a • f z =
        (h * v.re) • (fderiv ℝ φ z 1 • f z) + (h * v.im) • (fderiv ℝ φ z Complex.I • f z) := by
      intro z
      rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, add_smul]
      simp only [smul_smul]
    have hR : ∫ z, φ z • (h • g₀ z) = ∫ z, φ z • (h • g z) := by
      have hz0 : ∀ z ∉ W, φ z = 0 := fun z hz =>
        image_eq_zero_of_notMem_tsupport (fun h' => hz (hφW h'))
      have e1 := setIntegral_eq_integral_of_forall_compl_eq_zero (s := W) (μ := volume)
        (f := fun z => φ z • (h • g₀ z)) (fun z hz => by simp [hz0 z hz])
      have e2 := setIntegral_eq_integral_of_forall_compl_eq_zero (s := W) (μ := volume)
        (f := fun z => φ z • (h • g z)) (fun z hz => by simp [hz0 z hz])
      rw [← e1, ← e2]
      refine setIntegral_congr_ae measurableSet_ball ?_
      have := (ae_restrict_iff' measurableSet_ball).1 hg₀e
      filter_upwards [this] with z hz hzW
      rw [hz hzW]
    have hR2 : ∀ z, φ z • (h • g z) = (h * v.re) • (φ z • fs z) + (h * v.im) • (φ z • ft z) := by
      intro z
      simp only [hg, smul_add, smul_smul]
      ring_nf
    have j1 : Integrable fun z => (h * v.re) • (fderiv ℝ φ z 1 • f z) := i1.smul (h * v.re)
    have j2 : Integrable fun z => (h * v.im) • (fderiv ℝ φ z Complex.I • f z) :=
      i2.smul (h * v.im)
    have j3 : Integrable fun z => (h * v.re) • (φ z • fs z) := i3.smul (h * v.re)
    have j4 : Integrable fun z => (h * v.im) • (φ z • ft z) := i4.smul (h * v.im)
    rw [hR, integral_congr_ae (Eventually.of_forall hL), integral_congr_ae (Eventually.of_forall hR2),
      integral_add j1 j2, integral_add j3 j4,
      integral_smul, integral_smul, integral_smul, integral_smul, w1, w2]
    simp only [smul_neg, neg_add]
  have hA := ae_sub_eq_integral_segment (W := W) (f := f) (G := fun z => h • g₀ z) a hd
    (fun K hK hKc => (hi K (hK.trans hWsub) hKc).1) (hg₀m.const_smul h)
    (fun K hK hKc => by
      have hgK' : IntegrableOn g K := hgK K (hK.trans hWsub) hKc
      have he : g₀ =ᵐ[volume.restrict K] g := ae_restrict_of_ae_restrict_of_subset hK hg₀e
      exact (hgK'.congr_fun_ae he.symm).smul h)
    c r (by rw [hna])
  have hDQ : (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) =ᵐ[volume.restrict (ball c r)]
      fun z => ∫ t in (0:ℝ)..1, g₀ (z + (t:ℂ) * a) := by
    filter_upwards [hA] with z hz
    rw [← ha, hz, intervalIntegral.integral_smul, inv_smul_smul₀ hh]
  rw [eLpNorm_congr_ae hDQ]
  calc eLpNorm (fun z => ∫ t in (0:ℝ)..1, g₀ (z + (t:ℂ) * a)) q (volume.restrict (ball c r))
      ≤ eLpNorm g₀ q (volume.restrict (ball c (r + ‖a‖))) :=
        eLpNorm_segment_average_le hg₀m hq a c r
    _ = eLpNorm g q (volume.restrict W) := by
        rw [hna]; exact eLpNorm_congr_ae hg₀e

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (q : ENNReal) (hq : 1 ≤ q) {U : Set ℂ} (hU : IsOpen U)
    {f fs ft : ℂ → E} (hw : HasWeakPartialsOn U f fs ft)
    (hi : ∀ K ⊆ U, IsCompact K → IntegrableOn f K ∧ IntegrableOn fs K ∧ IntegrableOn ft K)
    (v : ℂ) (hv : ‖v‖ = 1) (c : ℂ) (r h : ℝ) (hh : h ≠ 0) (hb : ball c (r + |h|) ⊆ U) :
    eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) q (volume.restrict (ball c r)) ≤
      eLpNorm (fun z => v.re • fs z + v.im • ft z) q (volume.restrict (ball c (r + |h|))) :=
  eLpNorm_diffQuot_le_aux q hq hU hw hi v hv c r h hh hb
