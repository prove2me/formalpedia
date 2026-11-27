-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PhysicalPrefixAgreementV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:42:04.001062+00:00
-- url     : https://prove2.me/submissions/848c4fb4-5850-479e-81d9-11c45857891a

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open Kyprianou.Ch04 MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
theorem solution :
∀ {Ω : Type} (X L : NNReal → Ω → ℝ) (w : Ω)
    (b : ℝ) (f ft fx g gt gx : ℝ → ℝ → ℝ) (n : ℕ) (τ : NNReal)
    (hτ : τ ≤ (n : NNReal))
    (hX : Measurable (fun t => X t w)) (hL : Measurable (fun t => L t w))
    (hPre : ∀ t < τ, |X t w| ≤ (n : ℝ))
    (hLeft : ∀ t ≤ τ, |L t w| ≤ (n : ℝ))
    (hEq : ∀ s x, 0 ≤ s → s ≤ (n : ℝ) → |x| ≤ (n : ℝ) →
      g s x = f s x ∧ gt s x = ft s x ∧ gx s x = fx s x),
    let μ := pathJumpMeasure X L w
    let D (a : ℝ → ℝ → ℝ) (t : NNReal) :=
      b * (∫ s in Icc (0 : ℝ) (t : ℝ), a s (L s.toNNReal w)) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * a z.1 (L z.1.toNNReal w) ∂μ
    let R (a aTime ax : ℝ → ℝ → ℝ) (t : NNReal) :=
      a (t : ℝ) (X t w) - (a 0 (X 0 w) +
        (∫ s in Icc (0 : ℝ) (t : ℝ), aTime s (X s.toNNReal w) ∂volume) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
          (a z.1 (L z.1.toNNReal w + z.2) - a z.1 (L z.1.toNNReal w) -
            z.2 * ax z.1 (L z.1.toNNReal w)) ∂μ))
    (∀ t ≤ τ, gx (t : ℝ) (L t w) = fx (t : ℝ) (L t w) ∧ D gx t = D fx t) ∧
    (∀ t < τ, R g gt gx t = R f ft fx t)
 := by
  intro Ω X L w b f ft fx g gt gx n τ hτ hX hL hPre hLeft hEq μ D R
  have hTime (t : NNReal) (ht : t ≤ τ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      s.toNNReal ≤ t ∧ s ≤ (n : ℝ) := by
    have hst : s.toNNReal ≤ t := by
      exact Real.toNNReal_le_iff_le_coe.mpr hs.2
    exact ⟨hst,hs.2.trans (by exact_mod_cast ht.trans hτ)⟩
  have hWeight (t : NNReal) (ht : t ≤ τ) :
      gx (t : ℝ) (L t w) = fx (t : ℝ) (L t w) :=
    (hEq _ _ t.coe_nonneg (by exact_mod_cast ht.trans hτ) (hLeft t ht)).2.2
  have hW (t : NNReal) (ht : t ≤ τ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      gx s (L s.toNNReal w) = fx s (L s.toNNReal w) := by
    have h := hWeight s.toNNReal ((hTime t ht s hs).1.trans ht)
    simpa only [Real.coe_toNNReal _ hs.1] using h
  have hMark : ∀ᵐ z ∂μ, z.2 = X z.1.toNNReal w - L z.1.toNNReal w := by
    change ∀ᵐ z ∂pathJumpMeasure X L w, _
    unfold pathJumpMeasure
    apply (ae_map_iff ((NNReal.continuous_coe.measurable).prodMk (hX.sub hL)).aemeasurable
      (measurableSet_eq_fun measurable_snd
        ((hX.comp (measurable_real_toNNReal.comp measurable_fst)).sub
          (hL.comp (measurable_real_toNNReal.comp measurable_fst))))).2
    exact ae_of_all _ (fun t => by simp)
  constructor
  · intro t ht
    refine ⟨hWeight t ht,?_⟩
    dsimp only [D]
    congr 1
    · congr 1
      exact setIntegral_congr_fun measurableSet_Icc (hW t ht)
    · apply setIntegral_congr_fun (measurableSet_Icc.prod
        (measurableSet_le measurable_const measurable_id.abs))
      intro z hz
      exact congrArg (fun a : ℝ => z.2 * a) (hW t ht z.1 hz.1)
  · intro t ht
    have hInner (u : NNReal) (hu : u ≤ t) :=
      hEq (u : ℝ) (X u w) u.coe_nonneg
        (by exact_mod_cast hu.trans (ht.le.trans hτ)) (hPre u (hu.trans_lt ht))
    have h0 : g 0 (X 0 w) = f 0 (X 0 w) := by
      simpa only [NNReal.coe_zero] using (hInner 0 bot_le).1
    have h1 := (hInner t le_rfl).1
    have hdt : (∫ s in Icc (0 : ℝ) (t : ℝ), gt s (X s.toNNReal w) ∂volume) =
        ∫ s in Icc (0 : ℝ) (t : ℝ), ft s (X s.toNNReal w) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      simpa only [Real.coe_toNNReal _ hs.1] using (hInner s.toNNReal
        (hTime t ht.le s hs).1).2.1
    have hj : (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
        (g z.1 (L z.1.toNNReal w + z.2) - g z.1 (L z.1.toNNReal w) -
          z.2 * gx z.1 (L z.1.toNNReal w)) ∂μ) =
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
          (f z.1 (L z.1.toNNReal w + z.2) - f z.1 (L z.1.toNNReal w) -
            z.2 * fx z.1 (L z.1.toNNReal w)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hMark,
        ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz hmem
      have hs := hmem.1
      have hu := (hTime t ht.le z.1 hs).1
      have he := hInner z.1.toNNReal hu
      have hl := hEq z.1 (L z.1.toNNReal w) hs.1
        (hTime t ht.le z.1 hs).2 (hLeft _ (hu.trans ht.le))
      have hs' : L z.1.toNNReal w + z.2 = X z.1.toNNReal w := by rw [hz]; ring
      have he' : g z.1 (X z.1.toNNReal w) = f z.1 (X z.1.toNNReal w) := by
        simpa only [Real.coe_toNNReal _ hs.1] using he.1
      rw [hs',he',hl.1,hl.2.2]
    dsimp only [R]
    rw [h1,h0,hdt,hj]
