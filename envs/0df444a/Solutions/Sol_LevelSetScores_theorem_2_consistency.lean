-- Prove2me | solution 1 for LevelSetScores.theorem_2_consistency
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T03:42:16.196076+00:00
-- url     : https://prove2.me/submissions/07c3fa70-4be9-4d96-8d74-ddf8e00a795c

import Mathlib
import Definitions.Def_LevelSetScores_levelSet
import Definitions.Def_LevelSetScores_weightedMass
import Definitions.Def_LevelSetScores_levelSetScore

open MeasureTheory
open scoped ENNReal

namespace LSSHelp

variable {d : ℕ}

lemma wm_meas (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [SFinite ν]
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    Measurable (LevelSetScores.weightedMass h ν B) := by
  unfold LevelSetScores.weightedMass
  have hg : Measurable (B.indicator (fun z => ENNReal.ofReal (h z))) :=
    (ENNReal.measurable_ofReal.comp hh).indicator hB
  exact (hg.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'

lemma wm_lintegral (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [SFinite ν]
    (P : Measure (EuclideanSpace ℝ (Fin d)))
    (Ξ : EuclideanSpace ℝ (Fin d) → ℝ) (hΞm : Measurable Ξ)
    (hΞ : Measure.conv P ν = volume.withDensity (fun z => ENNReal.ofReal (Ξ z)))
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    ∫⁻ y, LevelSetScores.weightedMass h ν B y ∂P
      = ∫⁻ z in B, ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z) := by
  have hg : Measurable (B.indicator (fun z => ENNReal.ofReal (h z))) :=
    (ENNReal.measurable_ofReal.comp hh).indicator hB
  unfold LevelSetScores.weightedMass
  rw [← Measure.lintegral_conv hg, hΞ,
    lintegral_withDensity_eq_lintegral_mul _ hΞm.ennreal_ofReal hg,
    ← lintegral_indicator hB]
  congr 1
  funext z
  by_cases hz : z ∈ B
  · simp [Set.indicator_of_mem hz, mul_comm]
  · simp [Set.indicator_of_notMem hz]

lemma split_set {X : Type*} [MeasurableSpace X] {μ : Measure X} (f : X → ℝ≥0∞) {B C : Set X}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    ∫⁻ z in B, f z ∂μ = ∫⁻ z in B ∩ C, f z ∂μ + ∫⁻ z in B \ C, f z ∂μ := by
  conv_lhs => rw [← Set.inter_union_sdiff B C]
  exact lintegral_union (B := B \ C) (A := B ∩ C) (hB.diff hC)
    (Set.disjoint_sdiff_right.mono_left Set.inter_subset_right)

lemma arith (a x1 x1' x2 x3 y1 y1' y2 y3 : ℝ≥0∞) (e1 : x1' = x1) (e2 : y1' = y1)
    (b1 : a * x2 ≤ y2) (b2 : y3 ≤ a * x3) :
    a * (x1 + x2) + (y1' + y3) ≤ a * (x1' + x3) + (y1 + y2) := by
  subst e1 e2
  calc a * (x1' + x2) + (y1' + y3) = (a * x1' + y1') + (a * x2 + y3) := by ring
    _ ≤ (a * x1' + y1') + (y2 + a * x3) := add_le_add le_rfl (add_le_add b1 b2)
    _ = a * (x1' + x3) + (y1' + y2) := by ring

/-- expected score as a real number in terms of lintegrals -/
lemma score_integral (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h)
    (hh0 : ∀ z, 0 ≤ h z)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [SFinite ν]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] (α : ℝ)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B)
    (hfin : ∀ᵐ y ∂P, LevelSetScores.weightedMass h ν B y ≠ ∞)
    (hM : ∫⁻ y, LevelSetScores.weightedMass h ν B y ∂P ≠ ∞) :
    ∫ y, LevelSetScores.levelSetScore h ν α B y ∂P
      = α * (∫⁻ z in B, ENNReal.ofReal (h z)).toReal
        - (∫⁻ y, LevelSetScores.weightedMass h ν B y ∂P).toReal := by
  have hm := wm_meas h hh ν hB
  have hint_eq : (∫ z in B, h z) = (∫⁻ z in B, ENNReal.ofReal (h z)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh0)
      hh.aestronglyMeasurable
  unfold LevelSetScores.levelSetScore
  rw [integral_sub (integrable_const _), integral_const, integral_toReal hm.aemeasurable
    (hfin.mono fun y hy => lt_top_iff_ne_top.2 hy)]
  · simp [hint_eq]
  · exact (integrable_toReal_iff hm.aemeasurable hfin).2 hM

end LSSHelp

open MeasureTheory ENNReal LevelSetScores in
theorem solution {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [SFinite ν]
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P]
    {Ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hΞ_meas : Measurable Ξ)
    (hΞ : Measure.conv P ν = volume.withDensity (fun z => ENNReal.ofReal (Ξ z)))
    {α : ℝ} (hα : 0 < α)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A)
    (hA_fin : ∀ᵐ y ∂P, weightedMass h ν A y ≠ ∞)
    (hA_int : Integrable (levelSetScore h ν α A) P) :
    ∫⁻ y, weightedMass h ν (levelSet Ξ α) y ∂P = ∞ ∨
      ((∀ᵐ y ∂P, weightedMass h ν (levelSet Ξ α) y ≠ ∞) ∧
        Integrable (levelSetScore h ν α (levelSet Ξ α)) P ∧
        ∫ y, levelSetScore h ν α (levelSet Ξ α) y ∂P ≤ ∫ y, levelSetScore h ν α A y ∂P) := by
  set L := levelSet Ξ α with hLdef
  have hL : MeasurableSet L := measurableSet_le measurable_const hΞ_meas
  by_cases hML : ∫⁻ y, weightedMass h ν L y ∂P = ∞
  · exact Or.inl hML
  right
  have hmL := LSSHelp.wm_meas h hh_meas ν hL
  have hmA := LSSHelp.wm_meas h hh_meas ν hA
  have hLfin : ∀ᵐ y ∂P, weightedMass h ν L y ≠ ∞ :=
    (ae_lt_top hmL hML).mono fun y hy => hy.ne
  have hAint : Integrable (fun y => (weightedMass h ν A y).toReal) P := by
    have := (integrable_const (α * ∫ z in A, h z) (μ := P)).sub hA_int
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [levelSetScore]
  have hMA : ∫⁻ y, weightedMass h ν A y ∂P ≠ ∞ :=
    (integrable_toReal_iff hmA.aemeasurable hA_fin).1 hAint
  refine ⟨hLfin, ?_, ?_⟩
  · show Integrable (fun y => α * (∫ z in L, h z) - (weightedMass h ν L y).toReal) P
    exact (integrable_const _).sub ((integrable_toReal_iff hmL.aemeasurable hLfin).2 hML)
  rw [LSSHelp.score_integral h hh_meas hh_nonneg ν P α hL hLfin hML,
    LSSHelp.score_integral h hh_meas hh_nonneg ν P α hA hA_fin hMA]
  rw [LSSHelp.wm_lintegral h hh_meas ν P Ξ hΞ_meas hΞ hL] at hML ⊢
  rw [LSSHelp.wm_lintegral h hh_meas ν P Ξ hΞ_meas hΞ hA] at hMA ⊢
  have hFm : Measurable fun z => ENNReal.ofReal (h z) := hh_meas.ennreal_ofReal
  have hGm : Measurable fun z => ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z) :=
    hh_meas.ennreal_ofReal.mul hΞ_meas.ennreal_ofReal
  have htot : ∫⁻ z, ENNReal.ofReal (h z) ≠ ∞ := hh_int.lintegral_lt_top.ne
  have hΛL : ∫⁻ z in L, ENNReal.ofReal (h z) ≠ ∞ :=
    ne_top_of_le_ne_top htot (setLIntegral_le_lintegral _ _)
  have hΛA : ∫⁻ z in A, ENNReal.ofReal (h z) ≠ ∞ :=
    ne_top_of_le_ne_top htot (setLIntegral_le_lintegral _ _)
  set a := ENNReal.ofReal α
  have b1 : a * ∫⁻ z in L \ A, ENNReal.ofReal (h z)
      ≤ ∫⁻ z in L \ A, ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z) := by
    rw [← lintegral_const_mul _ hFm]
    refine setLIntegral_mono hGm fun z hz => ?_
    have : a ≤ ENNReal.ofReal (Ξ z) := ENNReal.ofReal_le_ofReal hz.1
    rw [mul_comm]
    exact mul_le_mul' le_rfl this
  have b2 : ∫⁻ z in A \ L, ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z)
      ≤ a * ∫⁻ z in A \ L, ENNReal.ofReal (h z) := by
    rw [← lintegral_const_mul _ hFm]
    refine setLIntegral_mono (hFm.const_mul _) fun z hz => ?_
    have hz2 : Ξ z < α := lt_of_not_ge hz.2
    have : ENNReal.ofReal (Ξ z) ≤ a := ENNReal.ofReal_le_ofReal hz2.le
    rw [mul_comm]
    exact mul_le_mul' this le_rfl
  have key : a * (∫⁻ z in L, ENNReal.ofReal (h z))
        + ∫⁻ z in A, ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z)
      ≤ a * (∫⁻ z in A, ENNReal.ofReal (h z))
        + ∫⁻ z in L, ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z) := by
    rw [LSSHelp.split_set (fun z => ENNReal.ofReal (h z)) (B := L) hL hA,
      LSSHelp.split_set (fun z => ENNReal.ofReal (h z)) (B := A) hA hL,
      LSSHelp.split_set (fun z => ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z)) (B := L) hL hA,
      LSSHelp.split_set (fun z => ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z)) (B := A) hA hL,
      ]
    refine LSSHelp.arith _ _ _ _ _ _ _ _ _ ?_ ?_ b1 b2
    · rw [Set.inter_comm]
    · rw [Set.inter_comm]
  have hR : a * (∫⁻ z in A, ENNReal.ofReal (h z))
        + ∫⁻ z in L, ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΛA, hML⟩
  have hLe := ENNReal.toReal_mono hR key
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΛL) hMA,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΛA) hML,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le] at hLe
  linarith
