-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_certain_record_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:30:43.011182+00:00
-- url     : https://prove2.me/submissions/0f9f87d1-f427-4461-998d-51050a4433cf


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Zero slope path reduction. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (l a : ℝ),
      (∫ ω, if tauPlus X l ω < reflectedSupExit X 0 a ω
        then discountedAt 0 (tauPlus X l ω) else 0 ∂P) = 1 →
      ∀ᵐ ω ∂P, tauPlus X l ω < reflectedSupExit X 0 a ω := by
  intro Ω mΩ P hP X l a h
  let f := fun ω => if tauPlus X l ω < reflectedSupExit X 0 a ω then (1:ℝ) else 0
  have he : (fun ω => if tauPlus X l ω < reflectedSupExit X 0 a ω
      then discountedAt 0 (tauPlus X l ω) else 0) = f := by
    funext ω
    by_cases hv : tauPlus X l ω < reflectedSupExit X 0 a ω
    · obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hv.trans_le le_top))
      simp [f,hv,← ht,discountedAt]
    · simp [f,hv]
  rw [he] at h
  have hi : Integrable f P := by
    by_contra hn
    rw [integral_undef hn] at h
    norm_num at h
  have h0 : ∫ ω, (1-f ω) ∂P = 0 := by
    rw [integral_sub (integrable_const _) hi,h]
    simp
  have hp : 0 ≤ (fun ω => 1-f ω) := by
    intro ω
    dsimp [f]
    split <;> norm_num
  have hz := (integral_eq_zero_iff_of_nonneg hp ((integrable_const _).sub hi)).1 h0
  filter_upwards [hz] with ω hw
  by_contra hn
  simp [f,hn] at hw
