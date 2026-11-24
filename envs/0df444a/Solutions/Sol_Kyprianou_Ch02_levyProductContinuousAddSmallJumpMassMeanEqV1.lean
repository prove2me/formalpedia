-- Prove2me | solution 1 for Kyprianou.Ch02.levyProductContinuousAddSmallJumpMassMeanEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:05:49.841327+00:00
-- url     : https://prove2.me/submissions/7a863da6-fab6-4b61-9de5-85e5a9cd0aa9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_cadlagJumpOfAddContinuousV1
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch02_cadlagSmallJumpMassBorelFunctionalV1
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : ∀ η : Λ, Continuous (fun t => Y t η))
    (T : ℝ≥0) :
    (∫⁻ p : Ω × Λ, ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal
          (if |(fun t (q : Ω × Λ) => X t q.1 + Y t q.2) (s : ℝ≥0) p -
                Function.leftLim (fun u : ℝ≥0 => (fun t (q : Ω × Λ) => X t q.1 + Y t q.2) u p) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |(fun t (q : Ω × Λ) => X t q.1 + Y t q.2) (s : ℝ≥0) p -
                Function.leftLim (fun u : ℝ≥0 => (fun t (q : Ω × Λ) => X t q.1 + Y t q.2) u p) (s : ℝ≥0)|
           else 0) ∂(P.prod Q)) =
      (∫⁻ ω : Ω, ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) T, ENNReal.ofReal
      (if |X s ω - Function.leftLim (fun u => X u ω) s| ≤ (1 : ℝ)
       then |X s ω - Function.leftLim (fun u => X u ω) s| else 0)
  have hF : AEMeasurable F P := by
    obtain ⟨G, hG, hrep⟩ := Kyprianou.Ch02.cadlagSmallJumpMassBorelFunctionalV1 T
    have hm := hG.comp_aemeasurable
      (Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX)
    refine hm.congr ?_
    filter_upwards [hX.cadlag_ae] with ω hω
    exact hrep (fun t => X t ω) (fun t => (hω t).1) (fun t _ => (hω t).2)
  have hp : MeasurePreserving (Prod.fst : Ω × Λ → Ω) (P.prod Q) P :=
    measurePreserving_fst
  have hc : ∀ᵐ p : Ω × Λ ∂(P.prod Q), IsCadlag (fun t => X t p.1) :=
    hp.quasiMeasurePreserving.ae hX.cadlag_ae
  calc
    _ = ∫⁻ p : Ω × Λ, F p.1 ∂(P.prod Q) := by
      apply lintegral_congr_ae
      filter_upwards [hc] with p hp
      dsimp [F]
      apply tsum_congr
      intro s
      rw [Kyprianou.Ch02.cadlagJumpOfAddContinuousV1
        (fun t => X t p.1) (fun t => Y t p.2) hp (hY p.2) s s.property.1]
    _ = ∫⁻ ω, F ω ∂P := by
      have hFm : AEMeasurable F ((P.prod Q).map Prod.fst) := by
        rw [hp.map_eq]
        exact hF
      rw [← lintegral_map' hFm hp.measurable.aemeasurable, hp.map_eq]
