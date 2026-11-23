-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationShiftedTailLIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:23:49.113954+00:00
-- url     : https://prove2.me/submissions/18638b89-a9c0-4bff-b8aa-e1e463baa664

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem realSetLIntegralTranslate
    (g : ℝ → ℝ≥0∞) (A U : ℝ) :
    (∫⁻ s in Set.Ioc A U, g (s - A) ∂volume) =
    (∫⁻ x in Set.Ioc (0 : ℝ) (U - A), g x ∂volume) := by
  classical
  have hPreimage :
      (fun x : ℝ => x + A) ⁻¹' Set.Ioc A U =
        Set.Ioc (0 : ℝ) (U - A) := by
    ext x
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor <;> dsimp at *
      · linarith
      · linarith
    · rintro ⟨hlo, hhi⟩
      constructor <;> dsimp at * <;> linarith
  have hMP : MeasurePreserving (fun x : ℝ => x + A) volume volume :=
    measurePreserving_add_right volume A
  have hEmb : MeasurableEmbedding (fun x : ℝ => x + A) :=
    measurableEmbedding_addRight A
  have heq :=
    hMP.setLIntegral_comp_preimage_emb hEmb
      (fun s : ℝ => g (s - A)) (Set.Ioc A U)
  rw [hPreimage] at heq
  simpa only [add_sub_cancel_right] using heq.symm

theorem solution
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω)
    (u : ℝ≥0) (hu : A ≤ (u : ℝ)) :
    (∫⁻ s in Set.Ioc A (u : ℝ),
      (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ∂volume) =
      reciprocalOccupation Y (Real.toNNReal ((u : ℝ) - A)) ω := by
  classical
  let g : ℝ → ℝ≥0∞ := fun s =>
    (ENNReal.ofReal (Y (Real.toNNReal s) ω : ℝ))⁻¹
  have hIntegrand :
      Set.EqOn
        (fun s : ℝ => (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹)
        (fun s : ℝ => g (s - A)) (Set.Ioc A (u : ℝ)) := by
    intro s hs
    have hA' : A ≤ s := le_of_lt hs.1
    have hs0 : 0 ≤ s := hA.trans hA'
    have hShiftAt :=
      hShift (Real.toNNReal s) (by rw [Real.coe_toNNReal s hs0]; exact hA')
    rw [Real.coe_toNNReal s hs0] at hShiftAt
    change (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ =
      (ENNReal.ofReal (Y (Real.toNNReal (s - A)) ω : ℝ))⁻¹
    rw [hShiftAt]
  have hVolumeShift := realSetLIntegralTranslate g A (u : ℝ)
  have hRes0 : 0 ≤ (u : ℝ) - A := sub_nonneg.mpr hu
  have hRes :
      (((Real.toNNReal ((u : ℝ) - A) : ℝ≥0) : ℝ)) = (u : ℝ) - A :=
    Real.coe_toNNReal ((u : ℝ) - A) hRes0
  calc
    (∫⁻ s in Set.Ioc A (u : ℝ),
      (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ∂volume) =
        (∫⁻ s in Set.Ioc A (u : ℝ), g (s - A) ∂volume) :=
      setLIntegral_congr_fun measurableSet_Ioc hIntegrand
    _ = (∫⁻ x in Set.Ioc (0 : ℝ) ((u : ℝ) - A), g x ∂volume) :=
      hVolumeShift
    _ = reciprocalOccupation Y (Real.toNNReal ((u : ℝ) - A)) ω := by
      simp only [reciprocalOccupation, hRes, g]
