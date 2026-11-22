-- Prove2me | solution 1 for MarkushevichBasis.fourier_continuousMap_isMarkushevichBasis
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:55:21.360714+00:00
-- url     : https://prove2.me/submissions/4a9ec038-cb09-4393-8fc5-94b639ac9245

import Mathlib
import Definitions.Def_MarkushevichBasis_Basic

open MeasureTheory AddCircle MarkushevichBasis

set_option autoImplicit false

theorem solution (T : ℝ) [Fact (0 < T)] :
    ∃ c : ℤ → StrongDual ℂ C(AddCircle T, ℂ),
      (∀ (n : ℤ) (g : C(AddCircle T, ℂ)), c n g = fourierCoeff (⇑g) n) ∧
      IsMarkushevichBasis (fun n : ℤ => fourier (T := T) n) c := by
  have hInt (g : C(AddCircle T, ℂ)) : Integrable g haarAddCircle :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  let l (n : ℤ) : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => fourierCoeff (⇑g) n
      map_add' := fun g h => congrFun (fourierCoeff.add (hInt g) (hInt h)) n
      map_smul' := fun a g => fourierCoeff.const_smul (⇑g) a n }
  let c (n : ℤ) : StrongDual ℂ C(AddCircle T, ℂ) := (l n).mkContinuous 1 fun g => by
    have hb (x : AddCircle T) : ‖fourier (-n) x • g x‖ ≤ ‖g‖ := by
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      exact g.norm_coe_le_norm x
    simpa only [one_mul] using (calc
      ‖l n g‖ ≤ ∫ x : AddCircle T, ‖fourier (-n) x • g x‖ ∂haarAddCircle :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _ : AddCircle T, ‖g‖ ∂haarAddCircle :=
        integral_mono ((hInt g).fourier_smul (-n)).norm (integrable_const _) hb
      _ = ‖g‖ := by simp)
  refine ⟨c, fun _ _ => rfl, ?_⟩
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_, ?_⟩
  · change fourierCoeff (fourier (T := T) i : AddCircle T → ℂ) i = 1
    simp [fourierCoeff_fourier]
  · change fourierCoeff (fourier (T := T) j : AddCircle T → ℂ) i = 0
    simp [fourierCoeff_fourier, hij]
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  · intro g hg
    have hZero (i : ℤ) : fourierCoeff (⇑g) i = 0 := hg i
    have hSummable : Summable (fourierCoeff (⇑g)) := by
      rw [show fourierCoeff (⇑g) = 0 from funext hZero]
      exact summable_zero
    have hSeries := hasSum_fourier_series_of_summable hSummable
    have hSeriesZero : HasSum (fun _ : ℤ => (0 : C(AddCircle T, ℂ))) g := by
      simpa only [hZero, zero_smul] using hSeries
    exact hSeriesZero.unique hasSum_zero
