-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.uAmplitude_bound_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:12:32.093877+00:00
-- url     : https://prove2.me/submissions/4a61697b-bfcb-4d89-a901-464f31f32f57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G235
import Definitions.Def_OAIQ098G322
import Definitions.Def_OAIQ098G365
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_amplitude_endpoints_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma uAmplitude_bound_g_oai (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) : ‖uAmplitude n j.val t‖ ≤ densityCap j := by
  obtain ⟨h0,h1,_⟩ := amplitude_endpoints_g n hn j
  let θ : ℝ := 6*t-j.val
  have hθ0 : 0 ≤ θ := by dsimp [θ] <;> linarith [ht.1]
  have hθ1 : θ ≤ 1 := by dsimp [θ] <;> linarith [ht.2]
  have hid : uAmplitude n j.val t = ((1-θ:ℝ):ℂ)*uAmplitude n j.val ((j.val:ℝ)/6)+
      (θ:ℂ)*uAmplitude n j.val (((j.val:ℝ)+1)/6) := by
    unfold uAmplitude θ
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖((1-θ:ℝ):ℂ)*uAmplitude n j.val ((j.val:ℝ)/6)‖+
        ‖(θ:ℂ)*uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ := norm_add_le _ _
    _ = (1-θ)*‖uAmplitude n j.val ((j.val:ℝ)/6)‖+
        θ*‖uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hθ0,
        abs_of_nonneg (sub_nonneg.mpr hθ1)]
    _ ≤ (1-θ)*densityCap j+θ*densityCap j := by gcongr
    _ = densityCap j := by ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.uAmplitude_bound_g_oai := @OAI.SharpPlanar.IntegerBasis.uAmplitude_bound_g_oai
