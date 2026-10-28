-- Prove2me | solution 1 for OAI.PiExponent.logarithmic_interpolation_one_transverse_threshold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:18:12.064812+00:00
-- url     : https://prove2.me/submissions/a011e3af-5879-451c-a36f-0b4ddf7e1676
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_separated_weight_log_interpolation_of_volume_bounds

open scoped BigOperators

theorem solution
    (K : ℕ) (hK : 0 < K)
    (w0 v0 alpha : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hvol1 : (K : ℚ) * alpha < 1)
    (hvol2 : (K : ℚ) * (w0 / v0) * alpha < 1) :
    ∃ B : ℕ,
      ∀ w : Fin 1 → ℕ, (∀ i, 0 < w i) → B ≤ w 0 →
        ∀ c : Fin K → Fin 1 → ℂ,
          (∀ i : Fin 1, Function.Injective (fun j : Fin K => c j i)) →
          OAI.PiExponent.eventualLogJetSurjective 1 K w0 v0 alpha w c := by
  have hvol1' : (K : ℚ) * alpha ^ 1 < 1 := by
    simpa only [pow_one] using hvol1
  have hvol2' : (K : ℚ) * (w0 / v0) * alpha ^ 1 < 1 := by
    simpa only [pow_one] using hvol2
  obtain ⟨S, hS⟩ :=
    OAI.PiExponent.separated_weight_log_interpolation_of_volume_bounds
      1 K (by decide : 0 < 1) hK w0 v0 alpha hw0 hv0 halpha halpha1 hvol1' hvol2'
  refine ⟨S [], ?_⟩
  intro w hw hB c hc
  have hsep : OAI.PiExponent.separatedWeights S w := by
    intro i
    have hiVal : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have hi : i = 0 := Fin.ext hiVal
    subst i
    change S [] ≤ w 0
    exact hB
  exact hS w hw hsep c hc