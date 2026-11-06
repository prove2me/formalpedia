-- Prove2me | solution 1 for OAI.SharpPlanar.D_as_table_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:25:29.333029+00:00
-- url     : https://prove2.me/submissions/fb72e850-09d0-4cf7-acd1-baa98e44f3e3

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_trig_table_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma residue_lt {a : ℕ} (ha : a ∈ residues) : a < 12 := by
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma divided_cos_to_double (x : ℝ) :
    Real.cos x / Real.sin x = Real.sin (2*x) / (1 - Real.cos (2*x)) := by
  by_cases hs : Real.sin x = 0
  · simp [Real.sin_two_mul, hs]
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have he : 1 - (2 * Real.cos x ^ 2 - 1) = 2 * Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [he]
  field_simp


lemma D_as_table_e_oai (n : ℕ) : D n = (Real.pi/6) *
    ∑ a ∈ residues.erase (n%12),
      (sinTable (n%12)*cosTable a - cosTable (n%12)*sinTable a) /
        (1 - (cosTable (n%12)*cosTable a + sinTable (n%12)*sinTable a)) := by
  unfold D
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [divided_cos_to_double,
    show 2 * (Real.pi * (((n%12 : ℕ):ℝ)-a)/12) =
      Real.pi*(n%12 : ℕ)/6 - Real.pi*a/6 by ring, Real.sin_sub, Real.cos_sub]
  rw [(trig_table_e (n%12) (by omega)).1, (trig_table_e (n%12) (by omega)).2,
    (trig_table_e a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).1,
    (trig_table_e a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).2]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.D_as_table_e_oai := @OAI.SharpPlanar.D_as_table_e_oai
