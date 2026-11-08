-- Prove2me | solution 1 for OAI.SharpPlanar.Q_as_table_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:25:04.978124+00:00
-- url     : https://prove2.me/submissions/d00104d2-c2d0-4dff-987d-db3a909e159b

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_trig_table_g

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

lemma squared_sine_to_cos (x : ℝ) : (2 * Real.sin x)^2 = 2 - 2*Real.cos (2*x) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma Q_as_table_g_oai (n : ℕ) : Q n =
    (Real.pi/6)^2 * ∏ a ∈ residues.erase (n % 12),
      (2 - 2*(cosTable (n%12)*cosTable a + sinTable (n%12)*sinTable a)) := by
  unfold Q
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [squared_sine_to_cos,
    show 2 * (Real.pi * (((n%12 : ℕ):ℝ)-a)/12) =
      Real.pi*(n%12 : ℕ)/6 - Real.pi*a/6 by ring, Real.cos_sub]
  rw [(trig_table_g (n%12) (by omega)).1, (trig_table_g (n%12) (by omega)).2,
    (trig_table_g a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).1,
    (trig_table_g a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).2]


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_as_table_g_oai := @OAI.SharpPlanar.Q_as_table_g_oai
