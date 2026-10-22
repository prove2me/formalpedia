-- Prove2me | solution 1 for Milne.motives_not_tannakian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:13:41.458995+00:00
-- url     : https://prove2.me/submissions/45d6dd97-427f-43d2-8ae8-46decf4e9a82

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta
import Theorems.Thm_Milne_curve_trace_euler
universe u v

open Milne

theorem solution (W : CorrWorld.{u, v}) (g : ℕ) (hg : 2 ≤ g) :
    ¬ ∃ F : FibFun W, True := by
  rintro ⟨F, -⟩
  -- the fiber dimension of the motive of the genus-g curve is its trace, 2 - 2g < 0
  have h := F.trDim (hOf W (W.curve g))
  have htr : W.trId (W.curve g) (W.delta (W.curve g)) = (2 : ℚ) - 2 * (g : ℚ) :=
    curve_trace_euler W g
  change W.trId (W.curve g) (W.delta (W.curve g)) = _ at h
  rw [htr] at h
  have hg' : (2 : ℚ) ≤ g := by exact_mod_cast hg
  have hnn : (0 : ℚ) ≤ (F.dimv (hOf W (W.curve g)) : ℚ) := Nat.cast_nonneg _
  linarith
