-- Prove2me | solution 1 for MarkovMixing.spectral_completeness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:25.121389+00:00
-- url     : https://prove2.me/submissions/987778df-df83-43dd-a4ed-fca89851a85a

import Mathlib
import Definitions.Def_mm_spectral

-- carved verbatim out of submission b36a2a77-0ed1-410e-b982-dafb4dc643a6, lines 592-597

section
open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

theorem solution
    (hspec : ∀ (t : ℕ) (x y : V), (P ^ t) x y / π y = ∑ j, ff j x * ff j y * lam j ^ t)
    (x y : V) : ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y := by
  have h := hspec 0 x y
  simpa [Matrix.one_apply] using h.symm

end
