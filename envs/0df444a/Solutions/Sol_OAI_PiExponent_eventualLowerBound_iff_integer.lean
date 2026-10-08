-- Prove2me | solution 1 for OAI.PiExponent.eventualLowerBound_iff_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:02:32.997558+00:00
-- url     : https://prove2.me/submissions/ddbc244c-fb4b-4fc2-acb6-74576e8fec02

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions


namespace OAI

namespace PiExponent

 













end PiExponent

end OAI

open OAI.PiExponent in
theorem solution (x : ℝ) :
    EventualLowerBound x ↔ IntegerEventualLowerBound x := by
  unfold EventualLowerBound IntegerEventualLowerBound
  constructor
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    refine ⟨Q, by exact_mod_cast hQ, ?_⟩
    intro p q hq
    have hq0 : 0 ≤ q := le_trans (by omega) hq
    have hnat : Q ≤ q.toNat := by omega
    have heq : (q.toNat : ℝ) = (q : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hq0)
    simpa only [heq] using hb p q.toNat hnat
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    have hQ0 : 0 ≤ Q := by omega
    refine ⟨Q.toNat, by omega, ?_⟩
    intro p q hq
    have hqi : Q ≤ (q : ℤ) := by omega
    simpa using hb p q hqi
