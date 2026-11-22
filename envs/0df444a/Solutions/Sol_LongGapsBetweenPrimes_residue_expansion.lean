-- Prove2me | solution 1 for LongGapsBetweenPrimes.residue_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:50.30833+00:00
-- url     : https://prove2.me/submissions/ac5b0c9e-a206-42c6-8736-6d1a10a985d4

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (n : ℕ) :
    g ⟨n % m, Nat.mod_lt n hm⟩ = ∑ a : Fin m, g a * residueIndicator m a.val n := by
  simpa [residueIndicator, Fin.ext_iff, mul_ite] using
    (Fintype.sum_ite_eq (⟨n % m, Nat.mod_lt n hm⟩ : Fin m) g).symm
end LongGapsBetweenPrimes
