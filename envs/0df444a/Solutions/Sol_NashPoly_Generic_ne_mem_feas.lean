-- Prove2me | solution 1 for NashPoly.Generic.ne_mem_feas
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:25:58.634767+00:00
-- url     : https://prove2.me/submissions/73410ff0-98c0-4153-83d8-8174abd21230

import Mathlib
import Definitions.Def_NashPoly_Generic_MultiplierExpr
import Theorems.Thm_NashPoly_Generic_ne_satisfies_3_6

open MvPolynomial Matrix NashPoly.Generic

theorem solution {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (hH : ∀ i, H i * Gmat (P.g i) = 1)
    (K : (i : Fin N) → Set (Fin (n i) → ℝ)) (hK : ∀ i, K i ⊆ P.X i) :
    P.NESet ⊆ P.Feas H K := by
  intro x hx
  exact ⟨ne_satisfies_3_6 P H hH hx, fun i v hv => hx.2 i v (hK i hv)⟩
