-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_interior
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:49:56.108987+00:00
-- url     : https://prove2.me/submissions/71d08cb8-d794-432d-9c81-5a89986a36fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_of_dim
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nestOK_symm
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank

/-- Interior Dm idempotence: dim-directed nest Le + nestOK symmetry. -/
theorem solution :
    ∀ o c, o < SupG.codeBound → c < SupG.codeBound → nestOK o c = true →
      ¬ o ≤ 1 → ¬ c ≤ 1 → Dm o c * Dm o c = Dm o c := by
  intro o c ho hc hn _ _
  by_cases hdim : dimCF o ≤ dimCF c
  · exact Dm_idem_le ho hc (nest_Le_of_dim o c ho hc hn hdim) hdim
  · have hdim' : dimCF c ≤ dimCF o := Nat.le_of_not_ge hdim
    have hnest' : nestOK c o = true := by
      simpa [nestOK_symm o c] using hn
    exact Dm_idem_ge ho hc (nest_Le_of_dim c o hc ho hnest' hdim') hdim
