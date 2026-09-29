-- Prove2me | solution 1 for MagicSquares.semi_magic_count_three
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-17T05:57:57.943212+00:00
-- url     : https://prove2.me/submissions/667e88e8-a40e-4094-94fa-257b3085d06d

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSemiMagic3
import Theorems.Thm_MagicSquares_sm3_bij
import Theorems.Thm_MagicSquares_sm3_params_card

set_option autoImplicit false

open MagicSquares

/-- Reduction of `MagicSquares.semi_magic_count_three`.

MacMahon's semi-magic count

$$H_{3}(t)\;=\;3\binom{t+3}{4}+\binom{t+2}{2}$$

splits into the two imported children:

* `sm3_bij` — the map sending a normalized coefficient vector
  $(u,v,w,x,y,z)$ to $uD+vE+wF+xA+yB+zC$ is a bijection from the parameter
  set onto the $3\times3$ semi-magic squares of line sum $t$, so
  `semiMagicCount 3 t = sm3Count t`;
* `sm3_params_card` — the parameter set, split according to the first zero
  among $(x,y,z)$, has $3\binom{t+3}{4}+\binom{t+2}{2}$ elements.

Composing the two identities gives the theorem. Unlike the magic count
$M_{3}(t)$, which vanishes unless $3\mid t$, this is an honest polynomial in
$t$ of degree $4=(3-1)^{2}$ — the order-three instance of the Ehrhart/Stanley
theorem that $H_{n}$ is a polynomial of degree $(n-1)^{2}$. -/
theorem solution (t : ℕ) :
    semiMagicCount 3 t = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by
  rw [sm3_bij t, sm3_params_card t]
