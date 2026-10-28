-- Prove2me | solution 1 for LieTwoAlg.Equiv.equation_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:41:43.729656+00:00
-- url     : https://prove2.me/submissions/c1eba5b5-5228-4693-b9d2-f143ad2eb6ea

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

universe u

open LieTwoAlg.Equiv in
theorem solution {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    (V : LInfData k) (hV : IsLInf V)
    (x a : V.V0) (f g : V.V1) :
    -V.l2m a f + V.l2m (x + V.d f) g =
      V.l2m x g - V.l2m (a + V.d g) f := by
  simp only [map_add, LinearMap.add_apply]
  rw [hV.f f g]
  abel
