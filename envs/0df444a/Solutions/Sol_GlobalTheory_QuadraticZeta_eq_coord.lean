-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.eq_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:37.023346+00:00
-- url     : https://prove2.me/submissions/ab202247-0ac9-4627-a230-29af910664be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {R : Type*} [CommRing R]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) (x : R) :
    x = (b.repr x 0 : R) + (b.repr x 1 : R) * b 1 := by
  conv_lhs => rw [← b.sum_repr x]
  simp [h0]
end GlobalTheory.QuadraticZeta
