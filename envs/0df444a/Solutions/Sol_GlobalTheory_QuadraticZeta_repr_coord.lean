-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.repr_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:22.389501+00:00
-- url     : https://prove2.me/submissions/62dffa57-5492-4b1d-be91-9bc95e089851

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
theorem _root_.solution (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) (x y : ℤ) :
    b.repr (x + y * b 1) 0 = x ∧ b.repr (x + y * b 1) 1 = y := by
  have : (x + y * b 1 : R) = x • b 0 + y • b 1 := by simp [h0]
  rw [this]
  simp [-zsmul_eq_mul]
end GlobalTheory.QuadraticZeta
