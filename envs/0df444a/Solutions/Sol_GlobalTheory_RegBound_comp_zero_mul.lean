-- Prove2me | solution 1 for GlobalTheory.RegBound.comp_zero_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:22.490012+00:00
-- url     : https://prove2.me/submissions/d3b8fc8c-d7a7-4024-9958-539a2d1b4487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution {h : MvPolynomial σ K} (hh : h.IsHomogeneous 1)
    (B : MvPolynomial σ K) : homogeneousComponent 0 (h * B) = 0 := by
  induction B using MvPolynomial.induction_on' with
  | monomial d c =>
    have h1 := isHomogeneous_monomial (d := d) c rfl
    rw [homogeneousComponent_of_mem (hh.mul h1), if_neg (by omega)]
  | add p q hp hq => rw [mul_add, map_add, hp, hq, add_zero]
end GlobalTheory.RegBound
