-- Prove2me | solution 1 for GlobalTheory.TraceDetSplit.charpoly_leftMul_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:01.094903+00:00
-- url     : https://prove2.me/submissions/aec2ff46-ebad-44d1-b736-a7114859df79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceDetSplit
namespace GlobalTheory.TraceDetSplit
theorem _root_.solution {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] {n : ℕ} (g : A) (w : Module.Basis (Fin n) E A) :
    (Algebra.leftMulMatrix w g).charpoly = (LinearMap.mulLeft E g).charpoly := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rfl
end GlobalTheory.TraceDetSplit
