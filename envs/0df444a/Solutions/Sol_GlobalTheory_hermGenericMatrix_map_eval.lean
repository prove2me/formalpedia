-- Prove2me | solution 1 for GlobalTheory.hermGenericMatrix_map_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:28.085925+00:00
-- url     : https://prove2.me/submissions/9e45bae6-3352-498c-857c-e274e3495bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Matrix
namespace GlobalTheory
theorem _root_.solution {κ : Type} [Field κ] (n : ℕ) (e : κ)
    (u : Fin n × Fin n → κ) :
    (hermGenericMatrix n e).map (MvPolynomial.eval u) =
      Matrix.of fun i j => u (i, j) + u (j, i) + e * (u (i, j) - u (j, i)) := by
  ext i j
  simp [hermGenericMatrix]
end GlobalTheory
