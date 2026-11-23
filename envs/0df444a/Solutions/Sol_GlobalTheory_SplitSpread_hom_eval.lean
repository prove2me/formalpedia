-- Prove2me | solution 1 for GlobalTheory.SplitSpread.hom_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:17.1323+00:00
-- url     : https://prove2.me/submissions/c46945b3-0556-4960-a5ed-5765e43f07d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.SplitSpread
open MvPolynomial
namespace GlobalTheory.SplitSpread
theorem _root_.solution {R S τ : Type} [CommSemiring R] [CommSemiring S] (h : R →+* S) (x : τ → R)
    (W : MvPolynomial τ R) : h (eval x W) = MvPolynomial.eval (h ∘ x) (MvPolynomial.map h W) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id]
end GlobalTheory.SplitSpread
