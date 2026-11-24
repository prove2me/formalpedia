-- Prove2me | solution 1 for GlobalTheory.SplitSpread.eval_eqs_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:02.237584+00:00
-- url     : https://prove2.me/submissions/2bab003a-2291-4737-b12a-e140636836c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
import Theorems.Thm_GlobalTheory_SplitSpread_hom_eval

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
variable {σ : Type} [Finite σ] {A : Type} [CommRing A] {D : ℕ}
namespace GlobalTheory.SplitSpread
theorem _root_.solution {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (b : Bool) :
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inr b))) =
      z (Sum.inr (Sum.inr b)) *
        MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map ψ g) - 1 := by
  simp only [eqs, eval₂_sub, eval₂_mul, eval₂_X, eval₂_one]
  rw [← coe_eval₂Hom, hom_eval, MvPolynomial.map_map, eval₂Hom_comp_C]
  congr 4
  funext i
  simp
end GlobalTheory.SplitSpread
