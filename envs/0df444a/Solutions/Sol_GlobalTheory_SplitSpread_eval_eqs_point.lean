-- Prove2me | solution 1 for GlobalTheory.SplitSpread.eval_eqs_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:03.019838+00:00
-- url     : https://prove2.me/submissions/1cad217d-20c3-4657-9915-5e40a1d80c88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
import Theorems.Thm_GlobalTheory_SplitSpread_hom_eval
import Theorems.Thm_GlobalTheory_SplitSpread_map_gen

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
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inl b))) =
      MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (spec z b) := by
  rw [← coe_eval₂Hom]
  simp only [eqs]
  rw [hom_eval, map_gen]
  congr 2
  funext i
  simp
end GlobalTheory.SplitSpread
