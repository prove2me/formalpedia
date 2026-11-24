-- Prove2me | solution 1 for GlobalTheory.SplitSpread.eval_eqs_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:01.539977+00:00
-- url     : https://prove2.me/submissions/3fa351b0-324b-4f71-a5de-c28317cdee85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
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
    (f g : MvPolynomial σ A) (n : σ →₀ ℕ) :
    eval₂ ψ z (eqs A D f g (Sum.inl n)) = coeff n (spec z true * spec z false - MvPolynomial.map ψ f) := by
  rw [← coe_eval₂Hom]
  simp only [eqs]
  rw [← MvPolynomial.coeff_map, map_sub, map_mul, map_gen, map_gen, MvPolynomial.map_map,
    eval₂Hom_comp_C]
  rfl
end GlobalTheory.SplitSpread
