-- Prove2me | solution 1 for HatAffineConstantRows.eval_affineObstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:16:13.608622+00:00
-- url     : https://prove2.me/submissions/0a0b8953-f991-4ad9-a57a-1022fd107bfe

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_eval_affineObstructionFactor

set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [Field K] {m : Nat} {I : Type v} [Fintype I]
    (A : I → Fin m → K) (b x : I → K)
    (F : (Fin m → K) → I → K)
    (hrealize : AffineRealizes A b F)
    (y : Fin m → K) :
    MvPolynomial.eval y (affineObstruction A b x) =
      ∏ i, (F y i - x i) := by
  classical
  rw [affineObstruction, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact eval_affineObstructionFactor A b x F hrealize y i
end HatAffineConstantRows
