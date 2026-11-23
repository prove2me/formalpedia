-- Prove2me | solution 1 for GlobalTheory.SplitSpread.map_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:17.330878+00:00
-- url     : https://prove2.me/submissions/eeba3b3d-d6eb-47ea-9295-f6a4c43c9e72

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
variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)
variable {A D}
namespace GlobalTheory.SplitSpread
theorem _root_.solution {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k) (b : Bool) :
    MvPolynomial.map (eval₂Hom ψ z) (gen A D b) = ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m))) := by
  simp [gen, map_sum, map_monomial]
end GlobalTheory.SplitSpread
