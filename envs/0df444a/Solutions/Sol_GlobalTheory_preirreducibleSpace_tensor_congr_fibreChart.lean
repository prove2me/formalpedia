-- Prove2me | solution 1 for GlobalTheory.preirreducibleSpace_tensor_congr_fibreChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:24.397823+00:00
-- url     : https://prove2.me/submissions/6cd597ba-b109-43f5-a3a9-1ae23a4f2b13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfacePartGeometricIrreducibleSpreadsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurfaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleFibreStandardEtaleSpreads
import Theorems.Thm_GlobalTheory_preirreducibleSpace_of_continuous_surjective_fibreChart

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (A B C k : Type) [CommRing A] [CommRing B]
    [CommRing C] [CommRing k] [Algebra A B] [Algebra A C] [Algebra A k] (e : B ≃ₐ[A] C) :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) ↔ PreirreducibleSpace (PrimeSpectrum (k ⊗[A] C)) := by
  let E : k ⊗[A] B ≃ₐ[A] k ⊗[A] C := Algebra.TensorProduct.congr AlgEquiv.refl e
  let H := PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv
  constructor
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H H.continuous H.surjective
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H.symm H.symm.continuous
      H.symm.surjective
end GlobalTheory
