-- Prove2me | solution 1 for GlobalTheory.NormalDescent.charK_monic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:14.790537+00:00
-- url     : https://prove2.me/submissions/0993001d-eb86-4ff5-a886-91db951357de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormalDescent
open Polynomial TensorProduct
variable {A B : Type} [CommRing A] [CommRing B]
namespace GlobalTheory.NormalDescent
theorem _root_.solution (φ : A →+* B) (hφ : φ.Finite) (K : Type) [Field K] [Algebra A K] (b : B) :
    (charK φ hφ K b).Monic := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  exact LinearMap.charpoly_monic _
end GlobalTheory.NormalDescent
