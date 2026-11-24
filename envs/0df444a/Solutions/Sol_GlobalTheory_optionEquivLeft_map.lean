-- Prove2me | solution 1 for GlobalTheory.optionEquivLeft_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:16.229833+00:00
-- url     : https://prove2.me/submissions/f2a4cb8f-c79d-4bbb-9fc8-35b235c1976a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurface

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
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A] (n : ℕ) {k : Type} [Field k]
    (ψ : A →+* k) (p : MvPolynomial (Option (Fin n)) A) :
    optionEquivLeft k (Fin n) (map ψ p) = Polynomial.map (map ψ) (optionEquivLeft A (Fin n) p) := by
  change (optionEquivLeft k (Fin n)).toAlgHom.toRingHom.comp (map ψ) p =
    (Polynomial.mapRingHom (map ψ)).comp (optionEquivLeft A (Fin n)).toAlgHom.toRingHom p
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [optionEquivLeft_C]
  · rcases i with _ | j <;> simp [optionEquivLeft_X_none, optionEquivLeft_X_some]
end GlobalTheory
