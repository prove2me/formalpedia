-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.mvPolynomial_isHomogeneous_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:15.670162+00:00
-- url     : https://prove2.me/submissions/fd32ee73-5359-4912-9046-34fc983b7591

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Theorems.Thm_GlobalTheory_GaloisDescent_isHomogeneous_comap
import Theorems.Thm_GlobalTheory_GaloisDescent_isWeightedHomogeneous_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial
variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {I : Ideal (MvPolynomial σ L)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) :
    (I.comap (map (algebraMap K L) : MvPolynomial σ K →+* _)).IsHomogeneous
      (homogeneousSubmodule σ K) :=
  isHomogeneous_comap (j := mapAlgHom (σ := σ) (Algebra.ofId K L)) _ _
    (fun i a ha => isWeightedHomogeneous_map 1 i _ ha) hI
end GlobalTheory.GaloisDescent
