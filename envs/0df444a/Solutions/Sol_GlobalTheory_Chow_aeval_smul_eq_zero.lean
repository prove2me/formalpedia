-- Prove2me | solution 1 for GlobalTheory.Chow.aeval_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:36.573643+00:00
-- url     : https://prove2.me/submissions/6f19a084-0654-42dd-b870-db7c41335cb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Theorems.Thm_GlobalTheory_Chow_aeval_smul_of_isHomogeneous
import Theorems.Thm_GlobalTheory_Chow_aeval_eq_zero_of_homogeneousComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [CommRing K] {σ β : Type*}
namespace GlobalTheory.Chow
theorem _root_.solution {G : Type*} [CommRing G] [Algebra K G]
    {p : Ideal (MvPolynomial σ K)} (hp : p.IsHomogeneous (homogeneousSubmodule σ K))
    {ξ : σ → G} (hξ : ∀ g ∈ p, aeval ξ g = 0) (c : G) :
    ∀ g ∈ p, aeval (fun j => c * ξ j) g = 0 := fun g hg =>
  aeval_eq_zero_of_homogeneousComponent fun n => by
    rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous n g),
      hξ _ (homogeneousComponent_mem_of_mem hp hg n), mul_zero]
end GlobalTheory.Chow
