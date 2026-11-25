-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:47:25.674123+00:00
-- url     : https://prove2.me/submissions/9a2523d9-8e3a-4c65-b19c-19505f23409e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueHomogeneousIdealFixedSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankFixedSubmoduleComplexification
import Theorems.Thm_GlobalTheory_GaloisDescent_complex_mem_range_of_forall_algEquiv
import Theorems.Thm_GlobalTheory_GaloisDescent_stable_iff_exists_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry
universe u
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [Algebra K ℂ]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {V : Type*} [AddCommGroup V]
    [Module K V] (W : Submodule ℂ (ℂ ⊗[K] V)) :
    (∀ σ : ℂ ≃ₐ[K] ℂ, ∀ w ∈ W, σ.toLinearMap.rTensor V w ∈ W) ↔
      ∃! N : Submodule K V, N.baseChange ℂ = W :=
  stable_iff_exists_baseChange (fun σ : ℂ ≃ₐ[K] ℂ => σ.toAlgHom)
    complex_mem_range_of_forall_algEquiv W
end GlobalTheory.GaloisDescent
