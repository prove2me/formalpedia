-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:41.349691+00:00
-- url     : https://prove2.me/submissions/f2e2c345-4c83-454e-84c3-e150de58f890

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_range_algebraMap_of_forall_algEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Cardinal
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial Cardinal
namespace GlobalTheory.GaloisDescent
namespace _root_.GlobalTheory.GaloisDescent
theorem _root_.solution {K : Type*} [Field K] [Algebra K ℂ] (x : ℂ)
    (hx : ∀ σ : ℂ ≃ₐ[K] ℂ, σ x = x) : x ∈ Set.range (algebraMap K ℂ) := by
  haveI : CharZero K := RingHom.charZero (algebraMap K ℂ)
  exact _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv x hx
end _root_.GlobalTheory.GaloisDescent
end GlobalTheory.GaloisDescent
