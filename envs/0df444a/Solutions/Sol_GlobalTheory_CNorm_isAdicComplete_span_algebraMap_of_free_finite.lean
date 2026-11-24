-- Prove2me | solution 1 for GlobalTheory.CNorm.isAdicComplete_span_algebraMap_of_free_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:39:20.86087+00:00
-- url     : https://prove2.me/submissions/ea507264-3df0-45cc-9ef1-c91a7a17f64b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
import Theorems.Thm_GlobalTheory_CNorm_isAdicComplete_of_free_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution :
    ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
      (t : R), IsAdicComplete (Ideal.span {t}) R →
        IsAdicComplete (Ideal.span {algebraMap R O t}) O := by
  intro R O _ _ _ _ _ t h
  have h1 : IsAdicComplete (Ideal.span {t}) O := isAdicComplete_of_free_finite _ h
  have h2 : Ideal.span {algebraMap R O t} = (Ideal.span {t}).map (algebraMap R O) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h2]
  exact (IsAdicComplete.map_algebraMap_iff _ O).2 h1
end GlobalTheory.CNorm
