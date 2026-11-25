-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.of_flat_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:51.468048+00:00
-- url     : https://prove2.me/submissions/4b60dacf-53e9-4e5a-89b1-e2c22ad2fcbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_linearEquiv
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution {f : ι → R} (h : IsQuasiRegularSeq R f) (N : Type*)
    [AddCommGroup N] [Module R N] [Module.Flat R N] : IsQuasiRegularSeq N f :=
  (h.tensor N).of_linearEquiv (TensorProduct.rid R N)
end IsQuasiRegularSeq
end GlobalTheory
