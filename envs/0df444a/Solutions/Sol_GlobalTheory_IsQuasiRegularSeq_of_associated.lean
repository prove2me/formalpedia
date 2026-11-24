-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.of_associated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:32.871405+00:00
-- url     : https://prove2.me/submissions/63f7a414-383d-461b-9313-78c7c0457fa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_unit_mul

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
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {M}
open GlobalTheory.IsQuasiRegularSeq
namespace GlobalTheory.IsQuasiRegularSeq
theorem _root_.solution {f g : ι → R} (h : IsQuasiRegularSeq M f) (hfg : ∀ i, Associated (f i) (g i)) :
    IsQuasiRegularSeq M g := by
  choose u hu using hfg
  obtain rfl : g = fun i => (u i : R) * f i := funext fun i => by rw [← hu i, mul_comm]
  exact h.unit_mul fun i => (u i).isUnit
end GlobalTheory.IsQuasiRegularSeq
