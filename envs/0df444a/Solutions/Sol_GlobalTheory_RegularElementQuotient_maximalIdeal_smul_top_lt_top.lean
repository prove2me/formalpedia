-- Prove2me | solution 1 for GlobalTheory.RegularElementQuotient.maximalIdeal_smul_top_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:55:19.545994+00:00
-- url     : https://prove2.me/submissions/bbc499b9-2c9b-445a-aef5-e711a3303841

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open CategoryTheory Abelian Limits RingTheory.Sequence Pointwise
open GlobalTheory GlobalTheory.RegularElementQuotient
namespace GlobalTheory.RegularElementQuotient
theorem _root_.solution {R : Type u_1} [CommRing R] [IsLocalRing R]
    (M : Type u_2) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h

  have hbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
      Module.Finite.fg_top h.ge (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  exact top_ne_bot hbot
end GlobalTheory.RegularElementQuotient
