-- Prove2me | solution 1 for GroundTheory.Global.relDiscr_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:47:12.948894+00:00
-- url     : https://prove2.me/submissions/58937756-f877-4e19-a56a-587639552bae

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain NumberField Module
open GroundTheory GroundTheory.Global
variable (K M N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [Field N] [NumberField N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
namespace GroundTheory.Global
theorem _root_.solution :
    relDiscr K N = relDiscr K M ^ finrank M N * Ideal.relNorm (𝓞 K) (relDiscr M N) := by
  rw [relDiscr, differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 M) (𝓞 N), map_mul,
    mul_comm, relDiscr, relDiscr, Ideal.relNorm_relNorm (𝓞 K) (𝓞 M),
    ← Ideal.relNorm_relNorm (𝓞 K) (𝓞 M) (Ideal.map _ _), Ideal.relNorm_algebraMap, map_pow,
    IsFractionRing.finrank_eq (𝓞 M) M (𝓞 N) N]
end GroundTheory.Global
