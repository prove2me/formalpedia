-- Prove2me | solution 1 for GroundTheory.Global.valued_trace_le_one_of_valuation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:14.164329+00:00
-- url     : https://prove2.me/submissions/633afa4c-c48f-44d2-a095-613cf00d0fae

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_forall_valued_trace_le_one_iff
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_field


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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
open SemiLocal
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
namespace GroundTheory.Global
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    (u : PlacesOver M v) {x : M} (hx : u.1.valuation M x ≤ 1) :
    Valued.v (Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
      (algebraMap M (u.1.adicCompletion M) x)) ≤ 1 := by
  refine (forall_valued_trace_le_one_iff v u.1 0).2 (Nat.zero_le _) _ ?_
  rw [valued_algebraMap_field, Nat.cast_zero, WithZero.exp_zero]
  exact hx
end GroundTheory.Global
