-- Prove2me | solution 1 for GroundTheory.Global.trace_mem_range_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:45.769443+00:00
-- url     : https://prove2.me/submissions/ae934f54-c7cc-4f7d-9179-983ee54cbef4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_SemiLocal_algebraMap_trace_eq_sum
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
theorem _root_.solution (x : M)
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : PlacesOver M v),
      Valued.v (Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
        (algebraMap M (u.1.adicCompletion M) x)) ≤ 1) :
    Algebra.trace K M x ∈ (algebraMap (𝓞 K) K).range := by
  refine mem_integers_of_valuation_le_one (R := 𝓞 K) (K := K) _ fun v ↦ ?_
  rw [← valued_algebraMap_field, algebraMap_trace_eq_sum]
  exact Valuation.map_sum_le _ fun u _ ↦ h v u
end GroundTheory.Global
