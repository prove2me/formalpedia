-- Prove2me | solution 1 for Neutral.B1.localIdele_neg_one_mem_rayUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:38.921816+00:00
-- url     : https://prove2.me/submissions/42cbcb92-b451-4ef5-abf0-b7ceea3e4eea

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Theorems.Thm_Neutral_B1_localIdele_snd_self
import Theorems.Thm_Neutral_B1_localIdele_isSupportedAt
import Theorems.Thm_Neutral_B1_mem_rayUnits_of_isSupportedAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (K : Type*) [Field K] [NumberField K]
namespace Neutral.B1
theorem _root_.solution (m₀ : Ideal (𝓞 K)) (mInf : Set (InfinitePlace K))
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ m₀ ≤ v.asIdeal) :
    localIdele K v (-1) ∈ rayUnits K m₀ mInf ∧ localIdele K v (-1) ≠ 1 := by
  refine ⟨mem_rayUnits_of_isSupportedAt K m₀ mInf _ v (localIdele_isSupportedAt K v _) hv ?_, ?_⟩
  · rw [localIdele_snd_self]
    simp
  · intro h
    have h1 := congrArg (fun a : Ideles K => (a : AdeleRing (𝓞 K) K).2 v) h
    simp only [localIdele_snd_self] at h1
    have h2 : (-1 : v.adicCompletion K) = 1 := h1.trans rfl
    have h3 : algebraMap K (v.adicCompletion K) 2 = algebraMap K (v.adicCompletion K) 0 := by
      rw [map_ofNat, map_zero]
      linear_combination -h2
    exact two_ne_zero ((algebraMap K (v.adicCompletion K)).injective h3)
end Neutral.B1
