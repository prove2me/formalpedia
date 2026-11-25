-- Prove2me | solution 1 for Neutral.B1.mem_rayUnits_of_isSupportedAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:51.604853+00:00
-- url     : https://prove2.me/submissions/3e00adbf-cc4a-4eb5-a129-61bde643fd51

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Theorems.Thm_Neutral_B1_valued_algebraMap_eq_one

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
    (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) (ha : IsSupportedAt K a v)
    (hv : ¬ m₀ ≤ v.asIdeal) (hu : Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1) :
    a ∈ rayUnits K m₀ mInf := by
  refine ⟨fun w _ => ?_, fun v' => ?_⟩
  · rw [ha.1 w]
    exact ⟨1, (mul_one 1).symm⟩
  by_cases h : v' = v
  · subst h
    refine ⟨hu, ?_⟩
    obtain ⟨y, hy, hyv⟩ := SetLike.not_le_iff_exists.mp hv
    refine ⟨y, hy, ?_⟩
    rw [valued_algebraMap_eq_one K v' y hyv]
    calc Valued.v ((a : AdeleRing (𝓞 K) K).2 v' - 1)
        ≤ max (Valued.v ((a : AdeleRing (𝓞 K) K).2 v')) (Valued.v (1 : v'.adicCompletion K)) :=
          Valuation.map_sub _ _ _
      _ = 1 := by rw [hu, map_one, max_self]
  · rw [ha.2 v' h]
    exact ⟨map_one _, 0, m₀.zero_mem, by simp⟩
end Neutral.B1
