-- Prove2me | solution 1 for Ideal.map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/33a9f2f1-5cda-5179-87c8-c3e3a15ddf45

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul

set_option autoImplicit false

universe u v

theorem solution
    {P : Type u} [CommRing P] [IsNoetherianRing P] (J : Ideal P) (𝔫 : Ideal P) [𝔫.IsPrime]
    {ι : Type v} (h : ι → P) (hh : ∀ i, h i ∈ J)
    (hle : J ≤ Ideal.span (Set.range h) ⊔ 𝔫 * J) :
    Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J =
      Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (h i)) := by
  classical
  set S := Localization.AtPrime 𝔫 with hS
  set M : Ideal S := J.map (algebraMap P S) with hM
  set N : Ideal S := Ideal.span (Set.range fun i => algebraMap P S (h i)) with hN
  have hNeq : N = (Ideal.span (Set.range h)).map (algebraMap P S) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hNM : N ≤ M := by
    rw [hNeq]
    exact Ideal.map_mono (Ideal.span_le.2 (Set.range_subset_iff.2 hh))
  refine le_antisymm ?_ hNM

  have hMfg : M.FG := IsNoetherian.noetherian M
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hMfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_

  have h1 : M ≤ (Ideal.span (Set.range h) ⊔ 𝔫 * J).map (algebraMap P S) := Ideal.map_mono hle
  refine h1.trans ?_
  rw [Ideal.map_sup, Ideal.map_mul, ← hNeq]
  refine sup_le le_sup_left (le_sup_right.trans' ?_)
  rw [Ideal.smul_eq_mul]
  refine Ideal.mul_mono_left ?_
  exact (Localization.AtPrime.map_eq_maximalIdeal (I := 𝔫)).le

end S_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul
end P2MW
export P2MW.S_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul (solution)
