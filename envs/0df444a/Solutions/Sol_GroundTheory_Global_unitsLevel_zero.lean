-- Prove2me | solution 1 for GroundTheory.Global.unitsLevel_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:33.367719+00:00
-- url     : https://prove2.me/submissions/6dbd0247-d1e7-4643-af55-19ff4afd4755

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Theorems.Thm_GroundTheory_Global_mem_unitsLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter IsDedekindDomain WithZero
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace GroundTheory.Global
theorem _root_.solution :
    unitsLevel (K := K) v 0 = (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  ext x
  rw [Submonoid.mem_units_iff, mem_unitsLevel]
  change _ ↔ (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, -⟩
    simp [h1]
  · rintro ⟨h1, h2⟩
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simp
    have h3 : 1 ≤ Valued.v (x : v.adicCompletion K) := by
      exact (inv_le_one₀ (zero_lt_iff.2 hx0)).1 h2
    refine ⟨le_antisymm h1 h3, ?_⟩
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact Valuation.map_sub_le _ h1 (by simp)
end GroundTheory.Global
