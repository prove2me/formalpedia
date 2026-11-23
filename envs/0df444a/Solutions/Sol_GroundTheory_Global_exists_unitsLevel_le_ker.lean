-- Prove2me | solution 1 for GroundTheory.Global.exists_unitsLevel_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:57.55419+00:00
-- url     : https://prove2.me/submissions/7773f218-6849-408e-ac8a-900a6e8d6fa0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Theorems.Thm_GroundTheory_Global_exists_le_ker_of_noSmallSubgroups
import Theorems.Thm_GroundTheory_Global_exists_unitsLevel_subset

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
variable {H : Type*} [Group H] [TopologicalSpace H]
namespace GroundTheory.Global
theorem _root_.solution (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) : ∃ n : ℕ, 1 ≤ n ∧ unitsLevel v n ≤ χ.ker := by
  obtain ⟨L, ⟨n, hn, rfl⟩, hL⟩ := exists_le_ker_of_noSmallSubgroups
    (P := fun L ↦ ∃ n : ℕ, 1 ≤ n ∧ L = unitsLevel v n)
    (fun W hW ↦ by
      obtain ⟨n, hn, h⟩ := exists_unitsLevel_subset v hW
      exact ⟨_, ⟨n, hn, rfl⟩, h⟩) hH χ hχ
  exact ⟨n, hn, hL⟩
end GroundTheory.Global
