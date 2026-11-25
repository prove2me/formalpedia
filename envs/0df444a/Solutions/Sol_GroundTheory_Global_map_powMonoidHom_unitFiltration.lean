-- Prove2me | solution 1 for GroundTheory.Global.map_powMonoidHom_unitFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:15.796036+00:00
-- url     : https://prove2.me/submissions/5b94731a-1f9b-4864-b32a-f4fa2d4307e5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_filtrationSeparated_unitFiltration
import Theorems.Thm_GroundTheory_Global_filtrationComplete_unitFiltration
import Theorems.Thm_GroundTheory_Global_pow_mem_unitFiltration
import Theorems.Thm_GroundTheory_Global_exists_pow_div_mem_unitFiltration
import Theorems.Thm_GroundTheory_LocalField_map_eq_of_graded_surjective


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
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd
namespace GroundTheory.Global
theorem _root_.solution :
    (unitFiltration K (d + 1)).map (powMonoidHom n) = unitFiltration K (d + 1 + d) :=
  map_eq_of_graded_surjective (unitFiltration_antitone K) (unitFiltration_antitone K)
    filtrationComplete_unitFiltration filtrationSeparated_unitFiltration (powMonoidHom n)
    (φ := fun j ↦ j + d) (Filter.tendsto_add_atTop_nat d) (d + 1)
    (fun _ hj _ hg ↦ pow_mem_unitFiltration hϖ hnd hj hg)
    (fun _ hj _ hh ↦ exists_pow_div_mem_unitFiltration hϖ hnd hj hh)
end GroundTheory.Global
