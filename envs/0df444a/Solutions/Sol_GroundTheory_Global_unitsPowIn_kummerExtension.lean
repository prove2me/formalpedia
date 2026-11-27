-- Prove2me | solution 1 for GroundTheory.Global.unitsPowIn_kummerExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:14.89162+00:00
-- url     : https://prove2.me/submissions/64f3038b-ef5e-46a2-bd89-39b49ba48365

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerCorrespondence
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Theorems.Thm_GroundTheory_ProfCoh_unitsPow_le_unitsPowIn


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
open GroundTheory.ProfCoh IntermediateField
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ)
variable [IsSepClosed Ω]
namespace GroundTheory.Global
theorem _root_.solution (hΔ : unitsPow K n ≤ Δ) :
    unitsPowIn K n (kummerExtension K n Ω Δ) = Δ := by
  have h1 : (QuotientGroup.mk' (unitsPow K n)).ker ≤ unitsPowIn K n (kummerExtension K n Ω Δ) := by
    rw [QuotientGroup.ker_mk']
    exact unitsPow_le_unitsPowIn K n _
  have h2 : (QuotientGroup.mk' (unitsPow K n)).ker ≤ Δ := by
    rw [QuotientGroup.ker_mk']
    exact hΔ
  calc unitsPowIn K n (kummerExtension K n Ω Δ)
      = (kummerGroup K n (kummerExtension K n Ω Δ)).comap (QuotientGroup.mk' (unitsPow K n)) :=
        (Subgroup.comap_map_eq_self h1).symm
    _ = (radicalClasses K n Δ).comap (QuotientGroup.mk' (unitsPow K n)) := by
        rw [kummerGroup_kummerExtension]
    _ = Δ := Subgroup.comap_map_eq_self h2
end GroundTheory.Global
