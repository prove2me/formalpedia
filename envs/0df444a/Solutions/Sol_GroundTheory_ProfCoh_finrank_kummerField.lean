-- Prove2me | solution 1 for GroundTheory.ProfCoh.finrank_kummerField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:09:53.006988+00:00
-- url     : https://prove2.me/submissions/7a9702fc-b1ef-4386-9b2e-ad55ab2c6612

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerCorrespondence
import Theorems.Thm_GroundTheory_ProfCoh_finiteDimensional_kummerField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial IntermediateField
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) [Finite Δ] :
    Module.finrank K (kummerField K n Ω Δ) = Nat.card Δ := by
  have := finiteDimensional_kummerField K n Ω Δ
  have := kummerField_isGalois K n Ω Δ
  have := kummerField_isMulCommutative K n Ω Δ
  rw [← card_kummerGroup K n _ (kummerField_exponent_dvd K n Ω Δ), kummerGroup_kummerField]
end GroundTheory.ProfCoh
