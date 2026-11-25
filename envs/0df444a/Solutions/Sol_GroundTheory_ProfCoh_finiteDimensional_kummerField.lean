-- Prove2me | solution 1 for GroundTheory.ProfCoh.finiteDimensional_kummerField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:29.870365+00:00
-- url     : https://prove2.me/submissions/425a079f-3d0f-43dc-9014-34940023ecb5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerCorrespondence
import Theorems.Thm_GroundTheory_ProfCoh_exists_finite_generators_kummerField

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
theorem _root_.solution [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n))
    [Finite Δ] : FiniteDimensional K (kummerField K n Ω Δ) := by
  obtain ⟨r, hr, heq⟩ := exists_finite_generators_kummerField K n Ω Δ
  rw [heq]
  exact finiteDimensional_adjoin fun α ⟨x, hx⟩ => by
    obtain ⟨a, -, ha⟩ := hr x
    exact isIntegral_of_pow_eq_algebraMap K n Ω (hx ▸ ha)
end GroundTheory.ProfCoh
