-- Prove2me | solution 1 for GroundTheory.Global.trace_invariantsEnd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:21.476226+00:00
-- url     : https://prove2.me/submissions/3d04e53f-3785-4d3b-9219-416113b635eb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Theorems.Thm_GroundTheory_Global_trace_restrict_invariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
namespace GroundTheory.Global
theorem _root_.solution (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I)
    (m : ℕ) :
    LinearMap.trace ℂ _ (invariantsEnd ρ I g hg ^ m) = cosetAverage I ρ.character (g ^ m) := by
  rw [invariantsEnd, Module.End.pow_restrict, trace_restrict_invariants, cosetAverage]
  congr 1
  refine finsum_congr fun i => ?_
  rw [Representation.character, map_mul ρ, map_pow ρ]
end GroundTheory.Global
