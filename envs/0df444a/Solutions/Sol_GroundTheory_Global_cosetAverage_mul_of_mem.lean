-- Prove2me | solution 1 for GroundTheory.Global.cosetAverage_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:33.313378+00:00
-- url     : https://prove2.me/submissions/4b0c6b6c-f4b4-4bb2-a639-bf90fdfa4bfa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff

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
variable {G : Type*} [Group G]
namespace GroundTheory.Global
theorem _root_.solution (I : Subgroup G) (f : G → ℂ) (g : G) {j : G} (hj : j ∈ I) :
    cosetAverage I f (g * j) = cosetAverage I f g := by
  unfold cosetAverage
  congr 1
  have := finsum_comp_equiv (Equiv.mulLeft (⟨j, hj⟩ : I)) (f := fun i : I => f (g * (i : G)))
  simpa [mul_assoc] using this
end GroundTheory.Global
