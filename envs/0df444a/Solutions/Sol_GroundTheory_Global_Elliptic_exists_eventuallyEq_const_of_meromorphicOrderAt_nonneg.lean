-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:39.331802+00:00
-- url     : https://prove2.me/submissions/ae4dd140-4821-45a7-aa6a-48e378a70b43

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_const_of_meromorphicOrderAt_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℂ E]
variable {L : PeriodPair}
variable (L)
namespace GroundTheory.Global.Elliptic
theorem _root_.solution [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  obtain ⟨c, hc⟩ := exists_const_of_meromorphicOrderAt_nonneg L hf hp ho
  refine ⟨c, ?_⟩
  filter_upwards [(hf.meromorphicOn (s := univ)).analyticAt_mem_codiscreteWithin] with z hz
  exact hc z hz
end GroundTheory.Global.Elliptic
