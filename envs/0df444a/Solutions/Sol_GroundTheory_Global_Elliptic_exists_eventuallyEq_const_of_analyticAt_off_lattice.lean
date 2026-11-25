-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_eventuallyEq_const_of_analyticAt_off_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:53.829856+00:00
-- url     : https://prove2.me/submissions/9b9772e8-f71a-45bb-872c-3503ccc3e00a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_meromorphicOrderAt_add
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {g : ℂ → ℂ} (hg : Meromorphic g)
    (hp : IsPeriodic L g) (han : ∀ z ∉ L.lattice, AnalyticAt ℂ g z)
    (h0 : 0 ≤ meromorphicOrderAt g 0) : ∃ c : ℂ, g =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  refine exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg L hg hp fun z ↦ ?_
  by_cases hz : z ∈ L.lattice
  · have := hp.meromorphicOrderAt_add hz 0
    rw [zero_add] at this
    rwa [this]
  · exact (han z hz).meromorphicOrderAt_nonneg
end GroundTheory.Global.Elliptic
