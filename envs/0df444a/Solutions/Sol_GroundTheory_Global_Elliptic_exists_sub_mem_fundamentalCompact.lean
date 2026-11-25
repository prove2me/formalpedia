-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_sub_mem_fundamentalCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:37.868163+00:00
-- url     : https://prove2.me/submissions/9254e6f9-0149-4e18-91d5-3249c4f9ae95

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions

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
variable (L : PeriodPair)
variable {L}
variable (L)
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (z : ℂ) :
    ∃ l ∈ L.lattice, z - l ∈ fundamentalCompact L := by
  refine ⟨ZSpan.floor L.basis z, ?_, subset_closure ?_⟩
  · rw [L.lattice_eq_span_range_basis]
    exact (ZSpan.floor L.basis z).2
  · rw [← ZSpan.fract_apply]
    exact ZSpan.fract_mem_fundamentalDomain _ _
end GroundTheory.Global.Elliptic
