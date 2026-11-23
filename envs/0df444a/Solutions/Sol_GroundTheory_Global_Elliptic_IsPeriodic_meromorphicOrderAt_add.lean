-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.IsPeriodic.meromorphicOrderAt_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:14.231181+00:00
-- url     : https://prove2.me/submissions/86a9d985-08a9-41bc-9a8b-aaea5e94d236

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_comp_add

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
variable {L}
namespace GroundTheory.Global.Elliptic
namespace IsPeriodic
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    meromorphicOrderAt f (z + l) = meromorphicOrderAt f z := by
  have := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := f) (x := z) (c := l)
  rw [hf.comp_add hl] at this
  exact this.symm
end IsPeriodic
end GroundTheory.Global.Elliptic
