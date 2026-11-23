-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:36.483798+00:00
-- url     : https://prove2.me/submissions/7b928d63-c937-4886-8c78-80f340e5e04a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace Topology Filter Set
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))
variable (R : PadicAlgCl p → PadicAlgCl p)
variable {E R}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    extendToClosure E R x = extendOnClosure E R ⟨x, hx⟩ :=
  dif_pos hx
end GroundTheory.PAdicHodge
