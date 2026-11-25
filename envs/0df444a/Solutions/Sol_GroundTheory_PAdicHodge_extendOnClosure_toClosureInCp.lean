-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendOnClosure_toClosureInCp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:05.406013+00:00
-- url     : https://prove2.me/submissions/154bc5b5-9294-4248-b87f-c68c0daca959

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_uniformContinuous_coe_comp

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
variable {c : ℝ} (hadd : ∀ y ∈ E, ∀ z ∈ E, R (y + z) = R y + R z)
  (hbound : ∀ y ∈ E, ‖R y‖ ≤ c * ‖y‖)
include hadd
include hbound
namespace GroundTheory.PAdicHodge
theorem _root_.solution (y : E) :
    extendOnClosure E R (toClosureInCp E y) = ((R y : PadicAlgCl p) : ℂ_[p]) :=
  uniformly_extend_of_ind (isometry_toClosureInCp E).isUniformInducing
    (denseRange_toClosureInCp E) (uniformContinuous_coe_comp hadd hbound) y
end GroundTheory.PAdicHodge
