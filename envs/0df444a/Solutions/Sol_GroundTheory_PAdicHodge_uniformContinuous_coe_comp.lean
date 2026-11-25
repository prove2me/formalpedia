-- Prove2me | solution 1 for GroundTheory.PAdicHodge.uniformContinuous_coe_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:27.239011+00:00
-- url     : https://prove2.me/submissions/3066909f-7ebd-4279-90ee-4f867e0b1076

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_lipschitzWith_coe_comp

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
theorem _root_.solution :
    UniformContinuous fun y : E => ((R y : PadicAlgCl p) : ℂ_[p]) :=
  (lipschitzWith_coe_comp hadd hbound).uniformContinuous
end GroundTheory.PAdicHodge
