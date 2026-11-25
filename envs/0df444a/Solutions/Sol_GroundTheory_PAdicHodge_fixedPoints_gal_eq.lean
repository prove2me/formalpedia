-- Prove2me | solution 1 for GroundTheory.PAdicHodge.fixedPoints_gal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:14.61718+00:00
-- url     : https://prove2.me/submissions/7613f0a5-4c4b-4276-bb39-415713c3f119

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_fixedPoints_gal_eq_closure
import Theorems.Thm_GroundTheory_PAdicHodge_isClosed_image_coe_of_finiteDimensional

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
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution [FiniteDimensional ℚ_[p] K] :
    MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p] =
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p)) := by
  rw [fixedPoints_gal_eq_closure, isClosed_image_coe_of_finiteDimensional.closure_eq]
end GroundTheory.PAdicHodge
