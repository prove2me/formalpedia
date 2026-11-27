-- Prove2me | solution 1 for GroundTheory.PAdicHodge.galCp_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T03:23:13.09935+00:00
-- url     : https://prove2.me/submissions/a4744cf6-df9b-4cec-a9d7-5a499e201cfb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
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
open UniformSpace Topology Filter
noncomputable section
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
theorem solution (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    (galCp σ).symm x = σ⁻¹ • x := by
  rfl
