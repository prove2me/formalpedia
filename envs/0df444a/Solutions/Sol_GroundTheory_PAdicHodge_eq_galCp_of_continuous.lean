-- Prove2me | solution 1 for GroundTheory.PAdicHodge.eq_galCp_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:57.760331+00:00
-- url     : https://prove2.me/submissions/09cf8bee-8302-45ca-a2cb-61ffda989c29

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Theorems.Thm_GroundTheory_PAdicHodge_galCp_coe
import Theorems.Thm_GroundTheory_PAdicHodge_continuous_galCp

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
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (f : ℂ_[p] → ℂ_[p])
    (hf : Continuous f) (h : ∀ y : PadicAlgCl p, f y = ((σ y : PadicAlgCl p) : ℂ_[p])) :
    f = galCp σ :=
  Completion.ext hf (continuous_galCp σ) fun y => by rw [h, galCp_coe]
end GroundTheory.PAdicHodge
