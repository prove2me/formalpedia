-- Prove2me | solution 1 for GroundTheory.PAdicHodge.gal_smul_coe_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:18.181563+00:00
-- url     : https://prove2.me/submissions/36c2ec9a-3a35-40be-8f44-989730707ce3

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
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p]) := by
  rw [gal_smul_coe]
  exact congrArg _ (σ.commutes k)
end GroundTheory.PAdicHodge
