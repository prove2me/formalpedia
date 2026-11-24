-- Prove2me | solution 1 for GroundTheory.PAdicHodge.gal_smul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:36.394303+00:00
-- url     : https://prove2.me/submissions/8bce238a-301d-4099-b994-44f356b6183b

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] ℂ_[p] q = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
  change σ • ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p]) = _
  rw [gal_smul_coe]
  exact congrArg _ ((σ.restrictScalars ℚ_[p]).commutes q)
end GroundTheory.PAdicHodge
