-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.blkMet_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:22.43223+00:00
-- url     : https://prove2.me/submissions/d3607eff-1c0a-495e-bc6f-7b0dbdd20556

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder
open GlobalTheory GlobalTheory.HodgeDomain
variable {p q : ℕ}
namespace GlobalTheory.HodgeDomain
theorem _root_.solution {A : Matrix (Fin p) (Fin p) ℂ} {B : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef)
    (hB : B.PosDef) : (blkMet A B).PosDef := by
  unfold blkMet
  have hpsd : (fromBlocks A 0 0 B).PosSemidef := by
    let _ := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
    have h0 : (0 : Matrix (Fin q) (Fin p) ℂ) = (0 : Matrix (Fin p) (Fin q) ℂ)ᴴ := by simp
    rw [h0]
    exact (Matrix.PosDef.fromBlocks₁₁ _ _ hA).2 (by simpa using hB.posSemidef)
  refine hpsd.posDef_iff_isUnit.2 ?_
  rw [Matrix.isUnit_iff_isUnit_det, det_fromBlocks_zero₁₂]
  exact (isUnit_iff_ne_zero.mpr hA.det_pos.ne').mul (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
end GlobalTheory.HodgeDomain
