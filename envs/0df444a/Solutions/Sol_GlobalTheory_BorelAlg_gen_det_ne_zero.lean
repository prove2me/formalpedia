-- Prove2me | solution 1 for GlobalTheory.BorelAlg.gen_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:22.815377+00:00
-- url     : https://prove2.me/submissions/a163229d-fa3e-43c7-a0f4-27367a07bf1e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_GlobalTheory_BorelAlg_eval_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
namespace GlobalTheory.BorelAlg
theorem _root_.solution (τ : ι) : (gen m L τ).det ≠ 0 := by
  intro h
  have := eval_det m L (RingHom.id L) (fun _ => 1) τ
  rw [h] at this
  simp at this
end GlobalTheory.BorelAlg
