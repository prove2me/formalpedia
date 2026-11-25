-- Prove2me | solution 1 for GlobalTheory.T.exists_adic_coordinates_of_basis_mod_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:17:58.402466+00:00
-- url     : https://prove2.me/submissions/f0a4807d-6dc8-480a-8f1e-cef267fa8b7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAdicCoordinatesOfBasisModP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAdicCoordinatesOfBasisModPStatement
import Theorems.Thm_GlobalTheory_AdicCoord_exists_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  first | exact @GlobalTheory.AdicCoord.exists_coord | exact GlobalTheory.AdicCoord.exists_coord | (intros; apply GlobalTheory.AdicCoord.exists_coord <;> assumption)
end _root_.GlobalTheory.T
