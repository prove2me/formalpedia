-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.moeb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:08.055745+00:00
-- url     : https://prove2.me/submissions/3b1c8ec8-dc35-4e52-a2b1-292c14d395ad

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_kapQ_isUnit
import Theorems.Thm_GlobalTheory_HodgeDomain_hQ_moeb

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
theorem _root_.solution {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z ∈ hcDom p q := by
  have hu : IsUnit (kapQ g z) := (Matrix.isUnit_iff_isUnit_det _).mpr (kapQ_isUnit hg hz)
  have h2 : ((kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z).PosDef := by
    rw [hQ_moeb hg hz]; exact hz
  exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).mp h2
end GlobalTheory.HodgeDomain
