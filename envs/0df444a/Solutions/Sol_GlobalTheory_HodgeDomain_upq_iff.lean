-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.upq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:25.979959+00:00
-- url     : https://prove2.me/submissions/d3dfde0b-fef5-42e3-9cf4-120a61be33f9

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
theorem _root_.solution {g : GL (Fin p ⊕ Fin q) ℂ} : g ∈ Upq p q ↔
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Jpq p q * g = Jpq p q := by
  unfold Upq UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  have hc : cT (starRingEnd ℂ) (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by
    ext i j
    simp [cT, conjTranspose_apply]
  rw [hc]
end GlobalTheory.HodgeDomain
