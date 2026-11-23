-- Prove2me | solution 1 for GlobalTheory.HodgeDomain.hQ_moeb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:39.415799+00:00
-- url     : https://prove2.me/submissions/366ac60a-6c0a-4982-af03-f69fa1a80417

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
import Theorems.Thm_GlobalTheory_HodgeDomain_kapQ_gram
import Theorems.Thm_GlobalTheory_HodgeDomain_moeb_mul_kapQ

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
    (hz : z ∈ hcDom p q) :
    (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z = hQ z := by
  have e := moeb_mul_kapQ hg hz
  have h1 := kapQ_gram hg z
  calc (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z =
      (kapQ g z)ᴴ * kapQ g z - (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z)ᴴ * (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z) := by
        unfold hQ
        rw [conjTranspose_mul]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = hQ z := by rw [e]; exact h1
end GlobalTheory.HodgeDomain
