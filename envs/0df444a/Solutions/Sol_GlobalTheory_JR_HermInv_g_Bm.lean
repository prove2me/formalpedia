-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.g_Bm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:19:59.541804+00:00
-- url     : https://prove2.me/submissions/12ad0fec-ed91-490d-afe5-b6bb49e137f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_semiconj_of_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (g : Matrix.unitaryGroup (Fin r) E) (X₁ X₂ : Hn r F E) (hact : actU g X₁ = X₂) :
    g.1 * Bm X₁.toGl = Bm X₂.toGl := by
  have hs := semiconj_of_act g X₁ X₂ hact
  have e2 : g.1 *ᵥ X₁.2.1 = X₂.2.1 := congrArg (fun Y : Hn r F E => Y.2.1) hact
  have hp : ∀ k : ℕ, g.1 * X₁.1.1 ^ k = X₂.1.1 ^ k * g.1 := fun k => SemiconjBy.pow_right hs k
  ext i j
  have : (g.1 * Bm X₁.toGl) i j = (g.1 *ᵥ (X₁.1.1 ^ (j : ℕ) *ᵥ X₁.2.1)) i := by
    simp only [mul_apply, Bm, of_apply, mulVec, dotProduct]
    rfl
  rw [this, mulVec_mulVec, hp, ← mulVec_mulVec, e2]
  rfl
end GlobalTheory.JR.HermInv
