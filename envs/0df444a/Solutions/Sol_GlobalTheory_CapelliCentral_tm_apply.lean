-- Prove2me | solution 1 for GlobalTheory.CapelliCentral.tm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:37.923226+00:00
-- url     : https://prove2.me/submissions/130ade3f-dc29-427b-8157-de8d6d6dfb59

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SmoothAddSmul
import Theorems.Thm_GlobalTheory_CapelliCentral_eabEnd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CapelliCentral
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CapelliCentral
theorem _root_.solution (u : ℂ) (a b : Fin n) (F : smoothSpace ε E) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (h : ∀ g, inUJ ε g → F.1 g = f g) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (Tm (eabEnd ε E) u a b F).1 g = Top (EabV ε) u a b f g := by
  unfold Tm Formalism.QuantumDeterminants.Top
  rw [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, eabEnd_apply a b F h hg, ← h g hg]
  split_ifs <;> simp
end GlobalTheory.CapelliCentral
