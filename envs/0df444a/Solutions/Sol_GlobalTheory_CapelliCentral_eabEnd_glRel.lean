-- Prove2me | solution 1 for GlobalTheory.CapelliCentral.eabEnd_glRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:36.294615+00:00
-- url     : https://prove2.me/submissions/a6775454-9a8a-458b-8781-005fece8c810

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SmoothAddSmul
import Theorems.Thm_GlobalTheory_CapelliCentral_eabEnd_apply
import Theorems.Thm_Formalism_REAL_eabGlV


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
open Matrix
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CapelliCentral
namespace _root_.GlobalTheory.CapelliCentral
theorem _root_.solution : _root_.Formalism.REAL.GlRel (_root_.GlobalTheory.CapelliCentral.eabEnd ε E) := by
  intro a b c d
  refine LinearMap.ext fun F => ?_
  apply _root_.GlobalTheory.CapelliCentral.ext_on
  intro g hg
  have hF : ∀ (p q : Fin n) (G : _root_.GlobalTheory.CapelliCentral.smoothSpace ε E),
      (_root_.GlobalTheory.CapelliCentral.eabEnd ε E p q G).1 g = _root_.Formalism.REAL.EabV ε p q G.1 g :=
    fun p q G => _root_.GlobalTheory.CapelliCentral.eabEnd_apply p q G (fun _ _ => rfl) hg
  have hFF : ∀ p q r s : Fin n,
      (_root_.GlobalTheory.CapelliCentral.eabEnd ε E p q (_root_.GlobalTheory.CapelliCentral.eabEnd ε E r s F)).1 g =
        _root_.Formalism.REAL.EabV ε p q (_root_.Formalism.REAL.EabV ε r s F.1) g :=
    fun p q r s => _root_.GlobalTheory.CapelliCentral.eabEnd_apply p q _
      (fun _ hg' => _root_.GlobalTheory.CapelliCentral.eabEnd_apply r s F (fun _ _ => rfl) hg') hg
  have key := _root_.Formalism.REAL.eabGlV n ε E F.1 a b c d g F.2.1 hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, hFF]
  rw [key]
  split_ifs <;> simp [hF]
end _root_.GlobalTheory.CapelliCentral
end GlobalTheory.CapelliCentral
