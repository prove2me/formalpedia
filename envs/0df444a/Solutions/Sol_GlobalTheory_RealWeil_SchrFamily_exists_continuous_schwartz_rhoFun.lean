-- Prove2me | solution 1 for GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:49:07.735279+00:00
-- url     : https://prove2.me/submissions/232ed348-4947-4b23-bbc5-69ec95dfc9ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
import Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_continuous_rhoSch
import Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_seminorm_rhoSch_le
import Theorems.Thm_GlobalTheory_RealWeil_coe_rhoSch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.SchrFamily
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.SchrFamily
theorem _root_.solution : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n),
    Continuous G ∧ (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N :=
  fun _ f => ⟨fun w => rhoSch w f, continuous_rhoSch f, fun w => coe_rhoSch w f, seminorm_rhoSch_le f⟩
end GlobalTheory.RealWeil.SchrFamily
