-- Prove2me | solution 1 for GlobalTheory.RealWeil.SchrFamily.rhoSch_rhoSch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:42:28.079883+00:00
-- url     : https://prove2.me/submissions/aed2d89d-be84-4773-a800-51b246d00ba7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
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
theorem _root_.solution (w₀ u : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w₀ (rhoSch u g) = Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) • rhoSch (w₀ + u) g := by
  ext x
  rw [coe_rhoSch, coe_rhoSch, rhoFun_rhoFun, SchwartzMap.smul_apply, coe_rhoSch]
  rfl
end GlobalTheory.RealWeil.SchrFamily
