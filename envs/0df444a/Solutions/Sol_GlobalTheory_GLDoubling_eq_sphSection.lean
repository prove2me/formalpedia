-- Prove2me | solution 1 for GlobalTheory.GLDoubling.eq_sphSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:46.272648+00:00
-- url     : https://prove2.me/submissions/02197adb-9b40-45e8-9d43-3988937e86a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_isIwasawa
import Theorems.Thm_GlobalTheory_GLDoubling_sphSection_left
import Theorems.Thm_GlobalTheory_GLDoubling_sphSection_right
import Theorems.Thm_GlobalTheory_GLDoubling_sphSection_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution {s : ℂ} {Φ : GL (n ⊕ n) k → ℂ} (h1 : Φ 1 = 1)
    (hl : ∀ (p : siegel k n) h, Φ (p * h) = npow (absRatio k n p) (s + (Fintype.card n : ℂ) / 2) * Φ h)
    (hr : ∀ h, ∀ κ ∈ KO k (n ⊕ n), Φ (h * κ) = Φ h) : Φ = sphSection k n s := funext fun g => by
  obtain ⟨p, κ, hκ, rfl⟩ := isIwasawa.1 g
  rw [hr _ _ hκ, sphSection_right _ _ hκ, ← mul_one (p : GL (n ⊕ n) k), hl, sphSection_left, h1, sphSection_one]
end GlobalTheory.GLDoubling
