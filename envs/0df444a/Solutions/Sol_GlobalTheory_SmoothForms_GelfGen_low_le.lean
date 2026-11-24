-- Prove2me | solution 1 for GlobalTheory.SmoothForms.GelfGen.low_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:58.547724+00:00
-- url     : https://prove2.me/submissions/b7e47b74-05cf-42d3-b299-29ce82652044

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms
noncomputable section
open GlobalTheory.SmoothForms.PermWord
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.GelfGen
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.GelfGen
theorem _root_.solution (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) ≤ Algebra.adjoin ℂ (Set.range (gelfA E)) :=
  Algebra.adjoin_mono (by rintro _ ⟨k, rfl⟩; exact ⟨k.val, rfl⟩)
end GlobalTheory.SmoothForms.GelfGen
