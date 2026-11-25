-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NoethApprox.schemeModels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:05.995676+00:00
-- url     : https://prove2.me/submissions/d46095a9-3bef-4b3b-947a-79ba2cb01ed0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchemeModelsSpread
import Theorems.Thm_GlobalTheory_SpreadScheme_hasModel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NoethApprox
namespace GlobalTheory.CompanionTheory.NoethApprox
theorem _root_.solution : GlobalTheory.SpreadingModels.SchemeModels := by
  intro R _ Y f h₁ h₂ h₃
  obtain ⟨R₀, i, φ, Y₀, f₀, π, a, b, c, d, e⟩ := GlobalTheory.SpreadScheme.hasModel (V := R) f
  exact ⟨R₀, i, φ, Y₀, f₀, π, a, b, d, c, e⟩
end GlobalTheory.CompanionTheory.NoethApprox
