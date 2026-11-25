-- Prove2me | solution 1 for GlobalTheory.T.cartan_decomposition_generalLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:26.732222+00:00
-- url     : https://prove2.me/submissions/e2629a06-88f8-4bfc-8083-25506b5d6942

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinear
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinearStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_KAK_cartan


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), ∃ k₁ ∈ GLint O n, ∃ k₂ ∈ GLint O n, ∃ (e : Fin n → ℤ) (d : GL (Fin n) F), (d : Matrix (Fin n) (Fin n) F) = Matrix.diagonal (fun i => ϖ ^ e i) ∧ g = k₁ * d * k₂ := by
  first | exact @GlobalTheory.CompanionTheory.QL.KAK.cartan | exact GlobalTheory.CompanionTheory.QL.KAK.cartan | (intros; apply GlobalTheory.CompanionTheory.QL.KAK.cartan <;> assumption)
end _root_.GlobalTheory.T
