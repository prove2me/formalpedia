-- Prove2me | solution 1 for GlobalTheory.T.iwasawa_decomposition_upperTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:46.745951+00:00
-- url     : https://prove2.me/submissions/0665a03b-5d31-4a72-bf94-5cb5520f28dd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangular
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangularStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Iwasawa_exists_upper_mul_int


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), ∃ b : GL (Fin n) F, (b : Matrix (Fin n) (Fin n) F).BlockTriangular id ∧ ∃ k ∈ GLint O n, g = b * k := by
  first | exact @GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int | exact GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int | (intros; apply GlobalTheory.CompanionTheory.QL.Iwasawa.exists_upper_mul_int <;> assumption)
end _root_.GlobalTheory.T
