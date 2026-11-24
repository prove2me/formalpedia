-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Par.isCompact_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:59:55.498568+00:00
-- url     : https://prove2.me/submissions/13676c33-fd5a-43dd-8096-21d46cefe5c8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Par
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Par
theorem _root_.solution (h : LF O ϖ nrm q) : IsCompact (O : Set F) := by
  rw [h.O_eq]
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))
end GlobalTheory.CompanionTheory.QL.Par
