-- Prove2me | solution 1 for GlobalTheory.T.smooth_local_ring_free_differentials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:38.965201+00:00
-- url     : https://prove2.me/submissions/d2ad6c41-566c-44a8-895a-74af207e3e71

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SmoothLocalRingFreeDifferentials
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SmoothLocalRingFreeDifferentialsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_finitePresentation_and_kaehler_atPrime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g → ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime], letI := secAlgebra g U.1; Algebra.FinitePresentation K Γ(Y, U.1) ∧ Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | exact GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime <;> assumption)
end _root_.GlobalTheory.T
