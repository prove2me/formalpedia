-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:59:58.064357+00:00
-- url     : https://prove2.me/submissions/7d9be48c-066e-4ffa-af15-330f53269481

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SmoothLocalRingFreeDifferentials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ResKCoords
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
namespace GlobalTheory.CompanionTheory.ResKCoords
theorem _root_.solution (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t)) :
    Algebra.FinitePresentation K A := by
  refine RingHom.finitePresentation_algebraMap.1
    (RingHom.finitePresentation_ofLocalizationSpanTarget (algebraMap K A) s hs fun r => ?_)
  haveI := h r.1 r.2
  haveI : Algebra.IsStandardSmooth K (Localization.Away r.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  rw [← IsScalarTower.algebraMap_eq K A (Localization.Away r.1)]
  exact (RingHom.finitePresentation_algebraMap).2 inferInstance
end GlobalTheory.CompanionTheory.ResKCoords
