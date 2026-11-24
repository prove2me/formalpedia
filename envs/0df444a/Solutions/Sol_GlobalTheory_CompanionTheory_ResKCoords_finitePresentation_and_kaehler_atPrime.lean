-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:30.680586+00:00
-- url     : https://prove2.me/submissions/01d3724d-044a-48f5-a2b9-d2ba79e53a1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SmoothLocalRingFreeDifferentials
import Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_kaehler_atPrime_of_away
import Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_finitePresentation_of_away

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
theorem _root_.solution :
    ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g →
      ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime],
      letI := secAlgebra g U.1
      Algebra.FinitePresentation K Γ(Y, U.1) ∧
        Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  intro K _ D Y g hg U P _
  letI := secAlgebra g U.1
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) g hg
    ⟨⊤, isAffineOpen_top _⟩ U (fun _ _ => trivial)
  have key : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t) := by
    intro t ht
    have h2 := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := D)).2
      _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (h' t ht)
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    rw [IsScalarTower.algebraMap_eq K Γ(Y, U.1) (Localization.Away t)]
    exact h2
  exact ⟨finitePresentation_of_away K _ D s hs key, kaehler_atPrime_of_away K _ D s hs key P⟩
end GlobalTheory.CompanionTheory.ResKCoords
