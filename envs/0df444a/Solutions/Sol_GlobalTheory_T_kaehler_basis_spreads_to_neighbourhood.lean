-- Prove2me | solution 1 for GlobalTheory.T.kaehler_basis_spreads_to_neighbourhood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:22:09.249844+00:00
-- url     : https://prove2.me/submissions/ff936bf5-1ede-4510-84a9-47fea0780ebc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhoodStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_KaehlerSpread_spread


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
theorem _root_.solution : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KaehlerSpread.spread | exact GlobalTheory.CompanionTheory.KaehlerSpread.spread | (intros; apply GlobalTheory.CompanionTheory.KaehlerSpread.spread <;> assumption)
end _root_.GlobalTheory.T
