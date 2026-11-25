-- Prove2me | solution 1 for GlobalTheory.T.kaehler_basis_on_localization_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:25:24.273395+00:00
-- url     : https://prove2.me/submissions/0a4b9a69-6568-4e39-a8bb-05c171082167

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisOnLocalizationAway
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisOnLocalizationAwayStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_ResKCoords_isCoords_basicOpen_of_away


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
theorem _root_.solution : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ} (x : Fin n → Γ(Y, U.1)), (letI := secAlgebra g U.1; ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) → IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | exact GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | (intros; apply GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away <;> assumption)
end _root_.GlobalTheory.T
