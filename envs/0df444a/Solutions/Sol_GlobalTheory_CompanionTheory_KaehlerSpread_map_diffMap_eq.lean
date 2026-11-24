-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KaehlerSpread.map_diffMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:48:28.174642+00:00
-- url     : https://prove2.me/submissions/84a58264-e3fc-415a-9230-2ed15f9d98b2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KaehlerSpread
open KaehlerDifferential
namespace GlobalTheory.CompanionTheory.KaehlerSpread
theorem _root_.solution (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [Algebra K B]
    [IsScalarTower K A B] [IsLocalization S B] :
    (IsLocalizedModule.mapExtendScalars S
      (Finsupp.mapRange.linearMap (Algebra.linearMap A B) : (Fin n →₀ A) →ₗ[A] (Fin n →₀ B))
      (map K K A B) B (diffMap K x)) =
      Finsupp.linearCombination B fun i => D K B (algebraMap A B (x i)) := by
  refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have h1 : (Finsupp.single i (1 : B) : Fin n →₀ B) =
      Finsupp.mapRange.linearMap (Algebra.linearMap A B) (Finsupp.single i (1 : A)) := by
    simp
  rw [h1, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
  simp [diffMap]
end GlobalTheory.CompanionTheory.KaehlerSpread
