-- Prove2me | solution 1 for GlobalTheory.ZM.ClosedCoord.eq_zero_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:43.207842+00:00
-- url     : https://prove2.me/submissions/f08b6a76-b737-4c9c-a120-1391634888de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProjectiveCoordinateRepresentationClosedSubsch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ClosedCoord
open MvPolynomial
namespace GlobalTheory.ZM.ClosedCoord
theorem _root_.solution {R' σ : Type} [CommRing R'] (v : σ → R') (hv : Ideal.span (Set.range v) = ⊤) (r : R')
    (h : ∀ a, algebraMap R' (Localization.Away (v a)) r = 0) : r = 0 := by
  have : r ∈ (⊥ : Ideal R') := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range v) hv r ?_
    rintro ⟨_, a, rfl⟩
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (v a)) _ r).1 (h a)
    exact ⟨n, by simpa using hn⟩
  simpa using this
end GlobalTheory.ZM.ClosedCoord
