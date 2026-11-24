-- Prove2me | solution 1 for GlobalTheory.LevCover.exists_lift_geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:45.953556+00:00
-- url     : https://prove2.me/submissions/e1365872-2458-417e-9a13-edfa13343e53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {S : Scheme.{0}}
namespace GlobalTheory.LevCover
theorem _root_.solution {W Z : Scheme.{0}} (p : W ⟶ Z) [IsFinite p] {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z) (hz : Set.range z ⊆ Set.range p) : ∃ w : Sp k ⟶ W, w ≫ p = z := by
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  have h1 : pt ∈ Set.range (pullback.snd p z) := by
    rw [Scheme.Pullback.range_snd]
    exact hz ⟨pt, rfl⟩
  obtain ⟨y, -⟩ := h1
  have : Nonempty (pullback p z : Scheme) := ⟨y⟩
  have : IsAffine (pullback p z) := isAffine_of_isAffineHom (pullback.snd p z)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := (pullback p z : Scheme))).exists_closed_singleton Set.univ_nonempty
  refine ⟨pointOfClosedPoint (pullback.snd p z) x hx ≫ pullback.fst p z, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
end GlobalTheory.LevCover
