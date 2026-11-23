-- Prove2me | solution 1 for GlobalTheory.WeilIsogeny.exists_gen_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:27.83905+00:00
-- url     : https://prove2.me/submissions/65916c18-0c5e-4095-ac20-3935e3ddc904

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenMovePow

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilIsogeny
open CommutatorPairing
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}
namespace GlobalTheory.WeilIsogeny
theorem _root_.solution (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val u r z J = val t r z J ^ d := by
  refine ⟨⟨fun j => t.s j ^ d⟩, fun i j => ?_, fun Z r z J => map_pow _ _ _⟩
  have h := congrArg (· ^ d) (ht i j)
  simp only [mul_pow, ← map_pow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact ((zpow_natCast _ _).symm.trans (zpow_mul _ _ _).symm).trans (congrArg _ (hε a).symm)
end GlobalTheory.WeilIsogeny
