-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.top_le_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:45.451051+00:00
-- url     : https://prove2.me/submissions/d85485a1-a091-4c6c-997e-c8dd5c6f5654

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
section Points
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}
private theorem preimage_whole_comp_of_preimage_whole {Z W V : Scheme.{0}} (f : Z ⟶ W) (x : W ⟶ V) {U : V.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (f ≫ x) ⁻¹ᵁ U := by
  intro p _
  exact h (show f.base p ∈ (⊤ : W.Opens) from trivial)
end Points
section Family
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {A : Over (Sp ℂ)}
variable [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable [Module.Finite ℂ R]
end Family
end GlobalTheory.ArtinKernel
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {A : Over (Sp ℂ)}
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A.left.Opens) (h' : ⊤ ≤ y.left ⁻¹ᵁ U) :
    ⊤ ≤ (toUnit (spO R) ≫ y).left ⁻¹ᵁ U := by
  rw [Over.comp_left]
  exact preimage_whole_comp_of_preimage_whole _ _ h'
end GlobalTheory.ArtinKernel
