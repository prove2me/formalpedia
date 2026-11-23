-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.top_le_iff_residue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:54.838531+00:00
-- url     : https://prove2.me/submissions/ed53081a-16f9-47b9-94fa-9e60bff9338c

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
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}
namespace GlobalTheory.ArtinKernel
theorem _root_.solution [Subsingleton (PrimeSpectrum R)] (ρ : R →+* ℂ) (x : Sp R ⟶ X) (y : Sp ℂ ⟶ X)
    (hy : spMap ρ ≫ x = y) (W : X.Opens) : ⊤ ≤ x ⁻¹ᵁ W ↔ ⊤ ≤ y ⁻¹ᵁ W := by
  subst hy
  refine ⟨preimage_whole_comp_of_preimage_whole _ _, fun h p _ => ?_⟩
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hq : (spMap ρ).base q ∈ x ⁻¹ᵁ W := h (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have e : (spMap ρ).base q = p := Subsingleton.elim (α := PrimeSpectrum R) _ _
  rw [e] at hq
  exact hq
end GlobalTheory.ArtinKernel
