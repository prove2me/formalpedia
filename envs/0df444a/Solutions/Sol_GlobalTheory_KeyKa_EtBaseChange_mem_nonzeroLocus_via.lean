-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.mem_nonzeroLocus_via
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:16.239413+00:00
-- url     : https://prove2.me/submissions/ecf23551-4133-4765-85a3-0ec2a25d2032

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.EtBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}
namespace GlobalTheory.KeyKa.EtBaseChange
theorem _root_.solution {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (hy : φ y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus s' := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨i, hi⟩ := exists_chart x'.P.isLB y
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    have := Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)
    refine this.ge ⟨⟨mem_pull.2 (x.P.A.left.basicOpen_le _ hk), hi⟩, hk⟩
  replace h1 := (Scheme.basicOpen_mul _ _ _).le ((congrArg x'.P.A.left.basicOpen e).le h1)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  exact ((Scheme.basicOpen_res _ _ _).le h1.2).2
end GlobalTheory.KeyKa.EtBaseChange
