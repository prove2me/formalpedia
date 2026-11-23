-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.exists_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:29.299282+00:00
-- url     : https://prove2.me/submissions/78871379-6a13-4e8e-abae-409ac666278c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution {P U Y : Type*} [TopologicalSpace P] [TopologicalSpace U] (p : P → Y) (x : Y)
    (hF : IsPreirreducible (p ⁻¹' {x})) (i g : U → P) (hi : Continuous i) (hg : IsOpenMap g)
    (h : ∀ u, p (g u) = p (i u)) (W O : Set P) (hW : IsOpen W) (hO : IsOpen O)
    (hWi : W ⊆ Set.range i) (h1 : (p ⁻¹' {x} ∩ W).Nonempty) (h2 : (p ⁻¹' {x} ∩ O).Nonempty) :
    ∃ u, i u ∈ W ∧ p (i u) = x ∧ g u ∈ O := by
  obtain ⟨w, hw, hwW⟩ := h1
  obtain ⟨u, rfl⟩ := hWi hwW
  obtain ⟨_, hz, ⟨v, hv, rfl⟩, hzO⟩ := hF _ _ (hg _ (hW.preimage hi)) hO
    ⟨g u, (h u).trans hw, u, hwW, rfl⟩ h2
  exact ⟨v, hv, (h v).symm.trans hz, hzO⟩
end GlobalTheory.SS.StrictLaw
