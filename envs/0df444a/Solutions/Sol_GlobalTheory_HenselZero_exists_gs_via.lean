-- Prove2me | solution 1 for GlobalTheory.HenselZero.exists_gs_via
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:02:28.713749+00:00
-- url     : https://prove2.me/submissions/6ab9447a-d019-4bfe-ae0e-db661c24179e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TransversalZerosLiftOfIsAdicComplete
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
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
open GlobalTheory GlobalTheory.HenselZero
open GlobalTheory.KeyKa.EtBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}
namespace GlobalTheory.HenselZero
theorem _root_.solution {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (c : x.P.L.ι) (c' : x'.P.L.ι) (h : φ y ∈ x.P.L.U c) (h' : y ∈ x'.P.L.U c') :
    ∃ u, IsUnit u ∧ gs φ y (x.P.L.U c) (s.f c) = u * gs (𝟙 _) y (x'.P.L.U c') (s'.f c') := by
  have hle : (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' ≤ φ ⁻¹ᵁ x.P.L.U c := fun y hy => mem_pull.1 hy.1
  have hV : (𝟙 x'.P.A.left : _ ⟶ _) y ∈ (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' := ⟨mem_pull.2 h, h'⟩
  have e := congrArg (gs (𝟙 _) y _) (hs (fun _ => c) c' hle)
  have e₁ := (gs_res (𝟙 _) y hle hV ((φ.app _).hom (s.f c))).trans (gs_pull (𝟙 _) φ y _ h (s.f c))
  rw [Category.id_comp] at e₁
  refine ⟨_, ?_, e₁.symm.trans (e.trans ((gs_mul _ _ _ hV _ _).trans
    (congrArg (_ * ·) (gs_res (𝟙 _) y inf_le_right hV _))))⟩
  rw [gs_eq _ _ _ hV]
  exact (((Units.isUnit (w.s (fun _ => c, c'))).pow l).map _).map _
end GlobalTheory.HenselZero
