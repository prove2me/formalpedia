-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.valT_spMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:45.479327+00:00
-- url     : https://prove2.me/submissions/0add25ea-9111-46d2-84e0-2c48929f5c3b

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
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_eq

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
variable {T T' : Type} [CommRing T] [CommRing T'] {X Y : Scheme.{0}}
namespace GlobalTheory.KeyKa.EtBaseChange
theorem _root_.solution (F : T →+* T') (w : Sp T ⟶ X) {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) :
    valT (spMap F ≫ w) U a = F (valT w U a) := by
  have h' : ⊤ ≤ (spMap F ≫ w) ⁻¹ᵁ U := fun p _ => h (show spMap F p ∈ ⊤ from trivial)
  rw [valT_eq w U h, valT_eq _ U h']
  have e := congrArg (fun q => q.hom a) (Scheme.Hom.appLE_comp_appLE (spMap F) w U ⊤ ⊤ h (fun _ _ => trivial))
  have e2 := congrArg (fun q => q.hom ((w.appLE U ⊤ h).hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom F))
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of T')).hom.hom e).symm.trans (Eq.trans ?_ e2)
  have e3 : (spMap F).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap F).appTop := Scheme.Hom.appLE_eq_app _
  simp only [e3]
  rfl
end GlobalTheory.KeyKa.EtBaseChange
