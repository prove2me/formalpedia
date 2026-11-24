-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.valT_via
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:26.000338+00:00
-- url     : https://prove2.me/submissions/e4765e23-96a7-4539-b9a9-ff47ed08a5ef

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
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_res
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_appLE
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_le_inf_pull
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
theorem _root_.solution {T : Type} [CommRing T] {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s)
    (p : Sp T ⟶ x'.P.A.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') :
    valT (p ≫ φ) (x.P.L.U c) (s.f c) =
      valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val ^ l *
        valT p (x'.P.L.U c') (s'.f c') := by
  have hle : (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' ≤ φ ⁻¹ᵁ x.P.L.U c := fun y hy => mem_pull.1 hy.1
  have hp := le_inf_pull p c c' h h'
  have e := congrArg (valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c')) (hs (fun _ => c) c' hle)
  refine (valT_appLE p φ hle hp _).symm.trans (e.trans ?_)
  refine (valT_eq p _ hp _).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
  · exact (map_pow _ _ _).trans (congrArg (· ^ l) (valT_eq p _ hp _).symm)
  · exact (valT_eq p _ hp _).symm.trans (valT_res p _ hp _)
end GlobalTheory.KeyKa.EtBaseChange
