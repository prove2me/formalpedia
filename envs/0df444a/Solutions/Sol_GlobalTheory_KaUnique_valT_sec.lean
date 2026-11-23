-- Prove2me | solution 1 for GlobalTheory.KaUnique.valT_sec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:47.639798+00:00
-- url     : https://prove2.me/submissions/46adf974-2718-4e55-9d8c-ae59f48bbe28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
import Theorems.Thm_GlobalTheory_KaUnique_trU_val

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
open GlobalTheory GlobalTheory.KaUnique
variable {T T' : Type} [CommRing T] [CommRing T'] {X : Scheme.{0}}
namespace GlobalTheory.KaUnique
theorem _root_.solution (w : Sp T ⟶ X) (L : LB X) (c c' : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ L.U c) (h' : ⊤ ≤ w ⁻¹ᵁ L.U c') (l : ℕ)
    (s : LB.Sec (pw L (l : ℤ))) :
    valT w (L.U c) (s.f c) = (trU w L c c' h h').val ^ l * valT w (L.U c') (s.f c') := by
  have hh : ⊤ ≤ w ⁻¹ᵁ (L.U c ⊓ L.U c') := fun _ hp => ⟨h hp, h' hp⟩
  have e : rs X (inf_le_left : L.U c ⊓ L.U c' ≤ L.U c) (s.f c) =
      ((L.g c c') ^ (l : ℤ)).val * rs X (inf_le_right : L.U c ⊓ L.U c' ≤ L.U c') (s.f c') := s.compat c c'
  have e1 := valT_res w (inf_le_left : L.U c ⊓ L.U c' ≤ L.U c) hh (s.f c)
  have e2 := valT_res w (inf_le_right : L.U c ⊓ L.U c' ≤ L.U c') hh (s.f c')
  rw [← e1, ← e2, e, trU_val, valT_eq _ _ hh, valT_eq _ _ hh, valT_eq _ _ hh, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]
end GlobalTheory.KaUnique
