-- Prove2me | solution 1 for GlobalTheory.T.exists_transversal_zeros_of_residue_zeros_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:30.439669+00:00
-- url     : https://prove2.me/submissions/374efe46-4ddc-47af-92c5-6e1afacc2e67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TransversalZerosLiftOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TransversalZerosLiftOfIsAdicCompleteStatement
import Theorems.Thm_GlobalTheory_KeyKa_etZ_lift_of_isAdicComplete


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (xk : KeyIn (IsLocalRing.ResidueField O)) φ w (n d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), KeyVia xk x (IsLocalRing.residue O) φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  first | exact @GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete | exact GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete | (intros; apply GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete <;> assumption)
end _root_.GlobalTheory.T
