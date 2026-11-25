-- Prove2me | solution 1 for GlobalTheory.ConstFam.val_feGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:21:42.657649+00:00
-- url     : https://prove2.me/submissions/c1d57d48-bc71-4bc2-a1da-455990c0b8f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {k : Type} [Field k] (D : DegPre k)
namespace GlobalTheory.ConstFam
theorem _root_.solution (j : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of k))} (ρ : T ⟶ D.P.A) (κ : T ⟶ TK k)
    {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (feGen D j mu α) ρ.left z J =
      cubN (th D z J) j (cP D T α) (cP D T mu) ρ * (th D z J (cP D T α) ρ (cP D T mu))⁻¹ *
        (val (D.tau mu α) κ.left z J * (val (D.psi mu) κ.left z J ^ j * val D.rigK κ.left z J ^ j)) :=
  (exists_feGen D j mu α).choose_spec.2 T ρ κ z J hJ
end GlobalTheory.ConstFam
