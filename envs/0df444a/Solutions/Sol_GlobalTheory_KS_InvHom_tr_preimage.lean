-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.tr_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:30.835362+00:00
-- url     : https://prove2.me/submissions/74c544ac-f00a-4300-b635-991c2232eff0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHom
import Theorems.Thm_GlobalTheory_KS_InvHom_thick
import Theorems.Thm_GlobalTheory_PowLie_isTangent_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.PowLie (sc zeroPt isTangent_iff)
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.InvHom
variable {K : Type} [Field K]
variable {A : Over (Sp K)} [GrpObj A]
namespace GlobalTheory.KS.InvHom
theorem _root_.solution {v : epsR K ⟶ A} (hv : IsTangent v) (W : A.left.Opens) :
    (tr v).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  have h : jA A ≫ tr v = 𝟙 A := by
    rw [MonObj.comp_mul, ← Category.assoc, jA, lift_fst, lift_snd, Category.assoc,
      (isTangent_iff v).1 hv]
    exact _root_.one_mul (𝟙 A)
  rw [← (thick A).1 ((tr v).left ⁻¹ᵁ W), ← Scheme.Hom.comp_preimage (jA A).left, ← Over.comp_left, h]
  rfl
end GlobalTheory.KS.InvHom
