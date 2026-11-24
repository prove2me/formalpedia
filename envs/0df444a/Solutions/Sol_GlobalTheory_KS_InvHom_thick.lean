-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:43:54.136958+00:00
-- url     : https://prove2.me/submissions/2f9c250b-aba0-4374-9ab1-9c9ac79e496e

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
import Theorems.Thm_GlobalTheory_ConstThickening_structure_dualNumber
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
namespace GlobalTheory.KS.InvHom
theorem _root_.solution (A : Over (Sp K)) :
    (∀ O : (epsR K ⊗ A).left.Opens, (snd (epsR K) A).left ⁻¹ᵁ ((jA A).left ⁻¹ᵁ O) = O) ∧
    ∀ (O : A.left.Opens) (F : Γ((epsR K ⊗ A).left, (snd (epsR K) A).left ⁻¹ᵁ O)),
      ∃! ab : Γ(A.left, O) × Γ(A.left, O), F = ((snd (epsR K) A).left.app O).hom ab.1 +
        constFn (R := DualNumber K) (fst (epsR K) A).left _ DualNumber.eps *
          ((snd (epsR K) A).left.app O).hom ab.2 := by
  have h := GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left
    (jA A).left (IsPullback.of_hasPullback (epsR K).hom A.hom).flip
    (by rw [← Over.comp_left, jA, lift_snd]; rfl)
    (by
      have : jA A ≫ fst (epsR K) A = toUnit A ≫ zeroPt K := by rw [jA, lift_fst]
      exact congrArg CommaMorphism.left this)
  exact ⟨h.1, h.2.2⟩
end GlobalTheory.KS.InvHom
