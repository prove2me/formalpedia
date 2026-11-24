-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:23:00.894335+00:00
-- url     : https://prove2.me/submissions/24df47c9-6b72-4ca9-b790-fbde38616d73

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
import Theorems.Thm_GlobalTheory_KS_InvHom_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_InvHom_tr_preimage
import Theorems.Thm_GlobalTheory_KS_pbT_add
import Theorems.Thm_GlobalTheory_KS_pbT_constFn
import Theorems.Thm_GlobalTheory_KS_pbT_mul
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
theorem _root_.solution {v : epsR K ⟶ A} (hv : IsTangent v) {dd} (hd : IsInvDer v dd) {Z : Over (Sp K)}
    (S : Z ⟶ epsR K ⊗ A) (W : A.left.Opens) (f : Γ(A.left, W)) (O : Z.left.Opens)
    (hO : O ≤ (S ≫ snd (epsR K) A).left ⁻¹ᵁ W) :
    pbT (S ≫ tr v).left f O = pbT (S ≫ snd (epsR K) A).left f O +
      constFn (R := DualNumber K) (S ≫ fst (epsR K) A).left O DualNumber.eps *
        pbT (S ≫ snd (epsR K) A).left (dd W f) O := by
  have hO' : O ≤ S.left ⁻¹ᵁ ((snd (epsR K) A).left ⁻¹ᵁ W) := hO
  have h := congrArg (fun s => pbT S.left s O) (hd W f)
  simp only [pbT_add, pbT_mul] at h
  rw [pbT_pbT _ _ (tr_preimage hv W).ge hO', pbT_pbT _ _ le_rfl hO', pbT_pbT _ _ le_rfl hO',
    pbT_constFn _ _ hO'] at h
  exact h
end GlobalTheory.KS.InvHom
