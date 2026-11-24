-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.inv_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:26.591777+00:00
-- url     : https://prove2.me/submissions/dca59ef1-7f1c-4482-ae7c-2e42526b4f45

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
import Theorems.Thm_GlobalTheory_KS_InvHom_tan_sc
import Theorems.Thm_GlobalTheory_KS_InvHom_inv_sc
import Theorems.Thm_GlobalTheory_KS_InvHom_inv_prod
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
theorem _root_.solution {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    {d : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hv : ∀ i, IsTangent (v i))
    (hd : ∀ i, IsInvDer (v i) (d i)) (hw : IsLieComb c v w) :
    IsTangent w ∧ IsInvDer w (fun W f => ∑ i, constFn A.hom W (c i) * d i W f) := by
  obtain ⟨u, hu, rfl⟩ := hw
  have e : ∀ i, u i = sc (c i) ≫ v i := fun i => Over.OverMorphism.ext (hu i)
  exact inv_prod u (fun i W f => constFn A.hom W (c i) * d i W f) (fun i => e i ▸ tan_sc (hv i) _)
    (fun i => e i ▸ inv_sc (hv i) (hd i) _)
end GlobalTheory.KS.InvHom
