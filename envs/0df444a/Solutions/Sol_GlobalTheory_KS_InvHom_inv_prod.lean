-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.inv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:58:23.510881+00:00
-- url     : https://prove2.me/submissions/dd876c3f-81f1-4cf8-b492-ee0eef9467d4

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
import Theorems.Thm_GlobalTheory_KS_InvHom_tan_one
import Theorems.Thm_GlobalTheory_KS_InvHom_tan_mul
import Theorems.Thm_GlobalTheory_KS_InvHom_inv_one
import Theorems.Thm_GlobalTheory_KS_InvHom_inv_mul
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
theorem _root_.solution : ∀ {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (d : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ i, IsTangent (u i)) →
    (∀ i, IsInvDer (u i) (d i)) →
      IsTangent (List.ofFn u).prod ∧ IsInvDer (List.ofFn u).prod (fun W f => ∑ i, d i W f)
  | 0, u, d, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨tan_one, inv_one⟩
  | n + 1, u, d, hu, hd => by
    obtain ⟨h₁, h₂⟩ := solution (fun i => u i.succ) (fun i => d i.succ) (fun i => hu _) (fun i => hd _)
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨tan_mul (hu 0) h₁, inv_mul (hu 0) h₁ (hd 0) h₂⟩
end GlobalTheory.KS.InvHom
