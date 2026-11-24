-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.invDer_along_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:38:47.410308+00:00
-- url     : https://prove2.me/submissions/f18d631e-cd32-4d67-84a6-ea330cdbf3b4

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
import Theorems.Thm_GlobalTheory_KS_InvHom_pbT_app
import Theorems.Thm_GlobalTheory_KS_InvHom_inv_comb
import Theorems.Thm_GlobalTheory_KS_InvHom_inv_hom
import Theorems.Thm_GlobalTheory_KS_pbT_constFn
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
theorem _root_.solution : ∀ (K : Type) [Field K] (A₁ A₀ : Over (Sp K)) [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (w : epsR K ⟶ A₁) (dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)) (c : Fin g → K), IsMonHom f → (∀ a, IsTangent (v a)) → IsTangent w → (∀ a, IsInvDer (v a) (dd a)) → IsInvDer w dw → IsLieComb c v (w ≫ f) → ∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)), dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = ∑ a, constFn A₁.hom _ (c a) * (f.left.app W).hom (dd a W h) := by
  intro K _ A₁ A₀ _ _ f g v dd w dw c hf hv hw hdd hdw hc W h
  obtain ⟨h₁, h₂⟩ := inv_comb hv hdd hc
  rw [inv_hom f hw h₁ hdw h₂, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, ← pbT_app f.left (constFn A₀.hom W (c a)), pbT_constFn _ _ le_rfl, Over.w f]
end GlobalTheory.KS.InvHom
