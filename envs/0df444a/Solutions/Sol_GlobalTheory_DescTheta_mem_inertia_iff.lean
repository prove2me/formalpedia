-- Prove2me | solution 1 for GlobalTheory.DescTheta.mem_inertia_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:57.297535+00:00
-- url     : https://prove2.me/submissions/e7a7d8bb-e082-4849-870e-1ca1142796ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
import Theorems.Thm_GlobalTheory_DescTheta_evalAt_appLE
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
namespace GlobalTheory.DescTheta
theorem _root_.solution {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* Aut X) {W : X.Opens}
    (hW : IsAffineOpen W) (hst : ∀ g, W ≤ (ρ g).hom ⁻¹ᵁ W) (ξ : Sp k ⟶ X) (h : ⊤ ≤ ξ ⁻¹ᵁ W)
    (g : Γ) :
    letI := sectionsAction ρ W hst
    g⁻¹ ∈ (RingHom.ker (evalAt ξ W h)).inertia Γ ↔ ξ ≫ (ρ g).hom = ξ := by
  let := sectionsAction ρ W hst
  have e (b : Γ(X, W)) : g⁻¹ • b = ((ρ g).hom.appLE W W (hst g)).hom b := by
    have : g⁻¹ • b = ((ρ g⁻¹⁻¹).hom.appLE W W (hst _)).hom b := rfl
    simpa only [inv_inv] using this
  refine ⟨fun hg => ?_, fun hg b => ?_⟩
  · have e1 : ξ.appLE _ ⊤ h = (ρ g).hom.appLE _ _ (hst _) ≫ ξ.appLE _ ⊤ h := by
      rw [← cancel_mono (Scheme.ΓSpecIso (.of k)).hom]
      ext b
      have : evalAt ξ W h (g⁻¹ • b - b) = 0 := hg b
      rw [map_sub, sub_eq_zero, e] at this
      exact this.symm
    have hT := isAffineOpen_top (Sp k)
    have : IsIso hT.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
    symm
    rw [← cancel_epi hT.fromSpec, ← IsAffineOpen.SpecMap_appLE_fromSpec ξ hW hT h, e1,
      Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hW hW,
      IsAffineOpen.SpecMap_appLE_fromSpec_assoc ξ hW hT h]
  · change evalAt ξ W h (g⁻¹ • b - b) = 0
    rw [map_sub, sub_eq_zero, e]
    exact evalAt_appLE ξ _ _ _ _ _ b ξ hg h
end GlobalTheory.DescTheta
