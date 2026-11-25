-- Prove2me | solution 1 for GlobalTheory.DescTheta.exists_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:38.082802+00:00
-- url     : https://prove2.me/submissions/7c0c5517-037c-4ece-8a59-41c68b72ca47

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
theorem _root_.solution {Γ : Type} [Group Γ] [Fintype Γ] {Y' : Scheme.{0}} (τ : Γ →* Aut Y)
    (φ : Y ⟶ Y') (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hq : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    {L : LB Y'} (O : Y'.Opens) (s : Γ(toMod (L.pull φ), φ ⁻¹ᵁ O)) :
    ∃ t : Γ(toMod L, O), ∀ i, (φ.app (O ⊓ L.U i)).hom (coord t i) =
      ∑ g : Γ, ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom
        (resG Y (le_pull_chart φ O i :
          φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i)) (coord s (fun _ => i))) := by
  have H (i : L.ι) (u : Γ(Y, φ ⁻¹ᵁ (O ⊓ L.U i))) :
      (∑ g : Γ, ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom u) ∈
        Set.range (φ.app (O ⊓ L.U i)).hom := by
    refine (hq _).2 _ fun k _ => ?_
    let := sectionsAction τ _ (preimage_le_of_invariant τ φ hφ (O ⊓ L.U i))
    have e : k⁻¹ • ∑ g : Γ, g • u = ∑ g : Γ, g • u := by
      rw [Finset.smul_sum]
      simp only [← mul_smul]
      exact Equiv.sum_comp (Equiv.mulLeft k⁻¹) (fun g => g • u)
    have e' : ((τ k⁻¹⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom
      (∑ g : Γ, g • u) = ∑ g : Γ, g • u := e
    simp only [inv_inv] at e'
    exact e'
  choose t ht using fun i => H i (resG Y (le_pull_chart φ O i :
          φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i)) (coord s (fun _ => i)))
  refine ⟨mkSec t fun i j => ((hq _).1 ?_), ht⟩
  have l (i : L.ι) : φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i) :=
    le_pull_chart φ O i
  have li : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U i := inf_le_left
  have lj : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U j := inf_le_inf_right _ inf_le_left
  have key (k : L.ι) (lk : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U k) :
      (φ.app _).hom (resG Y' lk (t k)) = ∑ g : Γ,
        ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ (O ⊓ L.U i ⊓ L.U j) _)).hom
          (resG Y ((φ.preimage_mono lk).trans (l k)) (coord s (fun _ => k))) := by
    rw [Scheme.Hom.app_eq_appLE, appLE_resG, ← resG_app, ht k, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [resG_appLE, appLE_resG, appLE_resG]
  rw [map_mul, key i li, key j lj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [coord_rel s (fun _ => i) (fun _ => j) _ ((φ.preimage_mono lj).trans (l j))
    (le_inf (((φ.preimage_mono li).trans (l i)).trans inf_le_right)
      (((φ.preimage_mono lj).trans (l j)).trans inf_le_right)), map_mul,
    resG_pull_g φ (L := L) (fun _ => i) (fun _ => j)]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, appLE_resG, ← RingHom.comp_apply, ← CommRingCat.hom_comp]
  simp only [Scheme.Hom.appLE_comp_appLE, hφ]
end GlobalTheory.DescTheta
