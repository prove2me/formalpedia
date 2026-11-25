-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.exists_eval_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:50.884935+00:00
-- url     : https://prove2.me/submissions/83a48615-837b-41ef-8633-ccb55fcc5822

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJInducedCoeff
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_mem_fixedVectors
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_subgroupOf_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_subgroupOf_levi
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_act
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_exists_blockUpper_mul_integralGL__7c8211cc1088
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa MeasureTheory
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (hσ : IsSmooth σ) {m : ℕ} {R : Finset (GL (Fin n) F)}
    (hR₀ : ∀ x ∈ R, x ∈ integralGL F n)
    (hR : ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m)
    (lam : Module.Dual ℂ (parabolicIndSpace F n β σ)) :
    ∃ ℓ : GL (Fin n) F → Module.Dual ℂ W,
      (∀ x, ℓ x ∈ fixedVectors (Representation.dual σ)
        ((congruenceSubgroup F n m).subgroupOf (levi F n β))) ∧
      ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
        lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) := by
  classical
  have : LocallyCompactSpace (levi F n β) :=
    isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set K := congruenceSubgroup F n m
  set KM : Subgroup (levi F n β) := K.subgroupOf (levi F n β)
  have hKMc : IsCompact (KM : Set (levi F n β)) :=
    isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m)
  have hKMo : IsOpen (KM : Set (levi F n β)) :=
    isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m)
  set e := fixedProj σ hσ hKMc hKMo

  let E : fixedVectors (parabolicInd F n β σ) K →ₗ[ℂ] (R → W) :=
    LinearMap.pi fun x : R =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) (x : GL (Fin n) F)) ∘ₗ
        (parabolicIndSpace F n β σ).subtype ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype
  have hE : ∀ ψ, E ψ = 0 → ψ = 0 := by
    intro ψ hψ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) g
    obtain ⟨x, hxR, hxk⟩ := hR k hk
    have h0 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x = 0 := by
      have := congrFun hψ ⟨x, hxR⟩
      simpa [E] using this
    have hfix := ψ.2 (x⁻¹ * k) hxk
    have h1 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * k) =
        ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * x) := by
      have := congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (p * x)) hfix
      simp only [coe_indRep_apply] at this
      rw [← this, mul_assoc, mul_inv_cancel_left]
    rw [h1, ((ψ : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ x), h0]
    simp
  have hker : LinearMap.ker E = ⊥ := LinearMap.ker_eq_bot'.2 hE
  obtain ⟨E', hE'⟩ := LinearMap.exists_leftInverse_of_injective (K := ℂ)
    (V := fixedVectors (parabolicInd F n β σ) K) (V' := R → W) E hker
  let L := lam ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype ∘ₗ E'
  refine ⟨fun x => if hx : x ∈ R then
      L ∘ₗ LinearMap.single ℂ (fun _ : R => W) ⟨x, hx⟩ ∘ₗ (fixedVectors σ KM).subtype ∘ₗ e
    else 0, fun x => ?_, fun ψ hψ => ?_⟩
  · by_cases hx : x ∈ R
    · dsimp only
      rw [dif_pos hx, mem_fixedVectors_dual]
      intro k hk w
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [fixedProj_apply_act hσ hKMc hKMo hk]
    · dsimp only
      rw [dif_neg hx]
      exact zero_mem _
  · have hval : ∀ x ∈ R, ((fixedProj σ hσ hKMc hKMo ((ψ : GL (Fin n) F → W) x) :
        fixedVectors σ KM) : W) = (ψ : GL (Fin n) F → W) x := fun x hx =>
      fixedProj_apply_of_mem hσ hKMc hKMo
        (apply_mem_fixedVectors (f := ⟨ψ, hψ⟩) (hR₀ x hx))
    have hEψ : E ⟨ψ, hψ⟩ = ∑ x : R, LinearMap.single ℂ (fun _ : R => W) x
        ((ψ : GL (Fin n) F → W) x) := by
      funext y
      simp [E, Finset.sum_apply, Pi.single_apply]
    have hlam : lam ψ = L (E ⟨ψ, hψ⟩) := by
      simp only [L, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [← LinearMap.comp_apply E' E, hE', LinearMap.id_apply]
    rw [hlam, hEψ, map_sum, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [dif_pos x.2]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hval x x.2]
end GroundTheory.Automorphic.GodementJacquet
