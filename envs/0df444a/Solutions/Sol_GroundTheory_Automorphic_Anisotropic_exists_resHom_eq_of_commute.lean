-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.exists_resHom_eq_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:34.442995+00:00
-- url     : https://prove2.me/submissions/dfd24db7-d03e-4dfe-a14c-7b9b7ab686d2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_resHom_injective
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_exists_blockHom_eq
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Anisotropic.rmatHom_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)
variable {R}
variable (R)
variable {R}
variable (R)
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (γ : GL (Fin 𝒩) K)
    (hγ : ∀ j, (γ : Matrix (Fin 𝒩) (Fin 𝒩) K) * resScalar (ι := ι) b j =
      resScalar (ι := ι) b j * γ) :
    ∃ M : GL ι (K ⊗[K] E), resHom b K (M : Matrix ι ι (K ⊗[K] E)) = γ := by
  have key : ∀ g : Matrix (Fin 𝒩) (Fin 𝒩) K, (∀ j, g * resScalar (ι := ι) b j =
      resScalar (ι := ι) b j * g) → ∃ M, resHom b K M = g := by
    intro g hg
    obtain ⟨M, hM⟩ := exists_blockHom_eq b K ((Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))).symm g) fun j => by
      have h := congrArg (Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))).symm (hg j)
      rw [map_mul, map_mul] at h
      have e : (Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))).symm (resScalar (ι := ι) b j) =
          blockHom b K (Matrix.scalar ι (baseBasis b K j)) := by
        show (Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))).symm
          (Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))
            (blockHom b K (Matrix.scalar ι (baseBasis b K j)))) = _
        exact AlgEquiv.symm_apply_apply _ _
      rw [e] at h
      exact h.symm
    refine ⟨M, ?_⟩
    show Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ)) (blockHom b K M) = g
    rw [hM]
    exact AlgEquiv.apply_symm_apply _ _
  obtain ⟨M₀, h₀⟩ := key γ hγ
  obtain ⟨M₁, h₁⟩ := key (↑γ⁻¹ : Matrix (Fin 𝒩) (Fin 𝒩) K) fun j => by
    calc (↑γ⁻¹ : Matrix (Fin 𝒩) (Fin 𝒩) K) * resScalar (ι := ι) b j
        = ↑γ⁻¹ * (resScalar (ι := ι) b j * ↑γ) * ↑γ⁻¹ := by simp [mul_assoc]
      _ = ↑γ⁻¹ * (↑γ * resScalar (ι := ι) b j) * ↑γ⁻¹ := by rw [hγ]
      _ = resScalar (ι := ι) b j * ↑γ⁻¹ := by simp
  have e1 : M₀ * M₁ = 1 := resHom_injective b K (by rw [map_mul, map_one, h₀, h₁, γ.mul_inv])
  have e2 : M₁ * M₀ = 1 := resHom_injective b K (by rw [map_mul, map_one, h₀, h₁, γ.inv_mul])
  exact ⟨⟨M₀, M₁, e1, e2⟩, h₀⟩
end GroundTheory.Automorphic.Anisotropic
