-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_upper_mul_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:59:39.12205+00:00
-- url     : https://prove2.me/submissions/fd1be21f-87d5-4409-9e41-a41b751a82e7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_vecMul_unitary
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_map
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_vecMul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
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
attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Reduction.finAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finEval_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infEval_apply
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (φ : E ≃+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (h : GL (Fin n) E) :
    ∃ b : GL (Fin n) E, (b : Matrix (Fin n) (Fin n) E).IsUpperTriangular ∧
      ∃ k : GL (Fin n) E, (∀ y : Fin n → E,
        euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) E)) = euclidNorm y) ∧ h = b * k := by
  have hφ' : ∀ x, ‖φ.symm x‖ = ‖x‖ := fun x => by rw [← hφ, RingEquiv.apply_symm_apply]
  set h' := Matrix.GeneralLinearGroup.map φ.toRingHom h with hh'
  obtain ⟨k, a, ha, u, hu, hu1, hg⟩ := exists_KAN (h'⁻¹)
  set kU : GL (Fin n) 𝕜 := Unitary.toUnits k with hkU
  have hkU_val : (kU : Matrix (Fin n) (Fin n) 𝕜) = (k : Matrix (Fin n) (Fin n) 𝕜) := rfl
  set b'' : GL (Fin n) 𝕜 := h' * kU with hb''

  set Du : Matrix (Fin n) (Fin n) 𝕜 := (Matrix.diagonal fun i => ((a i : ℝ) : 𝕜)) * u with hDu
  have hleft : (b'' : Matrix (Fin n) (Fin n) 𝕜) * Du = 1 := by
    have h1 : (h' : Matrix (Fin n) (Fin n) 𝕜) * ((h'⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hg] at h1
    rw [hb'', Units.val_mul, hkU_val, hDu]
    simpa only [Matrix.mul_assoc] using h1
  have hDu_upper : Du.IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal _).mul hu
  have hinv : (b'' : Matrix (Fin n) (Fin n) 𝕜) = Du⁻¹ :=
    (Matrix.inv_eq_left_inv hleft).symm
  let _ : Invertible Du := ⟨(b'' : Matrix (Fin n) (Fin n) 𝕜), hleft, mul_eq_one_comm.1 hleft⟩
  have hb''_upper : (b'' : Matrix (Fin n) (Fin n) 𝕜).IsUpperTriangular := by
    rw [hinv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hDu_upper
  refine ⟨Matrix.GeneralLinearGroup.map φ.symm.toRingHom b'', ?_,
    Matrix.GeneralLinearGroup.map φ.symm.toRingHom kU⁻¹, ?_, ?_⟩
  · intro i j hij
    change φ.symm ((b'' : Matrix (Fin n) (Fin n) 𝕜) i j) = 0
    rw [hb''_upper hij, map_zero]
  · intro y
    have hk' : ((kU⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) ∈ unitaryGroup (Fin n) 𝕜 := by
      have : ((kU⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) = ((k⁻¹ : unitaryGroup (Fin n) 𝕜) :
          Matrix (Fin n) (Fin n) 𝕜) := by
        rw [hkU, ← map_inv]
        rfl
      rw [this]
      exact (k⁻¹).2
    rw [← euclidNorm_map φ.toRingHom hφ, ← euclidNorm_map φ.toRingHom hφ y]
    have : (fun i => φ.toRingHom ((y ᵥ* ((Matrix.GeneralLinearGroup.map φ.symm.toRingHom kU⁻¹ :
        GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) i)) =
        (fun i => φ.toRingHom (y i)) ᵥ* ((kU⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) := by
      ext j
      simp [vecMul, dotProduct, map_sum, map_mul, Matrix.GeneralLinearGroup.map]
    rw [this, euclidNorm_vecMul_unitary hk']
  · rw [← map_mul, hb'', mul_assoc, mul_inv_cancel, mul_one, hh']
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
end GroundTheory.Automorphic.Reduction
