-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.isClopen_shell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:39.859812+00:00
-- url     : https://prove2.me/submissions/7569ca25-6132-430a-aa8b-1a85841fa668

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_det_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_isClosed_valBall
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
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
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (F n)
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (k : ℤ) : IsClopen {g : GL (Fin n) F | ordDet g = k} := by
  have hcont : Continuous fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F).det :=
    Units.continuous_val.matrix_det
  have hset : {g : GL (Fin n) F | ordDet g = k} = (fun g : GL (Fin n) F =>
      (g : Matrix (Fin n) (Fin n) F).det) ⁻¹'
        ((LocalField.valBall F k : Set F) \ (LocalField.valBall F (k + 1) : Set F)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      LocalField.mem_valBall_iff_le_ord (det_ne_zero g), ordDet]
    omega
  rw [hset]
  have c1 : IsClopen (LocalField.valBall F k : Set F) :=
    ⟨LocalField.isClosed_valBall k, LocalField.isOpen_valBall k⟩
  have c2 : IsClopen (LocalField.valBall F (k + 1) : Set F) :=
    ⟨LocalField.isClosed_valBall (k + 1), LocalField.isOpen_valBall (k + 1)⟩
  exact (c1.diff c2).preimage hcont
end GroundTheory.Automorphic.GodementJacquet
