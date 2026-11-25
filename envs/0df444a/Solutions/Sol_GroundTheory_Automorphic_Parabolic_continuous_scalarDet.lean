-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.continuous_scalarDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:11.367006+00:00
-- url     : https://prove2.me/submissions/6b5629c3-af42-49e6-925f-09719c7ac0b8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_scalarDet
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
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



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology ComplexConjugate
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution : Continuous (scalarDet : GL (Fin n) F → GL (Fin n) F) := by
  have hval : Continuous fun g : GL (Fin n) F =>
      ((scalarDet g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    simp only [coe_scalarDet, Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.matrix_det)
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  exact (hval.comp continuous_inv).congr fun g => by simp only [Function.comp_apply, map_inv]
end GroundTheory.Automorphic.Parabolic
