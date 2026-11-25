-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_symm_conj_transposeGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:09.107282+00:00
-- url     : https://prove2.me/submissions/c9ecb868-aa82-4619-8371-cd5953046a84

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeHomeo_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_isSymm_mul_eq_transpose_mul
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply


attribute [local simp] GroundTheory.Automorphic.ContragredientTranspose.transposeHomeo_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (x : GL (Fin n) F) :
    ∃ S : GL (Fin n) F, transposeGL S = S ∧ S * x * S⁻¹ = transposeGL x := by
  obtain ⟨S, hS, hSx⟩ := exists_isSymm_mul_eq_transpose_mul (x : Matrix (Fin n) (Fin n) F)
  refine ⟨S, Units.ext hS.eq, Units.ext ?_⟩
  simp only [Units.val_mul, coe_transposeGL]
  rw [hSx, mul_assoc, Units.mul_inv, mul_one]
end GroundTheory.Automorphic.ContragredientTranspose
