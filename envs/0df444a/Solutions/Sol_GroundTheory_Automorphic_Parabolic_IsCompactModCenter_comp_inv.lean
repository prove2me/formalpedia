-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.IsCompactModCenter.comp_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:19.713981+00:00
-- url     : https://prove2.me/submissions/1250662f-6e12-4abb-80c5-5d333b81290d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
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
open Function
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Parabolic
namespace IsCompactModCenter
theorem _root_.solution {φ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ) :
    IsCompactModCenter fun g => φ g⁻¹ := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp (show g⁻¹ ∈ support φ from hg)
  replace hzc : z * c = g⁻¹ := hzc
  refine ⟨z⁻¹, inv_mem hz, c⁻¹, by simpa using hc, ?_⟩
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  show z⁻¹ * c⁻¹ = g
  rw [← mul_inv_rev, ← hzc', hzc, inv_inv]
end IsCompactModCenter
end GroundTheory.Automorphic.Parabolic
