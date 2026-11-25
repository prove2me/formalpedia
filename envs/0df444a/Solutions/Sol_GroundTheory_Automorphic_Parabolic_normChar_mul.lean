-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.normChar_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:34:13.147746+00:00
-- url     : https://prove2.me/submissions/b6b296ed-7ccd-404c-af54-20ea0cec4c91

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_scalarDet_mem_center
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_HasCentralChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology ComplexConjugate
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}
variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (x y : GL (Fin n) F) :
    normChar ω (x * y) = normChar ω x * normChar ω y := by
  unfold normChar
  rw [map_mul, hωπ.mul hv (scalarDet_mem_center x) (scalarDet_mem_center y), norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
end GroundTheory.Automorphic.Parabolic
