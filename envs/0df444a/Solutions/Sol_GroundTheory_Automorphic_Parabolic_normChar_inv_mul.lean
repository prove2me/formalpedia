-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.normChar_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:39.154215+00:00
-- url     : https://prove2.me/submissions/db6a7b65-6039-40fc-ab3c-e7bf2735905e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_normChar_mul
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_normChar_one

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
theorem _root_.solution (g : GL (Fin n) F) : normChar ω g⁻¹ * normChar ω g = 1 := by
  rw [← normChar_mul hωπ hv, inv_mul_cancel, normChar_one hωπ hv]
end GroundTheory.Automorphic.Parabolic
