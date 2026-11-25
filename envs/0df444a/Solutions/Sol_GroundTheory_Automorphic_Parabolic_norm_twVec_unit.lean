-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.norm_twVec_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:15.933975+00:00
-- url     : https://prove2.me/submissions/d6736c09-de27-4341-a8eb-f5727f08f18e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_HasCentralChar_ne_zero

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
  {ω : GL (Fin n) F → ℂ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V}
variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    ‖ω z / (‖ω z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.2 (hωπ.ne_zero hv hz))]
end GroundTheory.Automorphic.Parabolic
