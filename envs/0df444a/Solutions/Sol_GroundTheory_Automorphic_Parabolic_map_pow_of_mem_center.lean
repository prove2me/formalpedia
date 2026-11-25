-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.map_pow_of_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:13:13.018169+00:00
-- url     : https://prove2.me/submissions/b5112653-2d3c-47de-9430-2533401be923

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_HasCentralChar_mul
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_HasCentralChar_one


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
theorem _root_.solution {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (m : ℕ) : ω (z ^ m) = ω z ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, hωπ.one hv]
  | succ m ih => rw [pow_succ, hωπ.mul hv (pow_mem hz m) hz, ih, pow_succ]
end GroundTheory.Automorphic.Parabolic
