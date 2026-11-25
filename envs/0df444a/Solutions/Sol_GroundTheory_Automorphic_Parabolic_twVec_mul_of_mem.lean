-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.twVec_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:27.943194+00:00
-- url     : https://prove2.me/submissions/34659dca-933b-4ec4-8a0c-84101e08ade1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_normChar_mul

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
theorem _root_.solution {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1) (g : GL (Fin n) F) {k : GL (Fin n) F} (hk : k ∈ K) :
    twVec π ω x (g * k) = twVec π ω x g := by
  unfold twVec
  rw [map_mul, Module.End.mul_apply, hx k hk, normChar_mul hωπ hv, hK k hk, mul_one]
end GroundTheory.Automorphic.Parabolic
