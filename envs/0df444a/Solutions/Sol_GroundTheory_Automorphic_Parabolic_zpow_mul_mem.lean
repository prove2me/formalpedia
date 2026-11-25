-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.zpow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:35.122148+00:00
-- url     : https://prove2.me/submissions/e991f2cc-c1d2-4e18-bdd7-cd0337b26883

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {x : F} {k : ℕ} (hx : (GLnLocal.uniformizer F : F) ^ k * x ∈ 𝒪[F]) {z : ℤ}
    (hz : (k : ℤ) ≤ z) : (GLnLocal.uniformizer F : F) ^ z * x ∈ 𝒪[F] := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, z = ((d + k : ℕ) : ℤ) := ⟨(z - k).toNat, by omega⟩
  rw [hd, zpow_natCast, pow_add, mul_assoc]
  exact mul_mem (pow_mem (GLnLocal.uniformizer F).2 d) hx
end GroundTheory.Automorphic.Parabolic
