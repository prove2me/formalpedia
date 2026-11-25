-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.valuation_zpow_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:58.926362+00:00
-- url     : https://prove2.me/submissions/403b16c4-9756-4a64-9fa9-4fa335075063

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_zpow_mul_mem

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
theorem _root_.solution {x : F} {k t : ℕ} (hx : (GLnLocal.uniformizer F : F) ^ k * x ∈ 𝒪[F])
    {z : ℤ} (hz : ((k + t : ℕ) : ℤ) ≤ z) :
    valuation F ((GLnLocal.uniformizer F : F) ^ z * x) ≤ valuation F (GLnLocal.uniformizer F : F) ^ t := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ, z = t + d ∧ (k : ℤ) ≤ d := ⟨z - t, by omega, by omega⟩
  rw [hd.1, zpow_add₀ uniformizer_ne_zero, mul_assoc, map_mul, zpow_natCast, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (zpow_mul_mem hx hd.2))
end GroundTheory.Automorphic.Parabolic
