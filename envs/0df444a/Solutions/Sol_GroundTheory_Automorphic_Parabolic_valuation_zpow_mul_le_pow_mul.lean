-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.valuation_zpow_mul_le_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:21:28.860042+00:00
-- url     : https://prove2.me/submissions/5594cb3c-2cf5-4153-baa6-8d38f15bc3d4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero


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
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {x : F} {e : ℕ} {z : ℤ} (hz : (e : ℤ) ≤ z) :
    valuation F (ϖ ^ z * x) ≤ valuation F ϖ ^ e * valuation F x := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, z = e + d := ⟨(z - e).toNat, by omega⟩
  rw [zpow_add₀ uniformizer_ne_zero, zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow,
    map_pow, mul_right_comm]
  exact mul_le_of_le_one_right' (pow_le_one' (valuation_uniformizer_lt_one F).le d)
end GroundTheory.Automorphic.Parabolic
