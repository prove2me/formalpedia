-- Prove2me | solution 1 for GroundTheory.Global.exists_units_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:26:41.752824+00:00
-- url     : https://prove2.me/submissions/2471d92d-df9d-4c34-a03b-d8f2df5f5ea9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_exists_one_add_uniformizer_pow_mul_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] hϖ
namespace GroundTheory.Global
theorem _root_.solution {j : ℕ} (hj : d + 1 ≤ j) {u : 𝒪[K]ˣ} {a : 𝒪[K]}
    (hu : (u : 𝒪[K]) - 1 = ϖ ^ j * a) :
    ∃ c : 𝒪[K], ((u ^ n : 𝒪[K]ˣ) : 𝒪[K]) = 1 + ϖ ^ (j + d) * (ε * a + ϖ * c) := by
  obtain ⟨c, hc⟩ := exists_one_add_uniformizer_pow_mul_pow_eq hnd hj a
  refine ⟨c, ?_⟩
  rw [Units.val_pow_eq_pow_val, ← hc, ← hu, add_sub_cancel]
end GroundTheory.Global
