-- Prove2me | solution 1 for GroundTheory.ProfCoh.mk_mem_kummerGroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:37.076626+00:00
-- url     : https://prove2.me/submissions/1031a6a4-24bb-4360-a211-2eb2f839d219

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Theorems.Thm_GroundTheory_ProfCoh_unitsPow_le_unitsPowIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial
variable (K : Type*) [Field K] (n : ℕ)
variable (L : Type*) [Field L] [Algebra K L]
variable {K n L}
namespace GroundTheory.ProfCoh
theorem _root_.solution {a : Kˣ} :
    (a : UnitsModPow K n) ∈ kummerGroup K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by
  rw [← mem_unitsPowIn]
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp hba)
    have : a = b * c ^ n := by rw [hc]; group
    rw [this]
    exact mul_mem hb (unitsPow_le_unitsPowIn K n L (mem_unitsPow.mpr ⟨c, rfl⟩))
  · intro ha
    exact ⟨a, ha, rfl⟩
end GroundTheory.ProfCoh
