-- Prove2me | solution 1 for GroundTheory.Global.range_powMonoidHom_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:55.37683+00:00
-- url     : https://prove2.me/submissions/c32b36b9-2b76-45a4-9ea5-46ec247da1cd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex

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
variable {n : ℕ}
omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.Global
theorem _root_.solution {G H : Type*} [CommGroup G] [CommGroup H] (n : ℕ) :
    (powMonoidHom n : G × H →* G × H).range =
      (powMonoidHom n : G →* G).range.prod (powMonoidHom n : H →* H).range := by
  ext ⟨a, b⟩
  rw [Subgroup.mem_prod, MonoidHom.mem_range, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨x, y⟩, h⟩
    rw [powMonoidHom_apply, Prod.pow_mk, Prod.mk.injEq] at h
    exact ⟨⟨x, h.1⟩, ⟨y, h.2⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨(x, y), ?_⟩
    rw [powMonoidHom_apply] at hx hy ⊢
    rw [Prod.pow_mk, hx, hy]
end GroundTheory.Global
