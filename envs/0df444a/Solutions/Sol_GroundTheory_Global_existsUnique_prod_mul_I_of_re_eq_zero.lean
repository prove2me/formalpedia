-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_prod_mul_I_of_re_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:24.250825+00:00
-- url     : https://prove2.me/submissions/a7b50e6e-4e13-48be-be3e-13c1d1888a6d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_circleToUnits



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution {α : Type*} {P : α × ℂ → Prop}
    (h : ∃! p, P p) (hre : ∀ p, P p → p.2.re = 0) :
    ∃! q : α × ℝ, P (q.1, (q.2 : ℂ) * I) := by
  obtain ⟨p, hp, hu⟩ := h
  have hp' : p = (p.1, (p.2.im : ℂ) * I) := by
    refine Prod.ext rfl ?_
    apply Complex.ext <;> simp [hre p hp]
  refine ⟨(p.1, p.2.im), by show P (p.1, (p.2.im : ℂ) * I); rw [← hp']; exact hp,
    fun q hq => ?_⟩
  have := hu _ hq
  refine Prod.ext ?_ ?_
  · simpa using congrArg Prod.fst this
  · simpa using congrArg (fun r : α × ℂ => r.2.im) this
end GroundTheory.Global
