-- Prove2me | solution 1 for GlobalTheory.CubeLift.avg_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:52.98668+00:00
-- url     : https://prove2.me/submissions/e91f1710-854d-45ae-b5b0-717fb00d21e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_coeff_avg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
open Classical
namespace GlobalTheory.CubeLift
theorem _root_.solution (p : X × Y) (r : A) : avg (single p r) = if p.1 = 0 then single p.2 r else 0 := by
  obtain ⟨a, b⟩ := p
  ext y
  rw [coeff_avg]
  by_cases h : a = 0 <;> simp [h, Finsupp.single_apply]
end GlobalTheory.CubeLift
