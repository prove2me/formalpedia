-- Prove2me | solution 1 for GlobalTheory.BK.Fil_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:19.093956+00:00
-- url     : https://prove2.me/submissions/ecbfbb4f-9759-4502-9580-d30b6f87bd3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
namespace GlobalTheory.BK
theorem _root_.solution (e : ℕ) {i j : ℕ} (h : i ≤ j) : Fil O K l e j ≤ Fil O K l e i :=
  iInf_mono fun _ => sup_le_sup_right
    (Ideal.span_mono (by rintro x ⟨k, hk, hx⟩; exact ⟨k, h.trans hk, hx⟩)) _
end GlobalTheory.BK
