-- Prove2me | solution 1 for GlobalTheory.BK.mem_Fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:42.105673+00:00
-- url     : https://prove2.me/submissions/e8d20e7b-95c5-48f3-bba3-90d94f2252f2

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
theorem _root_.solution {e j : ℕ} {f : S O K e} : f ∈ Fil O K l e j ↔
    ∀ n : ℕ, ∃ g ∈ FilPre O K l e j, ∃ h : S O K e, f = g + (l : S O K e) ^ n * h := by
  simp only [Fil, Ideal.mem_iInf, Submodule.mem_sup, Ideal.mem_span_singleton']
  refine forall_congr' fun n => ⟨?_, ?_⟩
  · rintro ⟨g, hg, _, ⟨h, rfl⟩, rfl⟩
    exact ⟨g, hg, h, by ring⟩
  · rintro ⟨g, hg, h, rfl⟩
    exact ⟨g, hg, _, ⟨h, rfl⟩, by ring⟩
end GlobalTheory.BK
