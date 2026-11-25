-- Prove2me | solution 1 for GlobalTheory.BK.frob_mem_invL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:17.362381+00:00
-- url     : https://prove2.me/submissions/60931133-f7b1-4c99-8f66-b4a0b8eec341

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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] {B : Subalgebra O K⟦X⟧}
    (hB : ∀ f ∈ B, frob K l f ∈ B) {f : K⟦X⟧} (hf : f ∈ invL l B) : frob K l f ∈ invL l B := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by simpa using hB _ hn⟩
end GlobalTheory.BK
