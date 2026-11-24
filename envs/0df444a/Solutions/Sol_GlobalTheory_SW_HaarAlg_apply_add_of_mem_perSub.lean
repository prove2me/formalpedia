-- Prove2me | solution 1 for GlobalTheory.SW.HaarAlg.apply_add_of_mem_perSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:08.638916+00:00
-- url     : https://prove2.me/submissions/5e2c0f56-77dd-4236-861d-b20e74f3ee25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarAlg
variable {K : Type} [Field K] {κ ι : Type}
namespace GlobalTheory.SW.HaarAlg
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ)
    {p : Matrix κ ι K} (hp : p ∈ perSub K κ ι R) : ∀ x, φ (x + p) = φ x := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact fun x => h.2 x y hy
  | zero => simp
  | add p q _ _ hp hq => intro x; rw [← add_assoc, hq, hp]
  | neg p _ hp => intro x; rw [← hp (x + -p)]; simp
end GlobalTheory.SW.HaarAlg
