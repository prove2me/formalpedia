-- Prove2me | solution 1 for GlobalTheory.SW.HaarAlg.exists_common_level
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:44.683507+00:00
-- url     : https://prove2.me/submissions/3aefd721-0c83-4ff9-acb8-6e403cb352d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Theorems.Thm_GlobalTheory_SW_HaarAlg_hasLevel_mul

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
theorem _root_.solution {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ∃ R : ℕ, 0 < R ∧ HasLevel R φ ∧ HasLevel R ψ := by
  obtain ⟨R, hR, h1⟩ := hφ
  obtain ⟨S, hS, h2⟩ := hψ
  exact ⟨R * S, Nat.mul_pos hR hS, hasLevel_mul h1 S, mul_comm S R ▸ hasLevel_mul h2 R⟩
end GlobalTheory.SW.HaarAlg
