-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.periodic_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:21.355417+00:00
-- url     : https://prove2.me/submissions/222ac9a3-6ef7-40e0-a2ed-9231a8059363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_mem_perSub_iff

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.LinChange
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) :
    ∀ x, ∀ y ∈ perSub K κ ι R, φ (x + y) = φ x := by
  intro x y hy
  obtain ⟨z, hz, rfl⟩ := (mem_perSub_iff _ _).1 hy
  exact h.2 x z hz
end GlobalTheory.SW.LinChange
