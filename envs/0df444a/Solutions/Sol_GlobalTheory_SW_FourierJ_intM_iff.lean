-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.intM_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:11.356946+00:00
-- url     : https://prove2.me/submissions/646b0a1f-5121-4e51-8a8c-8cc03c27adbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ
noncomputable section
variable {κ ι : Type}
namespace GlobalTheory.SW.FourierJ
theorem _root_.solution [Fintype κ] [Fintype ι] (x : Matrix κ ι ℚ) : IntM x ↔ ∃ m : κ → ι → ℤ, x = zm m := by
  constructor
  · intro h
    choose m hm using fun k i => (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp (h k i)
    refine ⟨m, Matrix.ext fun k i => ?_⟩
    rw [← hm k i]
    simp [zm]
  · rintro ⟨m, rfl⟩ k i
    simpa [zm] using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℚ (m k i)))
end GlobalTheory.SW.FourierJ
