-- Prove2me | solution 1 for GlobalTheory.PadicVal.summable_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:03:15.261141+00:00
-- url     : https://prove2.me/submissions/ff031476-152e-492f-a47c-6dd6c72f59cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PadicVal
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.PadicVal
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {I : Type} {x : I → PadicAlgCl p} (hK : ∀ i, x i ∈ K) (hx : Filter.Tendsto x Filter.cofinite (nhds 0)) :
    Summable x := by
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  let y : I → K := fun i => ⟨x i, hK i⟩
  have hy : Filter.Tendsto y Filter.cofinite (nhds 0) := by
    rw [tendsto_subtype_rng]
    exact hx
  have hs : Summable y := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hy
  exact hs.map K.val continuous_subtype_val
end GlobalTheory.PadicVal
