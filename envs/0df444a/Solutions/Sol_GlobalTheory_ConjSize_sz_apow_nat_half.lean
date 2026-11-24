-- Prove2me | solution 1 for GlobalTheory.ConjSize.sz_apow_nat_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:13:25.053669+00:00
-- url     : https://prove2.me/submissions/2ff7d12a-dab7-473f-80c1-0390b55f8384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_ConjSize_Sz_mono
import Theorems.Thm_GlobalTheory_ConjSize_Sz_pow
import Theorems.Thm_GlobalTheory_ConjSize_sz_apow_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open GlobalTheory GlobalTheory.ConjSize
variable {K : Type} [Field K] (ι τ : K →+* ℂ)
variable {ι τ}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.ConjSize
theorem _root_.solution (u : kˣ) (h : apow u (1 / 2) ∈ Set.range ι) (n : ℕ) {c : ℝ} (hc : 1 ≤ c) (hu : nabs k u ≤ c) :
    Sz ι τ (apow u ((n : ℂ) / 2)) (c ^ n) := by
  have : apow u ((n : ℂ) / 2) = apow u (1 / 2) ^ n := by
    rw [apow, apow, ← Complex.cpow_nat_mul]; congr 1; ring
  rw [this]
  refine ((sz_apow_half u h).mono ?_).pow n
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith
end GlobalTheory.ConjSize
