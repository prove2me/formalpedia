-- Prove2me | solution 1 for GlobalTheory.ConjSize.sz_apow_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:43:36.425116+00:00
-- url     : https://prove2.me/submissions/e2a36ea7-baca-4e50-84b9-27364c0f5f82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_LGrp_nabs_eq_zpow
import Theorems.Thm_GlobalTheory_SplitFlip_apow_add
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos


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
theorem _root_.solution (u : kˣ) (h : apow u (1 / 2) ∈ Set.range ι) : Sz ι τ (apow u (1 / 2)) (Real.sqrt (nabs k u)) := by
  haveI : CharZero K := ι.charZero
  obtain ⟨y, hy⟩ := h
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = nabs k u := ⟨(resCard k : ℚ) ^ (-SmGL.ord k u), by
    rw [GlobalTheory.LGrp.nabs_eq_zpow]; push_cast; rfl⟩
  have h2 : apow u (1 / 2) ^ 2 = (r : ℂ) := by
    rw [sq, ← apow_add, apow, ← hr]; norm_num
  have h3 : y ^ 2 = (r : K) := ι.injective (by rw [map_pow, hy, h2, map_ratCast])
  refine ⟨y, hy, Real.le_sqrt_of_sq_le ?_⟩
  rw [← norm_pow, ← map_pow, h3, map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, hr,
    Real.norm_of_nonneg (GlobalTheory.SplitWeil.Model.nabs_pos u).le]
end GlobalTheory.ConjSize
