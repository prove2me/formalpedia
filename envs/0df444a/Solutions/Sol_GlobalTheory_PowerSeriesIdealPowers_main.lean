-- Prove2me | solution 1 for GlobalTheory.PowerSeriesIdealPowers.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:22.239424+00:00
-- url     : https://prove2.me/submissions/42766a90-be9b-49b4-9215-d8473f2a60d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem
import Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_mem_smul_top_iff
import Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_coeff_mem_of_mem_pow
import Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_mem_pow_of_coeff_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesIdealPowers
open MvPowerSeries IsLocalRing
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.PowerSeriesIdealPowers
theorem _root_.solution : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    [IsPrecomplete (IsLocalRing.maximalIdeal O) O] (a : ℕ),
    IsPrecomplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) := by
  intro O _ _ hO a
  constructor
  intro f hf
  simp only [SModEq.sub_mem, mem_smul_top_iff] at hf ⊢
  let s : (Fin a →₀ ℕ) → ℕ → O := fun d k => coeff d (f (k + d.degree))
  have hs : ∀ d, ∃ L : O, ∀ k, s d k ≡ L [SMOD ((maximalIdeal O) ^ k • ⊤ : Submodule O O)] := by
    intro d
    refine IsPrecomplete.prec hO ?_
    intro k l hkl
    rw [SModEq.sub_mem, mem_smul_top_iff]
    have h := coeff_mem_of_mem_pow (k + d.degree) _ (hf (Nat.add_le_add_right hkl _)) d
    rwa [map_sub, Nat.add_sub_cancel] at h
  choose L hL using hs
  let Lim : MvPowerSeries (Fin a) O := fun d => L d
  have hLim : ∀ d, coeff d Lim = L d := fun d => rfl
  refine ⟨Lim, fun n => mem_pow_of_coeff_mem a n _ fun d => ?_⟩
  rw [map_sub, hLim]
  by_cases hd : d.degree ≤ n
  · have h := hL d (n - d.degree)
    rw [SModEq.sub_mem, mem_smul_top_iff] at h
    simp only [s, Nat.sub_add_cancel hd] at h
    exact h
  · rw [show n - d.degree = 0 by omega]; simp
end GlobalTheory.PowerSeriesIdealPowers
