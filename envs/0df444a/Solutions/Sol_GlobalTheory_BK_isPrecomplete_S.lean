-- Prove2me | solution 1 for GlobalTheory.BK.isPrecomplete_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:40:00.467403+00:00
-- url     : https://prove2.me/submissions/5ae4aab0-499f-45b0-8b2d-cb864dd9c843

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Theorems.Thm_GlobalTheory_BK_smodEq_l_pow_S_iff
import Theorems.Thm_GlobalTheory_BK_wS_pos_of_padic
import Theorems.Thm_GlobalTheory_BK_mem_S


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BK PowerSeries Filter Topology
open GlobalTheory GlobalTheory.BK
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
namespace GlobalTheory.BK
theorem _root_.solution [CompleteSpace K] :
    IsPrecomplete (Ideal.span {(l : S O K e)}) (S O K e) := by
  refine ⟨fun f hf => ?_⟩
  have hf' : ∀ {a b : ℕ}, a ≤ b → ∀ m, ‖coeff m (f a : K⟦X⟧) - coeff m (f b : K⟦X⟧)‖ * wS K e m ≤
      ‖(l : K)‖ ^ a := fun h => (smodEq_l_pow_S_iff l e _ _ _).1 (hf h)
  have hl0 := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (K := K) l)
  have hcau : ∀ m, CauchySeq fun n => coeff m (f n : K⟦X⟧) := fun m => by
    refine cauchySeq_of_le_tendsto_0' (fun n => ‖(l : K)‖ ^ n / wS K e m) (fun a b h => ?_)
      (by simpa using hl0.div_const (wS K e m))
    rw [dist_eq_norm, le_div_iff₀ (wS_pos_of_padic l e m)]
    exact hf' h m
  choose c hc using fun m => cauchySeq_tendsto_of_complete (hcau m)
  have hb : ∀ n m, ‖coeff m (f n : K⟦X⟧) - c m‖ * wS K e m ≤ ‖(l : K)‖ ^ n := fun n m =>
    le_of_tendsto ((tendsto_const_nhds.sub (hc m)).norm.mul_const _)
      ((eventually_ge_atTop n).mono fun b h => hf' h m)
  have hu : ∀ n m, ‖c m‖ * wS K e m ≤
      max (‖coeff m (f n : K⟦X⟧)‖ * wS K e m) (‖(l : K)‖ ^ n) := fun n m => by
    refine le_trans ?_ (max_le_max le_rfl (hb n m))
    rw [← max_mul_of_nonneg _ _ (wS_nonneg e m)]
    refine mul_le_mul_of_nonneg_right ?_ (wS_nonneg e m)
    have := IsUltrametricDist.norm_add_le_max (coeff m (f n : K⟦X⟧))
      (-(coeff m (f n : K⟦X⟧) - c m))
    rw [norm_neg] at this
    simpa using this
  have hmem : PowerSeries.mk c ∈ S O K e := by
    refine mem_S.2 ⟨fun m => ?_, ?_⟩
    · rw [coeff_mk]
      exact (hu 0 m).trans (max_le ((mem_S.1 (f 0).2).1 m) (by simp))
    · simp only [coeff_mk]
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun m =>
        ha.trans_le (mul_nonneg (norm_nonneg _) (wS_nonneg e m)), fun a ha => ?_⟩
      obtain ⟨n, hn⟩ := (hl0.eventually (gt_mem_nhds ha)).exists
      filter_upwards [(mem_S.1 (f n).2).2.eventually (gt_mem_nhds ha)] with m hm
      exact (hu n m).trans_lt (max_lt hm hn)
  refine ⟨⟨_, hmem⟩, fun n => (smodEq_l_pow_S_iff l e _ _ _).2 fun m => ?_⟩
  simpa using hb n m
end GlobalTheory.BK
