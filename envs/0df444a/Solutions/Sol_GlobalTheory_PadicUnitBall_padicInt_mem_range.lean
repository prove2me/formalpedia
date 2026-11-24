-- Prove2me | solution 1 for GlobalTheory.PadicUnitBall.padicInt_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:47.130708+00:00
-- url     : https://prove2.me/submissions/9a3bad4c-2f6a-4b2c-971a-81d202d588a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl
import Theorems.Thm_GlobalTheory_PadicUnitBall_p_mem_maximalIdeal
import Theorems.Thm_GlobalTheory_PadicUnitBall_exists_norm_le_pow
import Theorems.Thm_GlobalTheory_PadicUnitBall_smul_top_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicUnitBall
variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}
namespace GlobalTheory.PadicUnitBall
theorem _root_.solution
    (hc : IsAdicComplete (maximalIdeal V) V)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) (z : ℤ_[p]) :
    ∃ L : V, κ (algebraMap V (FractionRing V) L) = algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]) := by
  set f : ℕ → V := fun n => ((z.appr n : ℕ) : V) with hf
  have hpm := p_mem_maximalIdeal hV
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (maximalIdeal V) ^ m • (⊤ : Submodule V V)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_top_eq]
    obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr z m n hmn
    have hmono : z.appr m ≤ z.appr n := PadicInt.appr_mono z hmn
    have heq : z.appr n = z.appr m + p ^ m * c := by
      generalize p ^ m * c = k at hc; omega
    have : f m - f n = ((p : ℕ) : V) ^ m * (-(c : V)) := by
      simp only [hf, heq]; push_cast; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm m)
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcauchy
  refine ⟨L, ?_⟩
  obtain ⟨r, hr0, hr1, hr⟩ := exists_norm_le_pow hV
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hbound : ∀ n : ℕ, ‖κ (algebraMap V (FractionRing V) L) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖
      ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
    intro n
    have h1 : f n - L ∈ maximalIdeal V ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_top_eq] at this
    have h1' := hr n _ h1
    have hfn : κ (algebraMap V (FractionRing V) (f n)) =
        algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) := by
      simp only [hf, map_natCast, PadicInt.coe_natCast]
    have h2 : ‖z - ((z.appr n : ℕ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n z)
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
    have h2' : ‖algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) -
        algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      rw [← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, PadicInt.norm_def.symm, norm_sub_rev]
      exact h2
    calc _ = ‖(κ (algebraMap V (FractionRing V) L) - κ (algebraMap V (FractionRing V) (f n))) +
          (κ (algebraMap V (FractionRing V) (f n)) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]))‖ := by
            congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
        gcongr
        · rw [norm_sub_rev, ← map_sub, ← map_sub]; exact h1'
        · rw [hfn]; exact h2'
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n + ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp))
    simpa using this
  have h0 := ge_of_tendsto' ht hbound
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
end GlobalTheory.PadicUnitBall
