-- Prove2me | solution 1 for JacksonJobshop.Equilibrium.pi_series_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:56:50.093495+00:00
-- url     : https://prove2.me/submissions/a9ba2872-b718-4755-b534-a23c2b925bb2

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

theorem aux_psd_lam_nonneg {N : ℕ} (sys : JobshopSystem N) (K : ℕ) : 0 ≤ sys.lam K := by
  rcases sys.lam_assumption with h | ⟨K₀, h1, h2⟩
  · exact (h K).le
  · rcases le_or_gt K K₀ with hK | hK
    · exact (h1 K hK).le
    · exact (h2 K hK).ge

theorem aux_psd_W_nonneg {N : ℕ} (sys : JobshopSystem N) (K : ℕ) : 0 ≤ W sys K := by
  unfold W
  exact Finset.prod_nonneg (fun i _ => aux_psd_lam_nonneg sys i)

theorem aux_psd_w_nonneg {N : ℕ} (sys : JobshopSystem N) (k : Fin N → ℕ) : 0 ≤ w sys k := by
  unfold w
  refine Finset.prod_nonneg (fun n _ => Finset.prod_nonneg (fun i hi => ?_))
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  exact div_nonneg (sys.e_nonneg n) (sys.mu_pos n i (by omega)).le

theorem aux_psd_T_nonneg {N : ℕ} (sys : JobshopSystem N) (K : ℕ) : 0 ≤ T sys K := by
  unfold T
  exact Finset.sum_nonneg (fun k _ => aux_psd_w_nonneg sys k)

theorem aux_psd_term_nonneg {N : ℕ} (sys : JobshopSystem N) (K : ℕ) :
    0 ≤ W sys K * T sys K :=
  mul_nonneg (aux_psd_W_nonneg sys K) (aux_psd_T_nonneg sys K)

theorem aux_psd_term_zero {N : ℕ} (sys : JobshopSystem N) : W sys 0 * T sys 0 = 1 := by
  unfold W T w
  simp [Finset.Nat.antidiagonalTuple_zero_right]

end JacksonJobshop.Equilibrium

open JacksonJobshop.Equilibrium

theorem solution {N : ℕ} (sys : JobshopSystem N) :
    (Summable (fun K => W sys K * T sys K) → 0 < ∑' K, W sys K * T sys K) ∧
    (¬ Summable (fun K => W sys K * T sys K) →
      Filter.Tendsto (fun M => ∑ K ∈ Finset.range M, W sys K * T sys K)
        Filter.atTop Filter.atTop) := by
  refine ⟨fun hs => ?_, fun hns => ?_⟩
  · exact hs.tsum_pos (fun K => aux_psd_term_nonneg sys K) 0
      (by rw [aux_psd_term_zero]; norm_num)
  · exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun K => aux_psd_term_nonneg sys K)).mp hns
