-- Prove2me | solution 1 for MohP3.FormalLocal.Psurfk_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:34:23.74834+00:00
-- url     : https://prove2.me/submissions/fa4d87f7-1436-453c-a01c-24f6d38641e9

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_mem_Psurfk_iff
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : Psurfk k ≠ ⊥ := by
  have hmem : (ys k)^5 - (zs k)^4 ∈ Psurfk k := by
    rw [mem_Psurfk_iff]
    simp only [map_sub, map_pow, sigmaS_ys, sigmaS_zs]
    ring
  have hne : ((ys k)^5 - (zs k)^4 : Sk k) ≠ 0 := by
    intro h
    have h2 := congrArg (MvPowerSeries.coeff (Finsupp.single 1 5)) h
    rw [map_sub, ys, zs] at h2
    have h3 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 5)
        ((X 1 : Sk k)^5) = 1 := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_same]
    have h4 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) 5)
        ((X 2 : Sk k)^4) = 0 := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial]
      rw [if_neg]
      intro hc
      have := congrArg (fun (u : Fin 3 →₀ ℕ) => u 1) hc
      simp at this
    rw [h3, h4] at h2
    simp at h2
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hne hmem
end MohP3.FormalLocal
