-- Prove2me | solution 1 for MohP3.Wt.wOrd_sub_top_part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:23:34.273603+00:00
-- url     : https://prove2.me/submissions/03432ef3-96f3-428b-bfb0-c53efca4f45c

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_wt_dd
public import Theorems.Thm_MohP3_Wt_dd_self
public import Theorems.Thm_MohP3_Wt_dd_injective
public import Theorems.Thm_MohP3_Wt_mem_En
public import Theorems.Thm_MohP3_Wt_mem_En_of
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.wt_dd

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution (F : MvPowerSeries (Fin 3) k) (n : ℕ) (hF : WOrd F n) :
    WOrd (F - ∑ p ∈ En n, MvPowerSeries.monomial (dd p.1 p.2.1 p.2.2)
      (coeff (dd p.1 p.2.1 p.2.2) F)) (n + 1) := by
  classical
  intro d hd
  rw [map_sub, map_sum]
  have hcoe : ∀ p : ℕ × ℕ × ℕ,
      coeff d (MvPowerSeries.monomial (dd p.1 p.2.1 p.2.2) (coeff (dd p.1 p.2.1 p.2.2) F)) =
        if d = dd p.1 p.2.1 p.2.2 then coeff d F else 0 := by
    intro p
    rw [MvPowerSeries.coeff_monomial]
    split
    · next h => rw [h]
    · rfl
  simp only [hcoe]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
  · rw [hF d hlt]
    refine sub_eq_zero_of_eq ?_
    refine (Finset.sum_eq_zero ?_).symm
    intro p hp
    have hwp : wt (dd p.1 p.2.1 p.2.2) = n := by rw [wt_dd]; exact mem_En hp
    have : d ≠ dd p.1 p.2.1 p.2.2 := by
      intro hdp; rw [hdp, hwp] at hlt; omega
    simp [this]
  · have hp₀ : (d 0, d 1, d 2) ∈ En n := mem_En_of (by simpa [wt] using heq)
    rw [Finset.sum_eq_single (d 0, d 1, d 2)]
    · rw [dd_self]
      simp
    · intro b _ hb
      have : d ≠ dd b.1 b.2.1 b.2.2 := by
        intro hdb
        have hdb' : dd (d 0) (d 1) (d 2) = dd b.1 b.2.1 b.2.2 := by rw [dd_self, hdb]
        obtain ⟨h1, h2, h3⟩ := dd_injective hdb'
        exact hb (by rw [Prod.ext_iff, Prod.ext_iff]; exact ⟨h1.symm, h2.symm, h3.symm⟩)
      simp [this]
    · intro h; exact absurd hp₀ h
end MohP3.Wt
