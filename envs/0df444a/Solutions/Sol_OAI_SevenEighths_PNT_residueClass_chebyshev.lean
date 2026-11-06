-- Prove2me | solution 1 for OAI.SevenEighths.PNT.residueClass_chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:54:01.809763+00:00
-- url     : https://prove2.me/submissions/8daffb38-7bbc-49da-bfd8-c5fbd17e531d

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_Progressions
import Theorems.Thm_F_add
import Theorems.Thm_F_mul
import Theorems.Thm_F_neg
import Theorems.Thm_F_sub
import Theorems.Thm_OAI_QRH_b83dbbd_deriv_ofReal
import Theorems.Thm_cumsum_zero
import Theorems.Thm_nabla_cumsum
import Theorems.Thm_nabla_mul
import Theorems.Thm_nnabla_mul
import Theorems.Thm_toSchwartz_apply
import Theorems.Thm_vonMangoldt_cheby
attribute [local simp] F_add
attribute [local simp] F_mul
attribute [local simp] F_neg
attribute [local simp] F_sub
attribute [local simp] OAI.QRH_b83dbbd.deriv_ofReal
attribute [local simp] cumsum_zero
attribute [local simp] nabla_cumsum
attribute [local simp] nabla_mul
attribute [local simp] nnabla_mul
attribute [local simp] toSchwartz_apply



set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.PNT
open Filter ArithmeticFunction LSeries
open scoped Topology
namespace OAI.SevenEighths.PNT
theorem _root_.solution {q : ℕ} (a : ZMod q) :
    ∃ C : ℝ, ∀ N : ℕ,
      cumsum (fun n : ℕ => ‖(vonMangoldt.residueClass a n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨C, fun N => le_trans ?_ (hC N)⟩
  unfold cumsum
  apply Finset.sum_le_sum
  intro n hn
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt.residueClass_nonneg a n),
    abs_of_nonneg vonMangoldt_nonneg] using vonMangoldt.residueClass_le a n
end OAI.SevenEighths.PNT
