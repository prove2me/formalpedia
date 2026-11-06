-- Prove2me | solution 1 for OAI.SevenEighths.PNT.residueClass_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:54:03.636024+00:00
-- url     : https://prove2.me/submissions/f2c8c4f0-0f6d-4301-985d-99454363b1da

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
import Theorems.Thm_nterm_eq_norm_term
import Theorems.Thm_toSchwartz_apply
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
theorem _root_.solution {q : ℕ} (a : ZMod q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (vonMangoldt.residueClass a n : ℂ)) σ) := by
  have hs : LSeriesSummable (fun n => (vonMangoldt.residueClass a n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      lt_of_le_of_lt (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a) (by
        exact_mod_cast hσ)
  simpa only [← nterm_eq_norm_term] using hs.norm
end OAI.SevenEighths.PNT
