-- Prove2me | solution 1 for OAI.SevenEighths.PNT.residueClass_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:50.708485+00:00
-- url     : https://prove2.me/submissions/13c2bbcd-47cc-43fa-bc7d-bc25a9bf2394

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_Progressions
import Theorems.Thm_OAI_SevenEighths_PNT_residueClass_chebyshev
import Theorems.Thm_OAI_SevenEighths_PNT_residueClass_summable
import Theorems.Thm_F_add
import Theorems.Thm_F_mul
import Theorems.Thm_F_neg
import Theorems.Thm_F_sub
import Theorems.Thm_OAI_QRH_b83dbbd_deriv_ofReal
import Theorems.Thm_P2M_WienerIkeharaTheorem__892159d4c3be
import Theorems.Thm_cumsum_zero
import Theorems.Thm_nabla_cumsum
import Theorems.Thm_nabla_mul
import Theorems.Thm_nnabla_mul
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
theorem _root_.solution {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ => cumsum (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (vonMangoldt.residueClass_nonneg a)
    (fun σ hσ => residueClass_summable a hσ)
    (residueClass_chebyshev a)
    (vonMangoldt.continuousOn_LFunctionResidueClassAux a)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
    vonMangoldt.eqOn_LFunctionResidueClassAux ha
end OAI.SevenEighths.PNT
