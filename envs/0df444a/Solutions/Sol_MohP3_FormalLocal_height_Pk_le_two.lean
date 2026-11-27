-- Prove2me | solution 1 for MohP3.FormalLocal.height_Pk_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:43:01.524854+00:00
-- url     : https://prove2.me/submissions/6677a93b-4fb7-451c-b2b5-c4a7903e03b4

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_Pk_mem_minimalPrimes_Qk
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
open scoped Classical
namespace MohP3.FormalLocal
theorem _root_.solution : (Pk k).height ≤ 2 := by
  have hQ : Qk k = Ideal.span
      ((({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} : Finset (Sk k)) :
        Set (Sk k))) := by
    simp [Qk, Gen.Q]
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (p := Pk k)
    (s := ({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} : Finset (Sk k)))
    (by rw [← hQ]; exact Pk_mem_minimalPrimes_Qk k)
  refine h.trans ?_
  have : ({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} :
      Finset (Sk k)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  exact_mod_cast this
end MohP3.FormalLocal
