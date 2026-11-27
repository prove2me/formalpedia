-- Prove2me | solution 1 for MohP3.FormalLocal.arithRank_Pk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:03.311379+00:00
-- url     : https://prove2.me/submissions/c3a49c17-cdaa-4554-a493-a1ec619f156c

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_Pk_isPrime
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_Pk
public import Theorems.Thm_MohP3_FormalLocal_chiS_X0
public import Theorems.Thm_MohP3_FormalLocal_chiS_X1
public import Theorems.Thm_MohP3_FormalLocal_height_Pk
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
public import Theorems.Thm_MohP3_arithRank_le
public import Theorems.Thm_MohP3_height_le_arithRank
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd


attribute [local simp] MohP3.FormalLocal.chiS_X0
attribute [local simp] MohP3.FormalLocal.chiS_X1

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
open scoped Classical
namespace MohP3.FormalLocal
theorem _root_.solution : arithRank (Pk k) = 2 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (arithRank_le
      ({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} : Finset (Sk k)) ?_) ?_
    · have hQ : Ideal.span
          ((({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} : Finset (Sk k)) :
            Set (Sk k))) = Qk k := by
        simp [Qk, Gen.Q]
      rw [hQ, radical_Qk_eq_Pk, (Pk_isPrime k).radical]
    · have : ({Gen.H1 (xs k) (ys k) (zs k), Gen.H2 (xs k) (ys k) (zs k)} :
          Finset (Sk k)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact_mod_cast this
  · calc (2 : ℕ∞) = (Pk k).height := (height_Pk k).symm
      _ ≤ arithRank (Pk k) := height_le_arithRank (Pk k) (Pk_isPrime k)
end MohP3.FormalLocal
