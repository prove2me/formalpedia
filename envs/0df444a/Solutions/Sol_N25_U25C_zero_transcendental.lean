-- Prove2me | solution 1 for N25.U25C_zero_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:06.577867+00:00
-- url     : https://prove2.me/submissions/a1bf7f31-0627-4abe-b183-fec74883a48b

import Mathlib
import Theorems.Thm_N25_U25C_eq_mk
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_U25C_ne_zero
import Theorems.Thm_N25_unitSeries25_order
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

namespace N25

theorem _root_.solution (K : Type*) [Field K] :
    Transcendental K (U25C K 0) := by
  let F := ModularCurve.xHFunctionFieldC K 25 N25.H25
  let v := (AddValuation.toValuation (HahnSeries.addVal ℤ K)).comap
    { toFun := fun x : F => (x : LaurentSeries K)
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  have hv (x : F) : v x = Multiplicative.ofAdd (OrderDual.toDual
      ((x : LaurentSeries K).orderTop)) := rfl
  letI : v.IsTrivialOn K :=
    ⟨fun k hk => by
      rw [hv]
      change Multiplicative.ofAdd (OrderDual.toDual
        ((algebraMap K (LaurentSeries K) k).orderTop)) = 1
      rw [LaurentSeries.algebraMap_apply]
      rw [HahnSeries.C_apply, HahnSeries.orderTop_single hk]
      rfl⟩
  apply Valuation.transcendental_of_ne_one K (v := v) (U25C K 0) (U25C_ne_zero K 0)
  intro he
  have hh := congrArg (fun z => OrderDual.ofDual (Multiplicative.toAdd z)) he
  rw [U25C_eq_mk] at hh
  change (unitSeries25 K 0).orderTop = 0 at hh
  have hn : unitSeries25 K 0 ≠ 0 := by
    intro h
    apply U25C_ne_zero K 0
    exact (U25C_eq_mk K 0).trans (Subtype.ext h)
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hn, unitSeries25_order] at hh
  norm_num [unitQOrder25] at hh

end N25
