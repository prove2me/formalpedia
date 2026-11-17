-- Prove2me | solution 1 for N25.Endgame.rational_algebraic_constants25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:00.024592+00:00
-- url     : https://prove2.me/submissions/2ff604a5-48b6-4f45-a480-7623728bde8e

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

namespace N25.Endgame

/-- Algebraic constants in the literal rational Laurent field are rational. -/
theorem _root_.solution (y : FQ) (hy : IsAlgebraic ℚ y) :
    y ∈ (algebraMap ℚ FQ).range := by
  let c : ℚ := (y : LaurentSeries ℚ).coeff 0
  let z : FQ := y - algebraMap ℚ FQ c
  have hza : IsAlgebraic ℚ z := hy.sub (isIntegral_algebraMap.isAlgebraic)
  have ho : (z : LaurentSeries ℚ).order = 0 := by
    have h := (qInftyPlaceRat FQ cuspChoice25.hQ).ord_eq_zero_of_isAlgebraic hza
    have hb : (qInftyPlaceRat FQ cuspChoice25.hQ).ord z =
        (qSeriesBar ℚ FQ z).order := ord_qInftyPlaceBar ℚ cuspChoice25.hQ z
    exact hb.symm.trans h
  have hz : z = 0 := by
    by_contra hn
    have hn' : (z : LaurentSeries ℚ) ≠ 0 := fun h => hn (Subtype.ext h)
    have hc := HahnSeries.coeff_order_eq_zero.not.mpr hn'
    rw [ho] at hc
    apply hc
    have hC : ((algebraMap ℚ FQ c : FQ) : LaurentSeries ℚ) =
        algebraMap ℚ (LaurentSeries ℚ) c :=
      RingHom.congr_fun (RingHom.ext_rat
        (FQ.toSubfield.subtype.comp (algebraMap ℚ FQ))
        (algebraMap ℚ (LaurentSeries ℚ))) c
    change ((y : LaurentSeries ℚ) - ((algebraMap ℚ FQ c : FQ) : LaurentSeries ℚ)).coeff 0 = 0
    rw [hC]
    rw [HahnSeries.coeff_sub, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_same]
    exact sub_self _
  exact ⟨c, (sub_eq_zero.mp hz).symm⟩

end N25.Endgame
