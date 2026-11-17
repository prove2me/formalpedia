-- Prove2me | solution 1 for N25.Endgame.qInfinity_frobenius_fixed
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:10.473132+00:00
-- url     : https://prove2.me/submissions/eb0fd4c5-66fa-45bf-9eaf-ecdb86c0af2e

import Definitions.Def_N25_CuspReduction

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

namespace N25.Endgame

/-- Substitution of q to its prime-th power preserves the q-adic valuation ring. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (D : RedDatum25 p) :
    frobPlace25 D (ModularCurve.qInftyPlaceMod (κ D.A)
        (jBase25 (κ D.A)).property) =
      ModularCurve.qInftyPlaceMod (κ D.A) (jBase25 (κ D.A)).property := by
  let : Algebra (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25).algebra
  dsimp only [frobPlace25, jBase25]
  apply AlgebraicCurve.Place.ext
  ext f
  rw [ModularCurve.mem_qExpFrobeniusPlaceModL_iff]
  change (0 : ℤ) ≤ (ModularCurve.qSeriesBar (κ D.A) (FSpecial D.A)
      (ModularCurve.qExpFrobeniusModL (κ D.A) Γ25 p f)).order ↔
    (0 : ℤ) ≤ (ModularCurve.qSeriesBar (κ D.A) (FSpecial D.A) f).order
  change (0 : ℤ) ≤ (ModularCurve.qExpand (κ D.A) p (f : LaurentSeries (κ D.A))).order ↔
    (0 : ℤ) ≤ (f : LaurentSeries (κ D.A)).order
  by_cases hf : (f : LaurentSeries (κ D.A)) = 0
  · simp only [hf, map_zero, HahnSeries.order_zero, le_refl]
  · rw [ModularCurve.order_qExpandC (κ D.A) p hf]
    have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    exact mul_nonneg_iff_of_pos_left hp

end N25.Endgame
