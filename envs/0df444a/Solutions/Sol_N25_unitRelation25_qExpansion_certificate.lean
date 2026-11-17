-- Prove2me | solution 1 for N25.unitRelation25_qExpansion_certificate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:22.743877+00:00
-- url     : https://prove2.me/submissions/73aa0ecd-e21b-4536-b17a-03717f7daee7

import Mathlib
import Theorems.Thm_N25_U25C_eq_mk
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitRelationClearedSeries25_eq_zero
import Definitions.Def_N25_UnitRelation
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_UnitSeries
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Theorems.Thm_ModularForm_sturm_bound_of_isArithmetic
import Theorems.Thm_N25_clearedUnitRelation25_identity
import Theorems.Thm_N25_unitSeries25_normalization

set_option autoImplicit false

namespace N25

/-- The same integral relation holds on the literal modular-unit carrier over
every field, by mapping the zero integral series to its Laurent series. -/
theorem _root_.solution (K : Type*) [Field K] :
    planeRelation (U25C K 0) (U25C K 0 / U25C K 1) = 0 := by
  rw [U25C_eq_mk K 0, U25C_eq_mk K 1]
  let g := ModularCurve.intSeriesC K unitDenominatorSeries25
  let f₀ := ModularCurve.intSeriesC K (unitNumeratorSeries25 0)
  let f₁ := ModularCurve.intSeriesC K (unitNumeratorSeries25 1)
  have hg : g ≠ 0 := (unitSeries25_normalization K).1
  have hf₁ : f₁ ≠ 0 := by
    intro h
    have hc := ((unitSeries25_normalization K).2 1).2
    have h' : ModularCurve.intSeriesC K (unitNumeratorSeries25 1) = 0 := h
    simp [unitSeries25, h'] at hc
  have hclear : clearedUnitRelation25 g f₀ f₁ = 0 := by
    have h := congrArg (ModularCurve.intSeriesC K) unitRelationClearedSeries25_eq_zero
    simpa only [g, f₀, f₁, unitRelationClearedSeries25, clearedUnitRelation25, ModularCurve.intSeriesC,
      map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero] using h
  rw [clearedUnitRelation25_identity g f₀ f₁ hg hf₁] at hclear
  have hrel : planeRelation (f₀/g) (f₀/f₁) = 0 :=
    (mul_eq_zero.mp hclear).resolve_left (mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hf₁))
  have hratio : (f₀/g)/(f₁/g) = f₀/f₁ := by
    field_simp [hg, hf₁]
  apply Subtype.ext
  change planeRelation (f₀/g) ((f₀/g)/(f₁/g)) = 0
  rw [hratio]
  exact hrel

end N25
