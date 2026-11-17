-- Prove2me | solution 1 for N25.unitRelationClearedSeries25_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:13.53104+00:00
-- url     : https://prove2.me/submissions/e1982c74-d577-4478-ae55-2233a1898541

import Mathlib
import Theorems.Thm_N25_unitRelation25_sturm_realization
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_N25_unitRelation25_sturm_coefficients
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_GammaH25GL_isArithmetic
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Theorems.Thm_N25_GammaH25GL_relIndex
import Theorems.Thm_N25_GammaH25GL_period_one
import Theorems.Thm_ModularForm_sturm_bound_of_isArithmetic

set_option autoImplicit false

open UpperHalfPlane

open scoped MatrixGroups

namespace N25

/-- The finite coefficient certificate forces the full integral series to
vanish by the arithmetic Sturm bound. -/
theorem _root_.solution : unitRelationClearedSeries25 = 0 := by
  let : GammaH25GL.IsArithmetic := GammaH25GL_isArithmetic
  obtain ⟨H, hH, _⟩ := unitRelation25_sturm_realization
  have horder : (4951 : ℕ∞) ≤ (qExpansion 1 H).order := by
    apply PowerSeries.nat_le_order
    intro n hn
    rw [← hH, PowerSeries.coeff_map, unitRelation25_sturm_coefficients ⟨n, hn⟩, map_zero]
  have hbound : (↑(((396 : ℤ) * GammaH25GL.relIndex 𝒮ℒ).toNat / 12) : ℕ∞) <
      (qExpansion 1 H).order := by
    rw [GammaH25GL_relIndex]
    change (4950 : ℕ∞) < (qExpansion 1 H).order
    exact lt_of_lt_of_le (by exact_mod_cast (show 4950 < 4951 by decide)) horder
  have hHzero : H = 0 := ModularForm.sturm_bound_of_isArithmetic GammaH25GL_period_one hbound
  apply PowerSeries.ext
  intro n
  have hc := hH.coeff n
  rw [hHzero] at hc
  have hc' : ((PowerSeries.coeff n unitRelationClearedSeries25 : ℤ) : ℂ) = 0 := by
    simpa only [FunLike.coe_zero, qExpansion_zero, map_zero] using hc
  rw [map_zero]
  exact_mod_cast hc'

end N25
