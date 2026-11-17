-- Prove2me | solution 1 for N25.Endgame.xH25C_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:52.265608+00:00
-- url     : https://prove2.me/submissions/619434f5-0309-4b9e-8035-809f54ee749f

import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

namespace N25.Endgame

private theorem transcendental_finite (K : Type*) [Field K] :
    Transcendental K (jBase25 K) ∧
      FiniteDimensional (IntermediateField.adjoin K ({jBase25 K} : Set (FBase K))) (FBase K) := by
  let : Γ25.FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH 25 N25.H25)
  refine ⟨?_, ?_⟩
  · exact fun h => ModularCurve.transcendental_jqModC K
      ((isAlgebraic_algHom_iff (ModularCurve.qExpFunctionFieldC K Γ25).val Subtype.val_injective).mpr h)
  · obtain ⟨x, hx, _, hfin⟩ :=
      ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
        (AlgebraicClosure K) Γ25 (ModularCurve.translation_mem_GammaH 25 N25.H25)
    let := hfin
    have hcoeff : (x : LaurentSeries (AlgebraicClosure K)) =
        ModularCurve.coeffMap (algebraMap K (AlgebraicClosure K))
          (jBase25 K : LaurentSeries K) := by
      rw [hx]
      exact (ModularCurve.coeffMap_jqModC (algebraMap K (AlgebraicClosure K))).symm
    exact (ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
      (algebraMap K (AlgebraicClosure K)) Γ25 (jBase25 K) x
      (ModularCurve.transcendental_jqModC K) hcoeff).1

theorem _root_.solution
    (K : Type*) [Field K] [PerfectField K] :
    AlgebraicCurve.IsCurveOver K (FBase K) := by
  obtain ⟨htr, hfin⟩ := transcendental_finite K
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfin

end N25.Endgame
