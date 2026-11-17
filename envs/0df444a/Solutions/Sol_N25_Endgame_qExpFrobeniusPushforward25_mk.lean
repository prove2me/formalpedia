-- Prove2me | solution 1 for N25.Endgame.qExpFrobeniusPushforward25_mk
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:09.656947+00:00
-- url     : https://prove2.me/submissions/072e546e-a1dd-423f-a200-3657e7b404d0

import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental

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
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (D : AlgebraicCurve.Divisor.degZero (K := K) (F := FBase K)) :
    ModularCurve.qExpFrobeniusPushforwardModL K Γ25 ℓ
        (AlgebraicCurve.Pic0.mk D) =
      AlgebraicCurve.Pic0.mk
        (ModularCurve.qExpFrobeniusDegZeroPushforwardModL K Γ25 ℓ D) := by
  obtain ⟨⟨hP, hfin, hFI, hN⟩, _⟩ :=
    ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental K Γ25
      ⟨jBase25 K, (transcendental_finite K).1, (transcendental_finite K).2⟩
  let := hP
  exact ModularCurve.qExpFrobeniusPushforwardModL_mk hfin hFI hN D

end N25.Endgame
