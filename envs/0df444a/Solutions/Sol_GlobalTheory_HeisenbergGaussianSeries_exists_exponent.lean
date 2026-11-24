-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.exists_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:13.345987+00:00
-- url     : https://prove2.me/submissions/64fd8c90-7a73-4322-9850-628f78792ade

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries
namespace GlobalTheory.HeisenbergGaussianSeries
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) :
    ∃ M : V →L[ℝ] V →L[ℝ] ℂ, ∀ y v, M y v =
      -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)) := by
  let m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun y v => -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)))
    (by intro a b v; simp; ring) (by intro a b v; simp; ring)
    (by intro a b v; simp; ring) (by intro a b v; simp; ring)
  exact ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℂ)).toLinearMap ∘ₗ m),
    fun y v => rfl⟩
end GlobalTheory.HeisenbergGaussianSeries
