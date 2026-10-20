-- Prove2me | solution 1 for OAI.Cotype.QuadraticTypeBound.one_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:53:09.326862+00:00
-- url     : https://prove2.me/submissions/a155f617-3861-4cad-97d6-fa09e96b8385

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]


theorem solution [Nontrivial X] {n : ℕ} (hn : 0 < n)
    {A : ℝ} (h : QuadraticTypeBound X n A) : 1 ≤ A := by
  obtain ⟨x0, hx0⟩ := exists_ne (0 : X)
  let i0 : Fin n := ⟨0, hn⟩
  have hx := h (fun i => if i = i0 then x0 else 0)
  have hrad : ∀ ε, ‖rademacherSum X (fun i => if i = i0 then x0 else 0) ε‖ = ‖x0‖ := by
    intro ε
    simp only [rademacherSum, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [norm_smul]
    unfold sign; split_ifs <;> simp
  have hl : cubeL2 X (rademacherSum X (fun i => if i = i0 then x0 else 0)) ^ 2 = ‖x0‖ ^ 2 := by
    rw [cubeL2_sq]
    simp only [hrad, average, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hr : ∑ i, ‖(if i = i0 then x0 else 0 : X)‖ ^ 2 = ‖x0‖ ^ 2 := by
    simp [apply_ite]
  rw [hl, hr] at hx
  have hp : 0 < ‖x0‖ ^ 2 := by positivity
  nlinarith

