-- Prove2me | solution 1 for GlobalTheory.ClassFin.HarmMin.exists_path
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:50.697206+00:00
-- url     : https://prove2.me/submissions/f3e07cc2-aa5f-4b79-8316-a4b04a159368

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SumHermitianLogGramEqZeroOfEnergyMinimum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HarmMin
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ClassFin.HarmMin
theorem _root_.solution (X : Matrix ι ι ℂ) (hX : Xᴴ = X) :
    ∃ P Q : ℝ → Matrix ι ι ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, P t * Q t = 1) ∧ (∀ t, (P t)ᴴ = P t) ∧
      (∀ t, (Q t)ᴴ = Q t) ∧ HasDerivAt P X 0 ∧ HasDerivAt Q (-X) 0 := by
  refine ⟨fun t => NormedSpace.exp (t • X), fun t => NormedSpace.exp (t • (-X)), by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [← Matrix.exp_add_of_commute]
    · simp
    · simp
  · intro t
    rw [← Matrix.exp_conjTranspose]; simp [hX]
  · intro t
    rw [← Matrix.exp_conjTranspose]; simp [hX]
  · have := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this
  · have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this
end GlobalTheory.ClassFin.HarmMin
