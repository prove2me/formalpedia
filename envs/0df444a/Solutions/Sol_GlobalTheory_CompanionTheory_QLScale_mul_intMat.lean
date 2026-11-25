-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLScale.mul_intMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:45.552365+00:00
-- url     : https://prove2.me/submissions/5e328f9e-b541-4965-9623-21fd9d849a28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinearStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLScale
open scoped ENNReal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QLScale
theorem _root_.solution {n m : ℕ} {x : Matrix (Fin n) (Fin m) F} {g : Matrix (Fin n) (Fin n) F}
    (hg : IsInt O g) (hx : x ∈ intMat O n m) : g * x ∈ intMat O n m := by
  have hx' : ∀ i j, x i j ∈ O := hx
  have hg' : ∀ i j, g i j ∈ O := hg
  show ∀ i j, (g * x) i j ∈ O
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem O fun k _ => O.mul_mem (hg' i k) (hx' k j)
end GlobalTheory.CompanionTheory.QLScale
