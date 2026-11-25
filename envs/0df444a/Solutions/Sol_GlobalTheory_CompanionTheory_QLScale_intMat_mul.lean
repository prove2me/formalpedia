-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLScale.intMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:16:54.430176+00:00
-- url     : https://prove2.me/submissions/0390ac2e-d4f2-485d-afb4-7734c46ae83d

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
theorem _root_.solution {n m : ℕ} {x : Matrix (Fin n) (Fin m) F} {g : Matrix (Fin m) (Fin m) F}
    (hx : x ∈ intMat O n m) (hg : IsInt O g) : x * g ∈ intMat O n m := by
  have hx' : ∀ i j, x i j ∈ O := hx
  have hg' : ∀ i j, g i j ∈ O := hg
  show ∀ i j, (x * g) i j ∈ O
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem O fun k _ => O.mul_mem (hx' i k) (hg' k j)
end GlobalTheory.CompanionTheory.QLScale
