-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.hermForm_endo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:36.419806+00:00
-- url     : https://prove2.me/submissions/630b09b9-675e-4131-9a19-18e7185d27e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_mul
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
open GlobalTheory GlobalTheory.TensorSiegel
variable {r h g : ℕ} (σ : Fin r × Fin h ≃ Fin g) {R : Type*} [CommRing R]
namespace GlobalTheory.TensorSiegel
theorem _root_.solution (a : Matrix (Fin r) (Fin r) ℤ) (S : Matrix (Fin r) (Fin r) ℝ)
    (τ : Matrix (Fin h) (Fin h) ℂ) (y : Fin g → ℂ) :
    (hermForm (formMatrix σ S τ) (endo σ a y) (endo σ a y)) =
      hermForm (formMatrix σ ((a.map (Int.cast : ℤ → ℝ))ᵀ * S * a.map (Int.cast : ℤ → ℝ)) τ) y y := by
  have e : ∀ A : Matrix (Fin g) (Fin g) ℝ,
      star (A.map Complex.ofReal *ᵥ y) = A.map Complex.ofReal *ᵥ star y := by
    intro A
    ext i
    simp [mulVec, dotProduct]
  have e2 : ∀ A B : Matrix (Fin g) (Fin g) ℝ,
      A.map Complex.ofReal * B.map Complex.ofReal = (A * B).map Complex.ofReal := fun A B =>
    (Matrix.map_mul (f := Complex.ofRealHom)).symm
  rw [hermForm, hermForm, endo, mulVecLin_apply, e, ← vecMul_transpose, ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec, ← transpose_map, formMatrix, formMatrix, e2, e2, kron_transpose,
    kron_mul, kron_mul]
  simp
end GlobalTheory.TensorSiegel
