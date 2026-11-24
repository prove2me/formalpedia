-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.hermForm_smul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:37.170469+00:00
-- url     : https://prove2.me/submissions/c4cd65ee-a43a-4e38-8fcd-ef3073dba0a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd

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
theorem _root_.solution (c : ℝ) (S S' : Matrix (Fin r) (Fin r) ℝ)
    (τ : Matrix (Fin h) (Fin h) ℂ) (y : Fin g → ℂ) :
    (hermForm (formMatrix σ (c • S - S') τ) y y).re =
      c * (hermForm (formMatrix σ S τ) y y).re - (hermForm (formMatrix σ S' τ) y y).re := by
  have e : formMatrix σ (c • S - S') τ = c • formMatrix σ S τ - formMatrix σ S' τ := by
    ext i j
    simp [formMatrix, kron]
    ring
  rw [e, hermForm, hermForm, hermForm, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]
  simp
end GlobalTheory.TensorSiegel
