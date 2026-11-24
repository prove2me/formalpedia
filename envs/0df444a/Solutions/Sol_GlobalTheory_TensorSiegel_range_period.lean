-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.range_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:40.256329+00:00
-- url     : https://prove2.me/submissions/f4e4844e-338c-4ec9-9ee9-3b5541eacdf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_period_def

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
theorem _root_.solution (τ : Matrix (Fin h) (Fin h) ℂ) :
    (period σ τ).range = periodLattice (kron σ 1 τ) := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, _, rfl⟩
  · rintro ⟨n, n', rfl⟩
    refine ⟨fun u => Sum.elim (fun i => n (σ (u, i))) (fun i => n' (σ (u, i))), ?_⟩
    rw [period_def]
    congr 3
    · ext k; simp [coordFst]
    · ext k; simp [coordSnd]
end GlobalTheory.TensorSiegel
