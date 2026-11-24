-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.period_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:41:20.825808+00:00
-- url     : https://prove2.me/submissions/e9218bce-3376-469d-99a1-a46e49d5e287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_one_mulVec
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
theorem _root_.solution (τ : Matrix (Fin h) (Fin h) ℂ) (x : Fin r → (Fin h ⊕ Fin h → ℤ))
    (u : Fin r) (i : Fin h) :
    period σ τ x (σ (u, i)) = τ.mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ) := by
  rw [period_def, Pi.add_apply, kron_one_mulVec]
  simp [ofIntVec, coordFst, coordSnd, mulVec, dotProduct]
end GlobalTheory.TensorSiegel
