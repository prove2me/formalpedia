-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.eq_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:06.837448+00:00
-- url     : https://prove2.me/submissions/64e4a57d-f1a6-4a4a-85a4-3b2d3ba06d29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_period_apply

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
theorem _root_.solution {τ : Matrix (Fin h) (Fin h) ℂ}
    {Q : (Fin r → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)}
    (hQ : ∀ x u i, Q x (σ (u, i)) =
      τ.mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) : Q = period σ τ := by
  refine AddMonoidHom.ext fun x => funext fun k => ?_
  obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective k
  rw [hQ, period_apply]
end GlobalTheory.TensorSiegel
