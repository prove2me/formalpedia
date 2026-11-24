-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.eq_of_period_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:06.053452+00:00
-- url     : https://prove2.me/submissions/d0e43d0f-82a5-4177-9b25-cd8220ab5dbb

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
theorem _root_.solution [Nonempty (Fin r)] {τ τ' : Matrix (Fin h) (Fin h) ℂ}
    (e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ x, period σ τ' x = e (period σ τ x)) :
    τ = τ' := by
  have hb : ∀ (t : Matrix (Fin h) (Fin h) ℂ) (u : Fin r) (i : Fin h),
      period σ t (Pi.single u (Pi.single (.inr i) 1)) = Pi.single (σ (u, i)) 1 := by
    intro t u i
    ext k
    obtain ⟨⟨v, j⟩, rfl⟩ := σ.surjective k
    rw [period_apply]
    by_cases hv : v = u
    · subst hv
      simp [Pi.single_apply, mulVec, dotProduct]
    · simp [Pi.single_apply, mulVec, dotProduct, hv]
  have h1 : (e : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun k => ?_
    obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective k
    have := he (Pi.single u (Pi.single (.inr i) 1))
    rw [hb, hb] at this
    simpa using this.symm
  obtain ⟨u⟩ := ‹Nonempty (Fin r)›
  ext i j
  have h2 := he (Pi.single u (Pi.single (.inl j) 1))
  have h3 := LinearMap.congr_fun h1 (period σ τ (Pi.single u (Pi.single (.inl j) 1)))
  have h4 := congrFun (h2.trans h3) (σ (u, i))
  rw [LinearMap.id_apply, period_apply, period_apply] at h4
  simpa [Pi.single_apply, mulVec, dotProduct] using h4.symm
end GlobalTheory.TensorSiegel
