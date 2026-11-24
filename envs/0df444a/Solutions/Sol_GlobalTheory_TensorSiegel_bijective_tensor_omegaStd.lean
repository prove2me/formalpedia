-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.bijective_tensor_omegaStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:44.960324+00:00
-- url     : https://prove2.me/submissions/58cfff97-207e-40db-ab10-5fb5df511056

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
namespace GlobalTheory.TensorSiegel
theorem _root_.solution {r h : ℕ} (G : Matrix (Fin r) (Fin r) ℤ) (hG : IsUnit G.det)
    (EF : LinearMap.BilinForm ℤ (Fin r → (Fin h ⊕ Fin h → ℤ)))
    (hE : ∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v)) : Function.Bijective EF := by
  have hl : ∀ x v i, EF x (Pi.single v (Pi.single (.inl i) 1)) =
      -((fun u => x u (.inr i)) ᵥ* G) v := by
    intro x v i
    rw [hE]
    simp only [vecMul, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single v]
    · simp [omegaStd, Pi.single_apply, mul_comm]
    · intro w _ hw
      simp [omegaStd, hw]
    · simp
  have hr : ∀ x v i, EF x (Pi.single v (Pi.single (.inr i) 1)) =
      ((fun u => x u (.inl i)) ᵥ* G) v := by
    intro x v i
    rw [hE]
    simp only [vecMul, dotProduct]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single v]
    · simp [omegaStd, Pi.single_apply, mul_comm]
    · intro w _ hw
      simp [omegaStd, hw]
    · simp
  have hi : ∀ z : Fin r → ℤ, z ᵥ* G = 0 → z = 0 := fun z hz => by
    have := congrArg (· ᵥ* G⁻¹) hz
    simpa [vecMul_vecMul, mul_nonsing_inv _ hG] using this
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun φ => ?_⟩
  · ext u (i | i)
    · refine congrFun (hi (fun u => x u (.inl i)) (funext fun v => ?_)) u
      rw [← hr, hx]; rfl
    · refine congrFun (hi (fun u => x u (.inr i)) (funext fun v => ?_)) u
      have := hl x v i
      rw [hx] at this
      simpa using this.symm
  · refine ⟨fun u => Sum.elim
      (fun i => ((fun v => φ (Pi.single v (Pi.single (.inr i) 1))) ᵥ* G⁻¹) u)
      (fun i => ((fun v => -φ (Pi.single v (Pi.single (.inl i) 1))) ᵥ* G⁻¹) u), ?_⟩
    refine LinearMap.pi_ext' fun v => LinearMap.pi_ext' fun c => LinearMap.ext_ring ?_
    rcases c with i | i
    · simp [hl, vecMul_vecMul, nonsing_inv_mul _ hG]
    · simp [hr, vecMul_vecMul, nonsing_inv_mul _ hG]
end GlobalTheory.TensorSiegel
