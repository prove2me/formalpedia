-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.endo_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:05.393563+00:00
-- url     : https://prove2.me/submissions/0f9070ca-8faa-4046-a8f9-7337a25023a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_mulVec_one
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
theorem _root_.solution (a : Matrix (Fin r) (Fin r) ℤ) (τ : Matrix (Fin h) (Fin h) ℂ)
    (x : Fin r → (Fin h ⊕ Fin h → ℤ)) :
    endo σ a (period σ τ x) = period σ τ (fun u => ∑ v, a u v • x v) := by
  have e : (kron σ (a.map (Int.cast : ℤ → ℝ)) 1).map Complex.ofReal =
      kron σ (a.map (Int.cast : ℤ → ℂ)) 1 := by
    ext i j
    by_cases hij : (σ.symm i).2 = (σ.symm j).2 <;> simp [kron, one_apply, hij]
  ext k
  obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective k
  rw [endo, mulVecLin_apply, e, kron_mulVec_one]
  simp only [period_apply, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  push_cast
  simp only [Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
  ring
end GlobalTheory.TensorSiegel
