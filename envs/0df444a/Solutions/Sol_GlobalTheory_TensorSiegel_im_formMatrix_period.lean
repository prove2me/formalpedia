-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.im_formMatrix_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:07.661799+00:00
-- url     : https://prove2.me/submissions/3a8cc824-94bc-448c-9594-c82aea6453a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_im_realForm_period
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_mul
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_transpose
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_mulVec_one
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_one_map_im
import Theorems.Thm_GlobalTheory_TensorSiegel_kron_one_map_re
import Theorems.Thm_GlobalTheory_TensorSiegel_period_def
import Theorems.Thm_GlobalTheory_ofIntVec_eq_ofRealVec


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
theorem _root_.solution (G : Matrix (Fin r) (Fin r) ℤ) {τ : Matrix (Fin h) (Fin h) ℂ}
    (hs : τ.IsSymm) (hτ : (τ.map Complex.im).PosDef) (x y : Fin r → (Fin h ⊕ Fin h → ℤ)) :
    (hermForm (formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ) (period σ τ x) (period σ τ y)).im =
      ((∑ u, ∑ v, G u v * omegaStd (x u) (y v) : ℤ) : ℝ) := by
  have hu : IsUnit (τ.map Complex.im).det := (isUnit_iff_isUnit_det _).1 hτ.isUnit
  have hY : (τ.map Complex.im)ᵀ = τ.map Complex.im := hs.map _
  have hX : (τ.map Complex.re)ᵀ = τ.map Complex.re := hs.map _
  rw [hermForm, formMatrix, period_def, period_def]
  simp only [ofIntVec_eq_ofRealVec]
  rw [im_realForm_period _ _ (kron σ (G.map (Int.cast : ℤ → ℝ)) 1)]
  · simp only [dotProduct]
    rw [← σ.sum_comp, ← σ.sum_comp]
    simp only [Fintype.sum_prod_type, kron_mulVec_one, coordFst, coordSnd, Equiv.symm_apply_apply,
      omegaStd, map_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  · rw [kron_one_map_im, kron_transpose, kron_mul, hY, mul_nonsing_inv _ hu, transpose_one,
      Matrix.one_mul]
  · rw [kron_one_map_im, kron_mul, nonsing_inv_mul _ hu, Matrix.mul_one]
  · rw [kron_one_map_re, kron_transpose, kron_mul, kron_mul, hX]
    simp
end GlobalTheory.TensorSiegel
