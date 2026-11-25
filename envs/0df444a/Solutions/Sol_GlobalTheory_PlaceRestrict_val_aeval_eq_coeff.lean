-- Prove2me | solution 1 for GlobalTheory.PlaceRestrict.val_aeval_eq_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:06:42.569985+00:00
-- url     : https://prove2.me/submissions/1e26878a-19b6-4b09-93b4-354ffe8966fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_val_eval_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PlaceRestrict
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace GlobalTheory.PlaceRestrict
theorem _root_.solution {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (P : MvPolynomial σ Ω) (α : σ →₀ ℕ) (hα : α ∈ P.support)
    (hmin : ∀ β ∈ P.support, w (algebraMap Ω U (P.coeff α)) ≤ w (algebraMap Ω U (P.coeff β))) :
    w (MvPolynomial.aeval t P) = w (algebraMap Ω U (P.coeff α)) := by
  classical
  have hc : P.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  have key := val_eval_eq_zero w t ht hind (MvPolynomial.C (P.coeff α)⁻¹ * P) ?_ α ?_
  · have : MvPolynomial.aeval t P =
        algebraMap Ω U (P.coeff α) * MvPolynomial.aeval t (MvPolynomial.C (P.coeff α)⁻¹ * P) := by
      rw [map_mul, MvPolynomial.aeval_C, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
    rw [this, AddValuation.map_mul, key, add_zero]
  · intro β
    rw [MvPolynomial.coeff_C_mul, map_mul, AddValuation.map_mul]
    by_cases hβ : β ∈ P.support
    · have h3 := hmin β hβ
      calc (0 : WithTop ℤ) = w (algebraMap Ω U (P.coeff α)⁻¹) + w (algebraMap Ω U (P.coeff α)) := by
            rw [← AddValuation.map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, AddValuation.map_one]
        _ ≤ _ := add_le_add le_rfl h3
    · rw [MvPolynomial.notMem_support_iff.mp hβ, map_zero, AddValuation.map_zero]
      simp
  · rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc]
end GlobalTheory.PlaceRestrict
