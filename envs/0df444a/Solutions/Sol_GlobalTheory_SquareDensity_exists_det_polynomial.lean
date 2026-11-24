-- Prove2me | solution 1 for GlobalTheory.SquareDensity.exists_det_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:57:20.256186+00:00
-- url     : https://prove2.me/submissions/b15a3b6c-fba6-4af9-82cf-ffdfca403387

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSqAddSubDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.SquareDensity
namespace GlobalTheory.SquareDensity
theorem _root_.solution {R K : Type*} [CommRing R] [CommRing K] (φ : R →+* K) {m : ℕ}
    (U : Matrix (Fin m) (Fin m) R) (r : ℕ) :
    ∃ Φ : MvPolynomial (Fin r) K, Φ.IsHomogeneous m ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        φ (Polynomial.aeval U F).det =
          MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ := by
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r) K) := fun j k =>
    ∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i
  have hM : ∀ j k, (M j k).IsHomogeneous 1 := fun j k =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X K i).C_mul _
  refine ⟨M.det, ?_, fun F hF => ?_⟩
  · rw [Matrix.det_apply']
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    have h1 := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => 1)
      fun i _ => hM _ _
    have h2 := h1.C_mul (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)
    simpa using h2
  · rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext j k
    rw [Polynomial.aeval_eq_sum_range' hF, ← Fin.sum_univ_eq_sum_range
      (fun i => F.coeff i • U ^ i) r]
    change φ ((∑ i : Fin r, F.coeff i • U ^ (i : ℕ)) j k) = MvPolynomial.eval _
      (∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i)
    rw [Matrix.sum_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, map_zsmul, zsmul_eq_mul, mul_comm, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
end GlobalTheory.SquareDensity
