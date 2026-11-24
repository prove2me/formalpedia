-- Prove2me | solution 1 for GlobalTheory.AffinePoints.hasDerivAt_aevalTower_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:36.828137+00:00
-- url     : https://prove2.me/submissions/17254e19-ae41-4582-a6a4-24cd06bedd77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
namespace GlobalTheory.AffinePoints
theorem _root_.solution {R ι : Type*} [CommRing R] [Algebra 𝕜 R] [Fintype ι]
    (φ : R →ₐ[𝕜] 𝕜) (q : MvPolynomial ι R) (y v : ι → 𝕜) :
    HasDerivAt (fun t : 𝕜 => (aevalTower φ (y + t • v) : MvPolynomial ι R →ₐ[𝕜] 𝕜) q)
      (∑ i, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv i q) * v i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : 𝕜) (φ a)
  | add P Q hP hQ =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hP.add hQ
  | mul_X P i hP =>
    have hX : HasDerivAt (fun t : 𝕜 => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const (v i)).const_add (y i)
    have h := hP.mul hX
    simp only [map_mul, aevalTower_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.congr_deriv h ?_
    have h1 : ∀ j, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv j (P * X i)) * v j =
        (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv j P) * v j * y i +
        if i = j then (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) P * v j else 0 := by
      intro j
      rw [pderiv_mul, pderiv_X]
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij, Pi.single_eq_of_ne hij]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_mul]
    simp
end GlobalTheory.AffinePoints
