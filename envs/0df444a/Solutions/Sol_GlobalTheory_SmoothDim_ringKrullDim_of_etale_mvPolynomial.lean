-- Prove2me | solution 1 for GlobalTheory.SmoothDim.ringKrullDim_of_etale_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:34:12.630113+00:00
-- url     : https://prove2.me/submissions/c5e625b7-1348-429c-ae74-e3dafc50ecc6

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Theorems.Thm_GlobalTheory_SmoothDim_isMaximal_under_of_finiteType
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SmoothDim
namespace GlobalTheory.SmoothDim
theorem _root_.solution (K B : Type*) [Field K] [CommRing B] [Nontrivial B]
    (g : ℕ) [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] :
    ringKrullDim B = g := by
  have hR : ringKrullDim (MvPolynomial (Fin g) K) = g := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  apply le_antisymm
  · rw [← hR]
    refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin g) K) B)) fun P Q hPQ => ?_
    refine lt_of_le_of_ne (Ideal.comap_mono hPQ.le) fun h => hPQ.ne ?_
    exact PrimeSpectrum.ext (Algebra.QuasiFinite.eq_of_le_of_under_eq
      (R := MvPolynomial (Fin g) K) _ _ hPQ.le (congrArg PrimeSpectrum.asIdeal h))
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    letI : Algebra K B := ((algebraMap (MvPolynomial (Fin g) K) B).comp
      (algebraMap K (MvPolynomial (Fin g) K))).toAlgebra
    haveI : IsScalarTower K (MvPolynomial (Fin g) K) B := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.FiniteType K B := Algebra.FiniteType.trans
      (S := MvPolynomial (Fin g) K) inferInstance inferInstance
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
    haveI hp := isMaximal_under_of_finiteType K (MvPolynomial (Fin g) K) B m
    have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K g
      (m.under (MvPolynomial (Fin g) K))
    letI := Ideal.Quotient.field (m.under (MvPolynomial (Fin g) K))
    rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
    have h2 : (m.under (MvPolynomial (Fin g) K)).height ≤ m.height := by
      rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
        (m.under (MvPolynomial (Fin g) K)) m]
      exact le_self_add
    rw [← h1]
    exact (WithBot.coe_le_coe.mpr h2).trans Ideal.height_le_ringKrullDim_of_isPrime
end GlobalTheory.SmoothDim
