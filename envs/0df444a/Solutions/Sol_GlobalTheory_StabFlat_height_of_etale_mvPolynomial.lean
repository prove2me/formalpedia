-- Prove2me | solution 1 for GlobalTheory.StabFlat.height_of_etale_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:15:58.200945+00:00
-- url     : https://prove2.me/submissions/49cf28eb-a5f3-4af1-a572-2256b6bc95ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth
import Theorems.Thm_GlobalTheory_SmoothDim_isMaximal_under_of_finiteType
import Theorems.Thm_GlobalTheory_SmoothDim_ringKrullDim_of_etale_mvPolynomial
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat
namespace GlobalTheory.StabFlat
theorem _root_.solution (K B : Type*) [Field K] [CommRing B] (g : ℕ)
    [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] (m : Ideal B) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = g := by
  have : Nontrivial B := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hm.ne_top (Subsingleton.elim _ _)
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_isPrime.trans
    (SmoothDim.ringKrullDim_of_etale_mvPolynomial K B g).le) ?_
  letI : Algebra K B := ((algebraMap (MvPolynomial (Fin g) K) B).comp
    (algebraMap K (MvPolynomial (Fin g) K))).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin g) K) B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K B := Algebra.FiniteType.trans
    (S := MvPolynomial (Fin g) K) inferInstance inferInstance
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI hp := SmoothDim.isMaximal_under_of_finiteType K (MvPolynomial (Fin g) K) B m
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K g
    (m.under (MvPolynomial (Fin g) K))
  letI := Ideal.Quotient.field (m.under (MvPolynomial (Fin g) K))
  rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
  rw [← h1, WithBot.coe_le_coe, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (m.under (MvPolynomial (Fin g) K)) m]
  exact le_self_add
end GlobalTheory.StabFlat
