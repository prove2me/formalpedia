-- Prove2me | solution 1 for GlobalTheory.ZM.ThIdeal.coeff_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:10.284527+00:00
-- url     : https://prove2.me/submissions/db78de14-7e66-449b-b3ad-1af043ff0aae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaPointsVanishingIdealRadicalHomogeneous

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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ThIdeal
namespace GlobalTheory.ZM.ThIdeal
theorem _root_.solution {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
    have hm : MvPolynomial.monomial d c ∈ MvPolynomial.homogeneousSubmodule σ R d.degree :=
      MvPolynomial.isHomogeneous_monomial c rfl
    rw [MvPolynomial.homogeneousComponent_of_mem hm]
    have : MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (MvPolynomial.monomial d c) =
        Polynomial.C (MvPolynomial.eval₂Hom β w (MvPolynomial.monomial d c)) * Polynomial.X ^ d.degree := by
      simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, RingHom.comp_apply, Finsupp.degree_apply]
      ring
    rw [this, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
end GlobalTheory.ZM.ThIdeal
