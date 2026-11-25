-- Prove2me | solution 1 for GlobalTheory.noetherNormalization_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:24.809799+00:00
-- url     : https://prove2.me/submissions/ecda4508-56e0-4fcb-9467-bd197c672fd3

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsPrimitiveElementDiscriminantMultiple
import Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_primitive
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_isIntegral_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
theorem _root_.solution :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) := by
  intro A _ _ _ _
  obtain ⟨d, j, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := j.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) A) := hinj
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  obtain ⟨a, q, hq, hq₁, hq₂⟩ := GlobalTheory.NoetherPrimitive.exists_primitive (MvPolynomial (Fin d) ℂ) A
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) a := Algebra.IsIntegral.isIntegral a
  refine ⟨d, j, a, minpoly _ a, q, ?_, hinj, hfin, minpoly.monic hint, minpoly.irreducible hint,
    fun r => minpoly.isIntegrallyClosed_dvd_iff hint r, hq, hq₁, hq₂⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj',
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
end GlobalTheory
