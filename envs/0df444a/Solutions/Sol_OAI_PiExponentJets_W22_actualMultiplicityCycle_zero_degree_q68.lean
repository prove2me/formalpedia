-- Prove2me | solution 1 for OAI.PiExponentJets.W22.actualMultiplicityCycle_zero_degree_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:15:07.9996+00:00
-- url     : https://prove2.me/submissions/3a7ecaa0-83c7-4061-91b5-e16d9f473c88

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A011
import Definitions.Def_OAIQ068A027

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem quotientSectionMultiply_injective (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Function.Injective (quotientSectionMultiply I f hf n) := by
  intro x y h
  apply Subtype.ext
  exact hreg (congrArg Subtype.val h)

theorem quotientSectionCokernel_finrank_add (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k
        (quotientSection I (n + d) ⧸
          LinearMap.range (quotientSectionMultiply I f hf n)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n + d)) := by
  have hi := quotientSectionMultiply_injective I f hf hreg n
  simpa only [LinearMap.finrank_range_of_inj hi] using
    (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularHilbertStep
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem regular_hilbert_step [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) (n+d)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n+d)) := by
  have hd := quotientSectionCokernel_finrank_add I f hf hreg n
  rw [← quotientSectionFactor_ker_eq I hI f hf n] at hd
  let e := (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)).quotKerEquivOfSurjective
      (quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right (n+d))
  rw [e.finrank_eq] at hd
  exact hd

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_HilbertSeries
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

theorem sectionHilbertSeries_regular_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) :
    sectionHilbertSeries (Ideal.span {f} ⊔ I) =
      (1 - PowerSeries.X ^ d) * sectionHilbertSeries I := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_sectionHilbertSeries]
  by_cases hdn : d ≤ n
  · rw [ite_eq_left hdn]
    have h := regular_hilbert_step I hI f hf hreg (n-d)
    rw [Nat.sub_add_cancel hdn] at h
    apply eq_sub_of_add_eq
    exact_mod_cast h
  · rw [ite_eq_right hdn, sub_zero]
    exact congrArg (fun m : ℕ => (m : ℤ))
      (hilbert_step_of_degree_lt I hI f hf (Nat.lt_of_not_ge hdn))

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularPrefixes
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegel.W20

section Ring

variable {R : Type*} [CommRing R]

theorem prefixIdeal_succ (rs : List R) (i : Fin rs.length) :
    Ideal.ofList (rs.take (i.val + 1)) =
      Ideal.span {rs[i]} ⊔ Ideal.ofList (rs.take i.val) := by
  rw [List.take_succ_eq_append_getElem i.isLt, Ideal.ofList_append,
    Ideal.ofList_singleton, sup_comm]
  simp only [Fin.getElem_fin]

theorem regular_next_mod_prefix (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) :
    IsRightRegular (Ideal.Quotient.mk (Ideal.ofList (rs.take i.val)) rs[i]) := by
  have hsmul := hreg.toIsWeaklyRegular.regular_mod_prev i.val i.isLt
  have htop : (Ideal.ofList (rs.take i.val) • (⊤ : Submodule R R)) =
      Ideal.ofList (rs.take i.val) := by
    exact (Ideal.ofList (rs.take i.val)).mul_top
  rw [htop] at hsmul
  intro x y hxy
  apply hsmul
  simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm,
    Fin.getElem_fin] using hxy

end Ring

attribute [local instance] MvPolynomial.gradedAlgebra

end PiExponentSiegel.W20

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HilbertPolynomialBase
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

variable {σ : Type*}

variable {k : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem quotientSection_bot_finrank (n : ℕ) :
    Module.finrank k (quotientSection (⊥ : Ideal (MvPolynomial σ k)) n) =
      Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) := by
  let e := LinearEquiv.ofBijective
    (Ideal.Quotient.mkₐ k (⊥ : Ideal (MvPolynomial σ k))).toLinearMap
    ((Ideal.Quotient.mk_bijective_iff_eq_bot (⊥ : Ideal (MvPolynomial σ k))).mpr rfl)
  exact e.finrank_map_eq (MvPolynomial.homogeneousSubmodule σ k n)

theorem quotientSection_bot_finrank_multichoose [Fintype σ] (n : ℕ) :
    Module.finrank k (quotientSection (⊥ : Ideal (MvPolynomial σ k)) n) =
      (Fintype.card σ).multichoose n := by
  rw [quotientSection_bot_finrank, homogeneousSection_finrank, card_exponents_degree]

theorem sectionHilbertSeries_bot [Fintype σ] (hσ : 0 < Fintype.card σ) :
    sectionHilbertSeries (⊥ : Ideal (MvPolynomial σ k)) =
      (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ (Fintype.card σ) hσ]
  ext n
  rw [coeff_sectionHilbertSeries, PowerSeries.coeff_mk,
    quotientSection_bot_finrank_multichoose, Nat.multichoose_eq]
  congr 1
  have hs : Fintype.card σ + n - 1 = (Fintype.card σ - 1) + n := by omega
  rw [hs]
  exact Nat.choose_symm_add.symm

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_RegularSequenceSeries
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

theorem regular_prefix_series
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (n : ℕ) (hn : n ≤ rs.length) :
    sectionHilbertSeries (Ideal.ofList (rs.take n)) =
      (∏ i ∈ Finset.range n, (1 - PowerSeries.X ^ degreeAt degrees i)) *
        sectionHilbertSeries (⊥ : Ideal (MvPolynomial σ k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n < rs.length := hn
    have hn' : n ≤ rs.length := Nat.le_of_lt hlt
    rw [PiExponentSiegel.W20.prefixIdeal_succ rs ⟨n, hlt⟩]
    simp only [Fin.getElem_fin]
    have hh : (rs[n]'hlt).IsHomogeneous (degrees ⟨n, hlt⟩) := by
      simpa only [Fin.getElem_fin] using hhom ⟨n, hlt⟩
    have hr : IsRightRegular (Ideal.Quotient.mk (Ideal.ofList (rs.take n)) (rs[n]'hlt)) := by
      simpa only [Fin.getElem_fin] using
        PiExponentSiegel.W20.regular_next_mod_prefix rs hreg ⟨n, hlt⟩
    rw [sectionHilbertSeries_regular_step _
      (PiExponentSiegel.W20.prefixIdeal_homogeneous rs degrees hhom n)
      (rs[n]'hlt) hh hr]
    rw [ih hn', Finset.prod_range_succ]
    simp only [degreeAt, dite_eq_left hlt]
    ac_rfl

theorem degree_factors_mul_invOneSubPow (D : ℕ → ℕ) (m : ℕ) :
    (∏ i ∈ Finset.range m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ D i)) *
      (PowerSeries.invOneSubPow ℤ m).val =
      ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
        (PowerSeries.X : PowerSeries ℤ) ^ j := by
  have hfactor :
      (∏ i ∈ Finset.range m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ D i)) =
        (∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
          (PowerSeries.X : PowerSeries ℤ) ^ j) * (1 - PowerSeries.X) ^ m := by
    simp_rw [← geom_sum_mul_neg]
    rw [Finset.prod_mul_distrib]
    simp
  rw [hfactor, mul_assoc, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  rw [(PowerSeries.invOneSubPow ℤ m).inv_val, mul_one]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CompleteIntersectionHilbert
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem degreePolynomial_eval_one (D : ℕ → ℕ) (m : ℕ) :
    (degreePolynomial D m).eval 1 = ∏ i ∈ Finset.range m, (D i : ℤ) := by
  simp [degreePolynomial, Polynomial.eval_prod, Polynomial.eval_finsetSum]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PositiveDimensionalHilbert
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem regular_sequence_series_general
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    sectionHilbertSeries (Ideal.ofList rs) =
      (∏ i ∈ Finset.range rs.length, (1 - PowerSeries.X ^ degreeAt degrees i)) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  have h := regular_prefix_series rs degrees hhom hreg rs.length le_rfl
  simp only [List.take_length] at h
  rwa [sectionHilbertSeries_bot hσ] at h

theorem degreePolynomial_coe (D : ℕ → ℕ) (m : ℕ) :
    ((degreePolynomial D m) : PowerSeries ℤ) =
      ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
        (PowerSeries.X : PowerSeries ℤ) ^ j := by
  change (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ)
    (∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
      (Polynomial.X : Polynomial ℤ) ^ j) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_pow]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem regular_sequence_series_residual
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) :
    sectionHilbertSeries (Ideal.ofList rs) =
      ((degreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ - rs.length)).val := by
  rw [regular_sequence_series_general hσ rs degrees hhom hreg]
  have hn : Fintype.card σ = rs.length + (Fintype.card σ - rs.length) :=
    (Nat.add_sub_of_le hlen).symm
  have hi := congrArg (PowerSeries.invOneSubPow ℤ) hn
  rw [PowerSeries.invOneSubPow_add] at hi
  rw [hi, Units.val_mul, ← mul_assoc,
    degree_factors_mul_invOneSubPow, ← degreePolynomial_coe]

theorem rationalDegreePolynomial_eval_one (D : ℕ → ℕ) (m : ℕ) :
    (rationalDegreePolynomial D m).eval 1 =
      (∏ i ∈ Finset.range m, D i : ℕ) := by
  rw [rationalDegreePolynomial, Polynomial.eval_one_map, degreePolynomial_eval_one]
  simp

theorem rational_regular_sequence_series_residual
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) :
    rationalSectionHilbertSeries (Ideal.ofList rs) =
      ((rationalDegreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card σ - rs.length)).val := by
  rw [rationalSectionHilbertSeries,
    regular_sequence_series_residual hσ rs degrees hhom hreg hlen,
    map_mul, map_int_invOneSubPow]
  rw [← Polynomial.polynomial_map_coe]
  rfl

theorem regularSequenceHilbertPolynomial_eventually_exact
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) (n : ℕ)
    (hn : (rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree < n) :
    (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℚ) =
      (regularSequenceHilbertPolynomial rs degrees).eval (n : ℚ) := by
  rw [← coeff_rationalSectionHilbertSeries,
    rational_regular_sequence_series_residual hσ rs degrees hhom hreg hlen]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

theorem hilbertPolynomial_top_coefficient (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) :
    (Polynomial.hilbertPoly p r).coeff (r-1) =
      p.eval 1 * ((r-1).factorial : ℚ)⁻¹ := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one, Polynomial.hilbertPoly_succ,
    Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_preHilbertPoly_self]
  rw [← Finset.sum_mul]
  congr 1
  simp [Polynomial.eval_eq_sum, Polynomial.sum]

theorem hilbertPolynomial_natDegree_le (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) :
    (Polynomial.hilbertPoly p r).natDegree ≤ r-1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one, Polynomial.hilbertPoly_succ]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_smul_le _ _).trans
    (Polynomial.natDegree_preHilbertPoly ℚ s i).le

theorem hilbertPolynomial_degree_and_leading
    (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) (hp : p.eval 1 ≠ 0) :
    (Polynomial.hilbertPoly p r).natDegree = r-1 ∧
      (Polynomial.hilbertPoly p r).leadingCoeff = p.eval 1 * ((r-1).factorial : ℚ)⁻¹ := by
  have hf : (((r-1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r-1)
  have hc : (Polynomial.hilbertPoly p r).coeff (r-1) ≠ 0 := by
    rw [hilbertPolynomial_top_coefficient p r hr]
    exact mul_ne_zero hp (inv_ne_zero hf)
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (hilbertPolynomial_natDegree_le p r hr) hc
  refine ⟨hd, ?_⟩
  rw [Polynomial.leadingCoeff, hd, hilbertPolynomial_top_coefficient p r hr]

theorem regularSequenceHilbertPolynomial_multiplicity
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hlen : rs.length < Fintype.card σ) :
    hilbertMultiplicity (regularSequenceHilbertPolynomial rs degrees)
        (Fintype.card σ - rs.length) =
      (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  have hr : 0 < Fintype.card σ - rs.length := Nat.sub_pos_of_lt hlen
  have hf : (((Fintype.card σ - rs.length - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card σ - rs.length - 1)
  rw [hilbertMultiplicity, regularSequenceHilbertPolynomial,
    hilbertPolynomial_top_coefficient _ _ hr, mul_assoc, inv_mul_cancel₀ hf,
    mul_one, rationalDegreePolynomial_eval_one]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HilbertPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem polynomial_eq_of_nat_tail (p q : Polynomial ℚ) (N : ℕ)
    (h : ∀ n : ℕ, N < n → p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  have hinj : Function.Injective (fun n : ℕ => ((N + 1 + n : ℕ) : ℚ)) := by
    intro a b hab
    change ((N + 1 + a : ℕ) : ℚ) = ((N + 1 + b : ℕ) : ℚ) at hab
    have hab' : N + 1 + a = N + 1 + b := by exact_mod_cast hab
    omega
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  exact h _ (by omega)

theorem actualHP_eventually (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = (actualHP I hI).eval (n : ℚ) :=
  (exists_homogeneous_hilbert_polynomial σ I hI).choose_spec

theorem actualHP_unique (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) :
    actualHP I hI = p := by
  obtain ⟨M, hM⟩ := actualHP_eventually I hI
  apply polynomial_eq_of_nat_tail _ _ (M + N)
  intro n hn
  exact (hM n (by omega)).symm.trans (hp n (by omega))

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalComponentDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

theorem localized_prime_factor_length_one
    (Q : Ideal R) [Q.IsPrime] :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ Q.map (algebraMap R (Localization.AtPrime Q))) = 1 := by
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  let : IsSimpleModule (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  exact Module.length_eq_one _ _

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularDegreePositivity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegel.W20

open scoped BigOperators

section Ring

variable {R : Type*} [CommRing R]

theorem regular_sequence_ideal_ne_top (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) : Ideal.ofList rs ≠ ⊤ := by
  intro htop
  apply hreg.top_ne_smul
  have hmul : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
    (Ideal.ofList rs).mul_top
  rw [hmul, htop]

theorem regular_sequence_term_not_isUnit (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) :
    ¬ IsUnit rs[i] := by
  intro hunit
  apply regular_sequence_ideal_ne_top rs hreg
  exact (Ideal.ofList rs).eq_top_of_isUnit_mem
    (Ideal.subset_span (List.getElem_mem i.isLt)) hunit

theorem regular_sequence_term_ne_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) : rs[i] ≠ 0 := by
  let I : Ideal R := Ideal.ofList (rs.take i.val)
  have hle : I ≤ Ideal.ofList rs :=
    Ideal.span_mono (List.take_subset i.val rs)
  have hproper : I ≠ ⊤ := ne_top_of_le_ne_top
    (regular_sequence_ideal_ne_top rs hreg) hle
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hsmul := hreg.toIsWeaklyRegular.regular_mod_prev i.val i.isLt
  have hmul : (Ideal.ofList (rs.take i.val) • (⊤ : Submodule R R)) = I := I.mul_top
  rw [hmul] at hsmul
  intro hz
  have hz' : rs[i.val] = 0 := by simpa only [Fin.getElem_fin] using hz
  have hsmulzero : IsSMulRegular (R ⧸ I) (0 : R) := hz' ▸ hsmul
  exact IsSMulRegular.not_zero hsmulzero

end Ring

variable {k σ : Type*} [Field k]

theorem regular_homogeneous_degrees_pos
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    ∀ i, 0 < degrees i := by
  intro i
  by_contra hpos
  have hzero : degrees i = 0 := Nat.eq_zero_of_not_pos hpos
  have hhomzero : rs[i].IsHomogeneous 0 := by simpa only [hzero] using hhom i
  have hdegzero : (rs[i]).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr hhomzero
  have hconstant : rs[i] = MvPolynomial.C ((rs[i]).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegzero
  have hcoeff : (rs[i]).coeff 0 ≠ 0 := by
    intro hz
    apply regular_sequence_term_ne_zero rs hreg i
    rw [hconstant, hz, map_zero]
  apply regular_sequence_term_not_isUnit rs hreg i
  rw [hconstant]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C

end PiExponentSiegel.W20

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CompleteIntersectionComponentBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem actualHP_regular_sequence
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualHP (Ideal.ofList rs) hI = regularSequenceHilbertPolynomial rs degrees := by
  apply actualHP_unique _ hI _
    (rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree
  intro n hn
  exact regularSequenceHilbertPolynomial_eventually_exact
    (lt_of_le_of_lt (Nat.zero_le _) hlen) rs degrees hhom hreg hlen.le n hn

omit [Fintype σ] in
theorem regular_degreeAt_product_ne_zero
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi' := Finset.mem_range.mp hi
  simp only [degreeAt, dite_eq_left hi']
  exact Nat.ne_of_gt (PiExponentSiegel.W20.regular_homogeneous_degrees_pos
    rs degrees hhom hreg ⟨i, hi'⟩)

theorem actualHP_regular_sequence_natDegree
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (actualHP (Ideal.ofList rs) hI).natDegree = Fintype.card σ - rs.length - 1 := by
  rw [actualHP_regular_sequence rs degrees hhom hreg hlen hI]
  have hp : (rationalDegreePolynomial (degreeAt degrees) rs.length).eval 1 ≠ 0 := by
    rw [rationalDegreePolynomial_eval_one]
    exact_mod_cast regular_degreeAt_product_ne_zero rs degrees hhom hreg
  exact (hilbertPolynomial_degree_and_leading _ _ (Nat.sub_pos_of_lt hlen) hp).1

theorem actualMultiplicity_regular_sequence
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualMultiplicity (Ideal.ofList rs) hI (actualHP (Ideal.ofList rs) hI).natDegree =
      (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  rw [actualHP_regular_sequence_natDegree rs degrees hhom hreg hlen hI]
  unfold actualMultiplicity
  rw [actualHP_regular_sequence rs degrees hhom hreg hlen hI]
  exact regularSequenceHilbertPolynomial_multiplicity rs degrees hlen

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularCutHistory
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

theorem actualMultiplicityCycle_zero_degree_q68_oai
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) :
    (actualMultiplicityCycle (⊥ : Ideal (MvPolynomial σ k))
      (Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)) T v hv).degree = 1 := by
  let hbot := Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)
  have hminimal : (⊥ : Ideal (MvPolynomial σ k)) ∈ (⊥ : Ideal (MvPolynomial σ k)).minimalPrimes :=
    ⟨⟨inferInstance, le_rfl⟩, fun _ _ _ => bot_le⟩
  let B : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T := ⟨⊥, hminimal, bot_le⟩
  have hevery (P : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T) : P = B := by
    apply Subtype.ext
    exact le_antisymm (P.property.1.2 ⟨inferInstance, le_rfl⟩ bot_le) bot_le
  have hlength : actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) ⊥ = 1 := by
    unfold actualLocalLength
    rw [localized_prime_factor_length_one]
    exact ENat.toNat_natCast 1
  let degrees : Fin ([] : List (MvPolynomial σ k)).length → ℕ := fun i => Fin.elim0 i
  have hhom : ∀ i : Fin ([] : List (MvPolynomial σ k)).length,
      ([] : List (MvPolynomial σ k))[i].IsHomogeneous (degrees i) := fun i => Fin.elim0 i
  have hreg := RingTheory.Sequence.IsRegular.nil (MvPolynomial σ k) (MvPolynomial σ k)
  have hlen : ([] : List (MvPolynomial σ k)).length < Fintype.card σ :=
    Fintype.card_pos_iff.mpr ⟨v⟩
  have hnilhom : (Ideal.ofList ([] : List (MvPolynomial σ k))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by simpa only [Ideal.ofList_nil] using hbot
  have hdegree : actualMultiplicity (⊥ : Ideal (MvPolynomial σ k)) hbot
      (actualHP ⊥ hbot).natDegree = 1 := by
    simpa only [Ideal.ofList_nil, List.length_nil, Finset.range_zero, Finset.prod_empty,
      Nat.cast_one] using actualMultiplicity_regular_sequence [] degrees hhom hreg hlen hnilhom
  unfold RetainedPrimeCycle.degree
  change (∑ P : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T,
    (actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) P.val : ℚ) *
      (RetainedMinimalPrime.toComponent hbot v hv P).hilbertDegree) = 1
  rw [Finset.sum_eq_single B]
  · change (actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) ⊥ : ℚ) *
      actualMultiplicity (⊥ : Ideal (MvPolynomial σ k)) hbot (actualHP ⊥ hbot).natDegree = 1
    rw [hlength, Nat.cast_one, hdegree, one_mul]
  · intro P _ hne
    exact False.elim (hne (hevery P))
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ B))

end PiExponentJets.W22

end OAI
end

theorem solution.{u} : type_of% @OAI.PiExponentJets.W22.actualMultiplicityCycle_zero_degree_q68_oai.{u} := @OAI.PiExponentJets.W22.actualMultiplicityCycle_zero_degree_q68_oai.{u}
