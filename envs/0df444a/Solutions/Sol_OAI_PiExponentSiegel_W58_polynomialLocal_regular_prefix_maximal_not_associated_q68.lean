-- Prove2me | solution 1 for OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:03:23.238182+00:00
-- url     : https://prove2.me/submissions/716392e9-06e5-4850-8a22-d879ec3c7c1d

import Mathlib
import Definitions.Def_OAIQ068A019
import Theorems.Thm_OAI_PiExponentJets_PolynomialLocalResidueResolution_exists_regularParameters_actual_height_q68
import Theorems.Thm_OAI_PiExponentSiegelAux_W30_iterateScalarCones_dual_low_exact_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulFiniteFree
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30

universe u
variable {R : Type u} [CommRing R]

lemma scalarCone_finite (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hfinite : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => exact hfinite 0
  | succ n =>
    let := hfinite (n + 1)
    let := hfinite n
    change Module.Finite R (C.X (n + 1) × C.X n)
    infer_instance

lemma iterateScalarCones_finite (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C with
  | nil => exact hfinite n
  | cons r rs ih => exact ih (scalarConeComplex C r) (scalarCone_finite C r hfinite)

theorem regularSequenceComplex_finite (rs : List R) (n : ℕ) :
    Module.Finite R ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_finite
  intro k
  cases k with
  | zero =>
    change Module.Finite R R
    exact Module.Finite.self R
  | succ k =>
    change Module.Finite R (Fin 0 → R)
    infer_instance

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulBounded
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
universe u
variable {R : Type u} [CommRing R]

lemma scalarCone_bounded (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) (n : ℕ) (hn : d + 1 < n) :
    Subsingleton ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => omega
  | succ n =>
    let := hbound n (by omega)
    let := hbound (n + 1) (by omega)
    change Subsingleton (C.X (n + 1) × C.X n)
    infer_instance

lemma iterateScalarCones_bounded (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (d : ℕ) (hbound : ∀ n, d < n → Subsingleton (C.X n))
    (n : ℕ) (hn : d + rs.length < n) :
    Subsingleton ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C d with
  | nil => exact hbound n (by simpa using hn)
  | cons r rs ih =>
    apply ih (scalarConeComplex C r) (d + 1) (scalarCone_bounded C r d hbound)
    simp only [List.length_cons] at hn
    omega

theorem regularSequenceComplex_bounded (rs : List R) (n : ℕ) (hn : rs.length < n) :
    Subsingleton ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_bounded rs emptyKoszulComplex 0 ?_ n (by simpa using hn)
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
    change Subsingleton (Fin 0 → R)
    infer_instance

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_KoszulTopDifferential
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open Module
variable {R : Type u} [CommRing R]

theorem scalarConeFirstTopBoundary_eval
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (α : Module.Dual R (C.X 0)) (t : C.X 0) :
    (((W30.scalarConeComplex C r).d 1 0).hom.dualMap α) (0, t) = r * α t := by
  change α ((C.d 1 0).hom 0 + r • t) = r * α t
  simp only [map_zero, zero_add, map_smul, smul_eq_mul]

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteFreeExtTransfer
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe w v u

namespace PiExponentSiegelAux.W31
open Module
open CategoryTheory CategoryTheory.Abelian
open scoped BigOperators

section General
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_finite_identity_factorization
    {ι : Type*} [Fintype ι] (X F G : C) (n : ℕ)
    (p : ι → (F ⟶ G)) (j : ι → (G ⟶ F))
    (htotal : (∑ i, p i ≫ j i) = 𝟙 F)
    (h : Subsingleton (Ext X G n)) : Subsingleton (Ext X F n) := by
  apply subsingleton_of_forall_eq 0
  intro e
  have he : (∑ i, (e.comp (Ext.mk₀ (p i)) (add_zero n)).comp
      (Ext.mk₀ (j i)) (add_zero n)) = e := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      ← Ext.comp_sum, ← Ext.mk₀_sum, htotal, Ext.comp_mk₀_id]
  calc
    e = _ := he.symm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [h.elim (e.comp (Ext.mk₀ (p i)) (add_zero n)) 0, Ext.zero_comp]

end General

variable {R : Type u} [CommRing R]
variable {F : Type u} [AddCommGroup F] [Module R F]

theorem ext_subsingleton_of_finite_basis {ι : Type*} [Fintype ι]
    (b : Basis ι R F) (X : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X (ModuleCat.of R F) n) := by
  apply ext_subsingleton_of_finite_identity_factorization X (ModuleCat.of R F)
    (ModuleCat.of R R) n
    (fun i => ModuleCat.ofHom (b.coord i))
    (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i))) ?_ h
  apply ModuleCat.hom_ext
  ext x
  simpa only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    ModuleCat.hom_id, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, Basis.coord_apply, LinearMap.id_apply] using
    b.sum_repr x

theorem ext_subsingleton_of_finite_free [Module.Free R F] [Module.Finite R F]
    (X : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X (ModuleCat.of R F) n) :=
  ext_subsingleton_of_finite_basis (Module.Free.chooseBasis R F) X n h

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteFreeResolutionExt
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe w v u

namespace PiExponentSiegelAux.W31
open Module
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex

section General
variable {C : Type u} [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

theorem ext_subsingleton_iff_cocycles_are_boundaries
    (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Subsingleton (Ext M Y (n + 1)) ↔
      ∀ (f : P.complex.X (n + 1) ⟶ Y),
        P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f := by
  constructor
  · intro h f hf
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp
      (h.elim _ 0)
  · intro h
    apply subsingleton_of_forall_eq 0
    intro e
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 2) rfl
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr (h f hf)

end General

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FreeResolutionAssociatedHeight
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe w v u

namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian

section ExactDimensionShifting
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_shortExact
    (X : C) (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ)
    (hmid : Subsingleton (Ext X S.X₂ n))
    (hleft : Subsingleton (Ext X S.X₁ (n + 1))) :
    Subsingleton (Ext X S.X₃ n) := by
  let := hmid
  let := hleft
  apply subsingleton_of_forall_eq 0
  intro e
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ X hS e rfl
    (Subsingleton.elim _ 0)
  rw [Subsingleton.elim a 0, Ext.zero_comp] at ha
  exact ha.symm

end ExactDimensionShifting

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

theorem associatedPrime_nonzero_quotient_hom (P : Ideal R)
    (hP : IsAssociatedPrime P M) :
    ∃ f : R ⧸ P →ₗ[R] M, f ≠ 0 := by
  obtain ⟨hprime, f, hf⟩ :=
    (isAssociatedPrime_iff_exists_injective_linearMap P M).mp hP
  let := hprime
  refine ⟨f, ?_⟩
  intro hz
  have h10 : (1 : R ⧸ P) = 0 := hf (by simp [hz])
  exact one_ne_zero h10

theorem associatedPrime_nonzero_ext_zero (P : Ideal R)
    (hP : IsAssociatedPrime P M) :
    ∃ e : Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R M) 0, e ≠ 0 := by
  obtain ⟨f, hf⟩ := associatedPrime_nonzero_quotient_hom P hP
  refine ⟨Ext.mk₀ (ModuleCat.ofHom f), ?_⟩
  intro he
  have hh := (Ext.mk₀_eq_zero_iff (ModuleCat.ofHom f)).mp he
  exact hf (congrArg (fun g : ModuleCat.of R (R ⧸ P) ⟶ ModuleCat.of R M => g.hom) hh)

theorem not_isAssociatedPrime_of_ext_zero (P : Ideal R)
    (h : Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R M) 0)) :
    ¬ IsAssociatedPrime P M := by
  intro hP
  obtain ⟨e, he⟩ := associatedPrime_nonzero_ext_zero P hP
  exact he (h.elim e 0)

end PiExponentJets.W18

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulDualBottom
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [Module R X] [Module R Y] [Module R Z]

theorem coneBottom_dual_equiv (g : Y →ₗ[R] Z) (r : R) :
    (dualProdDualEquivDual R Y Z).toLinearMap.comp (dualConeBottom g r) =
      (coneBottom g r).dualMap := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  rintro ⟨y, z⟩
  change α (g y) + r • α z = α (g y + r • z)
  rw [map_add, map_smul]

theorem dualConeBottom_injective_of_regular (g : Y →ₗ[R] Z) (r : R)
    (hr : IsSMulRegular (Dual R Z) r) : Function.Injective (dualConeBottom g r) := by
  intro α β h
  exact hr (congrArg Prod.snd h)

universe u

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulDualInitial
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R A B : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

theorem regular_on_dual (r : R) (hr : IsSMulRegular R r) :
    IsSMulRegular (Dual R A) r := by
  intro α β h
  apply LinearMap.ext
  intro a
  apply hr
  exact congrArg (fun φ : Dual R A => φ a) h

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_zero_injective_of_regular
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (hr : IsSMulRegular S r) :
    Function.Injective ((scalarConeComplex P r).d 1 0).hom.dualMap := by
  have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
    ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
  rw [hd]
  change Function.Injective (coneBottom (P.d 1 0).hom r).dualMap
  intro α β h
  apply dualConeBottom_injective_of_regular (P.d 1 0).hom r (regular_on_dual r hr)
  apply (dualProdDualEquivDual S (P.X 1) (P.X 0)).injective
  have he (φ : Dual S (P.X 0)) :
      (dualProdDualEquivDual S (P.X 1) (P.X 0)) (dualConeBottom (P.d 1 0).hom r φ) =
        (coneBottom (P.d 1 0).hom r).dualMap φ :=
    LinearMap.congr_fun (coneBottom_dual_equiv (P.d 1 0).hom r) φ
  rw [he, he]
  exact h

theorem scalarCone_first_top_dual_image
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hbound : ∀ k, 0 < k → Subsingleton (P.X k)) (e : P.X 0 ≃ₗ[S] S) :
    LinearMap.range
      ((W31.scalarConeTopDualCoordinate P r 0 hbound e).toLinearMap.comp
        ((scalarConeComplex P r).d 1 0).hom.dualMap) = Ideal.span {r} := by
  have he (α : Dual S (P.X 0)) :
      W31.scalarConeTopDualCoordinate P r 0 hbound e
        (((scalarConeComplex P r).d 1 0).hom.dualMap α) =
          r * W31.topDualCoordinate e α := by
    rw [W31.scalarConeTopDualCoordinate_apply]
    exact W31.scalarConeFirstTopBoundary_eval P r α (e.symm 1)
  ext z
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨W31.topDualCoordinate e α, ?_⟩
    exact hα.symm.trans (he α)
  · rintro ⟨a, ha⟩
    refine ⟨(W31.topDualCoordinate e).symm a, ?_⟩
    change W31.scalarConeTopDualCoordinate P r 0 hbound e
      (((scalarConeComplex P r).d 1 0).hom.dualMap ((W31.topDualCoordinate e).symm a)) = z
    rw [he, LinearEquiv.apply_symm_apply]
    exact ha.symm

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceExt
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {R : Type u} [CommRing R]

theorem regularSequenceQuotientExt_iff_boundaries (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y (n + 1)) ↔
      ∀ f : (W30.regularSequenceComplex rs).X (n + 1) ⟶ Y,
        (W30.regularSequenceComplex rs).d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : (W30.regularSequenceComplex rs).X n ⟶ Y,
          (W30.regularSequenceComplex rs).d (n + 1) n ≫ g = f :=
  ext_subsingleton_iff_cocycles_are_boundaries _ Y (regularSequenceResolution rs hreg) n

theorem regularSequenceQuotientExt_of_dual_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ)
    (hdual : LinearMap.range (((W30.regularSequenceComplex rs).d (n + 1) n).hom.dualMap) =
      LinearMap.ker (((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap)) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) (n + 1)) := by
  apply (regularSequenceQuotientExt_iff_boundaries rs hreg (ModuleCat.of R R) n).mpr
  intro f hf
  have hfker : f.hom ∈
      LinearMap.ker (((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap) := by
    change f.hom.comp ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom = 0
    exact ModuleCat.hom_ext_iff.mp hf
  rw [← hdual] at hfker
  obtain ⟨g, hg⟩ := hfker
  refine ⟨ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  exact hg

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceExtObstruction
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian
open PiExponentSiegelAux

variable {R : Type u} [CommRing R]

section RangeSequences
variable {L M N : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
  [Module R L] [Module R M] [Module R N]

theorem differentialRangeShortComplex_shortExact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) :
    (differentialRangeShortComplex f g hex).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (LinearMap.range f).subtype = LinearMap.ker g.rangeRestrict
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict, hex]
  · exact (ModuleCat.mono_iff_injective _).mpr (LinearMap.range f).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr (LinearMap.surjective_rangeRestrict g)

theorem augmentationRangeShortComplex_shortExact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) (hg : Function.Surjective g) :
    (augmentationRangeShortComplex f g hex).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (LinearMap.range f).subtype = LinearMap.ker g
    rw [Submodule.range_subtype, hex]
  · exact (ModuleCat.mono_iff_injective _).mpr (LinearMap.range f).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr hg

end RangeSequences

theorem ext_subsingleton_of_subsingleton_module
    {M : Type u} [AddCommGroup M] [Module R M] [Subsingleton M]
    (X : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Ext X (ModuleCat.of R M) n) := by
  have hid : 𝟙 (ModuleCat.of R M) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  apply subsingleton_of_forall_eq 0
  intro e
  have he := Ext.comp_mk₀_id e
  rw [hid, Ext.mk₀_zero, Ext.comp_zero] at he
  exact he.symm

theorem regularSequenceDifferentialRange_top_subsingleton (rs : List R) :
    Subsingleton (regularSequenceDifferentialRange rs rs.length) := by
  let := W30.regularSequenceComplex_bounded rs (rs.length + 1) (Nat.lt_succ_self _)
  apply subsingleton_of_forall_eq 0
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

theorem regular_sequence_ext_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (X : ModuleCat.{u} R)
    (hv : ∀ i ≤ rs.length, Subsingleton (Ext X (ModuleCat.of R R) i)) :
    Subsingleton (Ext X (ModuleCat.of R (R ⧸ Ideal.ofList rs)) 0) := by
  have hfree (n : ℕ) (hn : n ≤ rs.length) :
      Subsingleton (Ext X ((W30.regularSequenceComplex rs).X n) n) := by
    let := W30.regularSequenceComplex_free rs n
    let := W30.regularSequenceComplex_finite rs n
    exact W31.ext_subsingleton_of_finite_free X n (hv n hn)
  have hend : Subsingleton
      (Ext X (regularSequenceDifferentialRange rs rs.length) (rs.length + 1)) := by
    let : Subsingleton (LinearMap.range
        ((W30.regularSequenceComplex rs).d (rs.length + 1) rs.length).hom) :=
      regularSequenceDifferentialRange_top_subsingleton rs
    exact ext_subsingleton_of_subsingleton_module X (rs.length + 1)
  have hrange : Subsingleton (Ext X (regularSequenceDifferentialRange rs 0) 1) := by
    apply Nat.decreasingInduction
      (motive := fun n _ =>
        Subsingleton (Ext X (regularSequenceDifferentialRange rs n) (n + 1)))
      (fun n hn ih => ?_) hend (Nat.zero_le rs.length)
    let f := ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom
    let g := ((W30.regularSequenceComplex rs).d (n + 1) n).hom
    have hex : LinearMap.range f = LinearMap.ker g :=
      (W31.regularSequenceAugmentation_spec rs hreg).2.2 n
    exact ext_subsingleton_of_shortExact X (differentialRangeShortComplex f g hex)
      (differentialRangeShortComplex_shortExact f g hex) (n + 1)
      (hfree (n + 1) (Nat.succ_le_of_lt hn)) ih
  let f := ((W30.regularSequenceComplex rs).d 1 0).hom
  let g := W31.regularSequenceAugmentation rs hreg
  have hex : LinearMap.range f = LinearMap.ker g :=
    (W31.regularSequenceAugmentation_spec rs hreg).2.1
  exact ext_subsingleton_of_shortExact X (augmentationRangeShortComplex f g hex)
    (augmentationRangeShortComplex_shortExact f g hex
      (W31.regularSequenceAugmentation_spec rs hreg).1) 0
    (hfree 0 (Nat.zero_le _)) hrange

theorem regular_sequence_associatedPrime_ext_obstruction [IsNoetherianRing R]
    (rs : List R) (hreg : RingTheory.Sequence.IsRegular R rs)
    (P : Ideal R) (hP : IsAssociatedPrime P (R ⧸ Ideal.ofList rs)) :
    ∃ i : ℕ, i ≤ rs.length ∧
      ¬ Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R R) i) := by
  classical
  by_contra h
  have hv (i : ℕ) (hi : i ≤ rs.length) :
      Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R R) i) := by
    by_contra hv
    exact h ⟨i, hi, hv⟩
  exact not_isAssociatedPrime_of_ext_zero P
    (regular_sequence_ext_zero rs hreg (ModuleCat.of R (R ⧸ P)) hv) hP

end PiExponentJets.W18

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceDualExactness
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open Module
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem regularSequenceComplex_dual_low_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n + 1 < rs.length) :
    LinearMap.range ((regularSequenceComplex rs).d (n + 1) n).hom.dualMap =
      LinearMap.ker ((regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap := by
  cases rs with
  | nil => simp at hn
  | cons r rs =>
    obtain ⟨hr, htail⟩ := (RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg
    have hJ : r • (⊤ : Submodule R R) = Ideal.span ({r} : Set R) := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul]
      exact Ideal.mul_top _
    change RingTheory.Sequence.IsRegular (R ⧸ (r • (⊤ : Submodule R R))) rs at htail
    rw [hJ] at htail
    let E := emptyKoszulComplex (R := R)
    have hb : ∀ k, 0 < k → Subsingleton (E.X k) :=
      fun k hk => regularSequenceComplex_bounded ([] : List R) k hk
    let P := scalarConeComplex E r
    let e : P.X 1 ≃ₗ[R] R :=
      (W31.scalarConeTopEquiv E r 0 hb).trans (LinearEquiv.refl R R)
    have hbound : ∀ k, 1 < k → Subsingleton (P.X k) :=
      scalarCone_bounded E r 0 hb
    have hinj : Function.Injective (P.d 1 0).hom.dualMap :=
      scalarCone_dual_zero_injective_of_regular E r hr
    have hlow : ∀ k, k < 0 → LinearMap.range (P.d (k + 1) k).hom.dualMap =
        LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap := by
      intro k hk
      omega
    have hI : LinearMap.range
        ((W31.topDualCoordinate e).toLinearMap.comp (P.d 1 0).hom.dualMap) =
          Ideal.span ({r} : Set R) :=
      scalarCone_first_top_dual_image E r hb (LinearEquiv.refl R R)
    have h := iterateScalarCones_dual_low_exact_q68 rs 0 P (Ideal.span {r})
      e hbound hinj hlow hI htail
    exact h n (by simp only [List.length_cons] at hn; omega)

end PiExponentSiegelAux.W30

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceHomZero
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module
variable {R : Type*} [CommRing R]

theorem quotient_dual_eq_zero_of_regular (I : Ideal R) (r : R) (hrI : r ∈ I)
    (hr : IsSMulRegular R r) (φ : Dual R (R ⧸ I)) : φ = 0 := by
  apply LinearMap.ext
  intro x
  apply hr
  change r • φ x = r • (0 : R)
  rw [smul_zero, ← φ.map_smul]
  have hx : r • x = 0 := by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I x
    change r • (Submodule.Quotient.mk a : R ⧸ I) = 0
    rw [← Submodule.Quotient.mk_smul I]
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    simpa only [smul_eq_mul, mul_comm] using I.smul_mem a hrI
  rw [hx, map_zero]

theorem regularSequenceQuotient_dual_subsingleton (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hne : rs ≠ []) :
    Subsingleton (Dual R (R ⧸ Ideal.ofList rs)) := by
  cases rs with
  | nil => exact (hne rfl).elim
  | cons r rs =>
    apply subsingleton_of_forall_eq 0
    intro φ
    apply quotient_dual_eq_zero_of_regular (Ideal.ofList (r :: rs)) r
    · exact Ideal.subset_span (by simp)
    · exact ((RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg).1

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceLowExt
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open CategoryTheory CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R]

theorem regularSequenceQuotientExt_positive_below_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n + 1 < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) (n + 1)) :=
  W31.regularSequenceQuotientExt_of_dual_exact rs hreg n
    (regularSequenceComplex_dual_low_exact rs hreg n hn)

theorem regularSequenceQuotientExt_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hne : rs ≠ []) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) 0) := by
  let := regularSequenceQuotient_dual_subsingleton rs hreg hne
  refine ⟨fun a b => Ext.homEquiv₀.injective ?_⟩
  apply ModuleCat.hom_ext
  exact Subsingleton.elim _ _

theorem regularSequenceQuotientExt_below_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) n) := by
  cases n with
  | zero =>
    apply regularSequenceQuotientExt_zero rs hreg
    intro h
    simp [h] at hn
  | succ n => exact regularSequenceQuotientExt_positive_below_length rs hreg n hn

theorem residueFieldExt_below_regular_length [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (n : ℕ) (hn : n < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) (ModuleCat.of R R) n) := by
  change Subsingleton (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R R) n)
  rw [← hmax]
  exact regularSequenceQuotientExt_below_length rs hreg n hn

end PiExponentSiegelAux.W30

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialLocalLowExt
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open CategoryTheory CategoryTheory.Abelian
universe u

theorem polynomialLocal_residueExt_below_height
    (K : Type u) [Field K] (n : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
    (i : ℕ) (hi : (i : ℕ∞) < Q.height) :
    Subsingleton (Ext
      (ModuleCat.of (Localization.AtPrime Q)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)))
      (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q)) i) := by
  obtain ⟨h, hh, xs, hlen, hreg, hmax⟩ :=
    PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height_q68 K n Q
  apply residueFieldExt_below_regular_length xs hreg hmax i
  rw [hlen]
  exact ENat.natCast_lt_natCast.mp (by simpa only [hh] using hi)

end PiExponentSiegelAux.W30

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularParameterSelection
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence CategoryTheory CategoryTheory.Abelian
namespace PiExponentSiegel.W58

variable (k : Type u) [Field k] (n : ℕ)
variable (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]

theorem polynomialLocal_regular_prefix_maximal_not_associated_q68_oai
    (rs : List (Localization.AtPrime P))
    (hreg : IsRegular (Localization.AtPrime P) rs)
    (hshort : (rs.length : ℕ∞) < P.height) :
    ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P ⧸ Ideal.ofList rs) := by
  intro hass
  obtain ⟨i, hi, hnonzero⟩ :=
    PiExponentJets.W18.regular_sequence_associatedPrime_ext_obstruction
      rs hreg (maximalIdeal (Localization.AtPrime P)) hass
  have hile : (i : ℕ∞) ≤ rs.length := by exact_mod_cast hi
  have hvanish := PiExponentSiegelAux.W30.polynomialLocal_residueExt_below_height
    k n P i (hile.trans_lt hshort)
  change Subsingleton (Ext
    (ModuleCat.of (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ maximalIdeal (Localization.AtPrime P)))
    (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) i) at hvanish
  exact hnonzero hvanish

end PiExponentSiegel.W58

end

end OAI
end

theorem solution.{u} : type_of% @OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated_q68_oai.{u} := @OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated_q68_oai.{u}
