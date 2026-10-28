-- Prove2me | solution 1 for OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:02:36.09196+00:00
-- url     : https://prove2.me/submissions/eaee7054-5916-425a-9a1c-d2a68656c53e

import Mathlib
import Definitions.Def_OAIQ068A019
import Theorems.Thm_OAI_PiExponentJets_W28_LocalIntersection_exists_cyclic_filtration_all_local_counts_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EndomorphismEulerAdditivity
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.EndomorphismEuler

section InducedMaps

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem kernelMap_injective (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (hf : Function.Injective f) :
    Function.Injective (kernelMap u v f comm) := by
  intro x y h
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val h

theorem cokernelMap_surjective (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (hf : Function.Surjective f) :
    Function.Surjective (cokernelMap u v f comm) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range v) y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨(LinearMap.range u).mkQ x, rfl⟩

end InducedMaps

section ActualSnake

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

variable (u₁ : M₁ →ₗ[A] M₁) (u₂ : M₂ →ₗ[A] M₂) (u₃ : M₃ →ₗ[A] M₃)
  (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hExact : Function.Exact f g)
  (hleft : f.comp u₁ = u₂.comp f) (hright : g.comp u₂ = u₃.comp g)
  (hf : Function.Injective f) (hg : Function.Surjective g)

include hExact hf in

theorem kernelMap_exact :
    Function.Exact (kernelMap u₁ u₂ f hleft) (kernelMap u₂ u₃ g hright) := by
  intro x
  constructor
  · intro hx
    have hgx : g x = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (hExact x).mp hgx
    have huy : u₁ y = 0 := by
      apply hf
      calc
        f (u₁ y) = u₂ (f y) := DFunLike.congr_fun hleft y
        _ = 0 := by rw [hy]; exact x.property
        _ = f 0 := (map_zero f).symm
    exact ⟨⟨y, huy⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact hExact.apply_apply_eq_zero (y : M₁)

include hExact hg in

theorem cokernelMap_exact :
    Function.Exact (cokernelMap u₁ u₂ f hleft) (cokernelMap u₂ u₃ g hright) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range u₂) x
  constructor
  · intro hx
    change (LinearMap.range u₃).mkQ (g x) = 0 at hx
    have hmem : g x ∈ LinearMap.range u₃ := (Submodule.Quotient.mk_eq_zero (LinearMap.range u₃)).mp hx
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨y, hy⟩ := hg z
    have hxy : g (x - u₂ y) = 0 := by
      rw [map_sub, show g (u₂ y) = u₃ (g y) from DFunLike.congr_fun hright y,
        hy, hz, sub_self]
    obtain ⟨w, hw⟩ := (hExact (x - u₂ y)).mp hxy
    refine ⟨(LinearMap.range u₁).mkQ w, ?_⟩
    change (LinearMap.range u₂).mkQ (f w) = (LinearMap.range u₂).mkQ x
    rw [hw, map_sub]
    have hz₂ : (LinearMap.range u₂).mkQ (u₂ y) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range u₂)).mpr ⟨y, rfl⟩
    rw [hz₂, sub_zero]
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range u₁) y
    change (LinearMap.range u₃).mkQ (g (f y)) = 0
    rw [hExact.apply_apply_eq_zero, map_zero]

theorem exact_kernel_connecting :
    Function.Exact (kernelMap u₂ u₃ g hright)
      (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg) := by
  exact SnakeLemma.exact_δ'_right
    (i₁ := u₁) (i₂ := u₂) (i₃ := u₃)
    (f₁ := f) (f₂ := g) (hf := hExact) (g₁ := f) (g₂ := g) (hg := hExact)
    (h₁ := hleft) (h₂ := hright)
    (ι₂ := (LinearMap.ker u₂).subtype) (hι₂ := LinearMap.exact_subtype_ker_map u₂)
    (ι₃ := (LinearMap.ker u₃).subtype) (hι₃ := LinearMap.exact_subtype_ker_map u₃)
    (π₁ := (LinearMap.range u₁).mkQ) (hπ₁ := LinearMap.exact_map_mkQ_range u₁)
    hg hf (kernelMap u₂ u₃ g hright) (by ext x; rfl)
    (Submodule.subtype_injective _)

theorem exact_connecting_cokernel :
    Function.Exact (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
      (cokernelMap u₁ u₂ f hleft) := by
  exact SnakeLemma.exact_δ'_left
    (i₁ := u₁) (i₂ := u₂) (i₃ := u₃)
    (f₁ := f) (f₂ := g) (hf := hExact) (g₁ := f) (g₂ := g) (hg := hExact)
    (h₁ := hleft) (h₂ := hright)
    (ι₃ := (LinearMap.ker u₃).subtype) (hι₃ := LinearMap.exact_subtype_ker_map u₃)
    (π₁ := (LinearMap.range u₁).mkQ) (hπ₁ := LinearMap.exact_map_mkQ_range u₁)
    (π₂ := (LinearMap.range u₂).mkQ) (hπ₂ := LinearMap.exact_map_mkQ_range u₂)
    hg hf (cokernelMap u₁ u₂ f hleft) (by ext x; rfl)
    (Submodule.mkQ_surjective _)

end ActualSnake

section LengthAlgebra

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem length_eq_kernel_add_range (f : M →ₗ[A] N) :
    Module.length A M = Module.length A (LinearMap.ker f) +
      Module.length A (LinearMap.range f) := by
  calc
    Module.length A M = Module.length A (LinearMap.ker f) +
        Module.length A (M ⧸ LinearMap.ker f) :=
      Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
        (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
        (LinearMap.exact_subtype_mkQ _)
    _ = _ := by rw [(LinearMap.quotKerEquivRange f).length_eq]

end LengthAlgebra

section SixTerm

variable {A X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [CommRing A]
  [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
  [AddCommGroup X₃] [Module A X₃] [AddCommGroup X₄] [Module A X₄]
  [AddCommGroup X₅] [Module A X₅] [AddCommGroup X₆] [Module A X₆]

theorem six_term_length_cross_add
    (a : X₁ →ₗ[A] X₂) (b : X₂ →ₗ[A] X₃) (c : X₃ →ₗ[A] X₄)
    (d : X₄ →ₗ[A] X₅) (e : X₅ →ₗ[A] X₆)
    (ha : Function.Injective a) (he : Function.Surjective e)
    (hab : Function.Exact a b) (hbc : Function.Exact b c)
    (hcd : Function.Exact c d) (hde : Function.Exact d e) :
    Module.length A X₅ + Module.length A X₁ + Module.length A X₃ =
      Module.length A X₂ + Module.length A X₄ + Module.length A X₆ := by
  have h₁ : Module.length A X₁ = Module.length A (LinearMap.range a) :=
    (LinearEquiv.ofInjective a ha).length_eq
  have h₂ : Module.length A X₂ = Module.length A (LinearMap.range a) +
      Module.length A (LinearMap.range b) := by
    rw [length_eq_kernel_add_range b, ← LinearMap.exact_iff.mp hab]
  have h₃ : Module.length A X₃ = Module.length A (LinearMap.range b) +
      Module.length A (LinearMap.range c) := by
    rw [length_eq_kernel_add_range c, ← LinearMap.exact_iff.mp hbc]
  have h₄ : Module.length A X₄ = Module.length A (LinearMap.range c) +
      Module.length A (LinearMap.range d) := by
    rw [length_eq_kernel_add_range d, ← LinearMap.exact_iff.mp hcd]
  have h₅ : Module.length A X₅ = Module.length A (LinearMap.range d) +
      Module.length A (LinearMap.range e) := by
    rw [length_eq_kernel_add_range e, ← LinearMap.exact_iff.mp hde]
  have h₆ : Module.length A (LinearMap.range e) = Module.length A X₆ := by
    rw [LinearMap.range_eq_top.mpr he]
    exact Module.length_top
  rw [h₁, h₂, h₃, h₄, h₅, ← h₆]
  ac_rfl

end SixTerm

section Euler

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

theorem endomorphism_euler_cross_add
    (u₁ : M₁ →ₗ[A] M₁) (u₂ : M₂ →ₗ[A] M₂) (u₃ : M₃ →ₗ[A] M₃)
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hExact : Function.Exact f g)
    (hleft : f.comp u₁ = u₂.comp f) (hright : g.comp u₂ = u₃.comp g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.length A (M₂ ⧸ LinearMap.range u₂) +
        Module.length A (LinearMap.ker u₁) + Module.length A (LinearMap.ker u₃) =
      Module.length A (LinearMap.ker u₂) + Module.length A (M₁ ⧸ LinearMap.range u₁) +
        Module.length A (M₃ ⧸ LinearMap.range u₃) := by
  exact six_term_length_cross_add
    (kernelMap u₁ u₂ f hleft) (kernelMap u₂ u₃ g hright)
    (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (cokernelMap u₁ u₂ f hleft) (cokernelMap u₂ u₃ g hright)
    (kernelMap_injective u₁ u₂ f hleft hf) (cokernelMap_surjective u₂ u₃ g hright hg)
    (kernelMap_exact (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) (f := f) (g := g)
      (hExact := hExact) (hleft := hleft) (hright := hright) (hf := hf))
    (exact_kernel_connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (exact_connecting_cokernel u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (cokernelMap_exact (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) (f := f) (g := g)
      (hExact := hExact) (hleft := hleft) (hright := hright) (hg := hg))

end Euler

end PiExponentJets.EndomorphismEuler

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionLength
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem finite_length_kernel_eq_cokernel
    (u : M →ₗ[A] M) (hfin : IsFiniteLength A M) :
    Module.length A (LinearMap.ker u) =
      Module.length A (M ⧸ LinearMap.range u) := by
  have hk := Module.length_eq_add_of_exact (LinearMap.ker u).subtype
    (LinearMap.ker u).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [u.quotKerEquivRange.length_eq] at hk
  have hr := Module.length_eq_add_of_exact (LinearMap.range u).subtype
    (LinearMap.range u).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hfiniteRange : Module.length A (LinearMap.range u) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (hfin.of_injective (Submodule.subtype_injective (LinearMap.range u)))
  apply ENat.add_left_injective_of_ne_top hfiniteRange
  calc
    Module.length A (LinearMap.ker u) + Module.length A (LinearMap.range u) =
        Module.length A M := hk.symm
    _ = Module.length A (M ⧸ LinearMap.range u) +
        Module.length A (LinearMap.range u) := hr.trans (add_comm _ _)

theorem kernel_length_eq_colon (I : Ideal A) (x : A) :
    Module.length A (LinearMap.ker (quotientMul I x)) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) :=
  (colonQuotientEquivKernel I x).length_eq.symm

theorem cokernel_length_eq_cut (I : Ideal A) (x : A) :
    Module.length A ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {x})) :=
  (cokernelEquivCut I x).length_eq

theorem finite_length_cut_eq_colon (I : Ideal A) (x : A)
    (hfin : IsFiniteLength A (A ⧸ I)) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) := by
  rw [← cokernel_length_eq_cut, ← kernel_length_eq_colon]
  exact (finite_length_kernel_eq_cokernel (quotientMul I x) hfin).symm

theorem regular_colon_length_zero (I : Ideal A) (x : A)
    (hregular : Function.Injective (quotientMul I x)) :
    Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) = 0 := by
  rw [← kernel_length_eq_colon, LinearMap.ker_eq_bot.mpr hregular]
  exact Module.length_bot

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionTransport
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem scalar_kernel_length_eq (e : M ≃ₗ[A] N) (x : A) :
    Module.length A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) =
      Module.length A (LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N))) :=
  (scalarKernelEquiv e x).length_eq

theorem scalar_cokernel_length_eq (e : M ≃ₗ[A] N) (x : A) :
    Module.length A (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) =
      Module.length A (N ⧸ LinearMap.range (x • (LinearMap.id : N →ₗ[A] N))) :=
  (scalarCokernelEquiv e x).length_eq

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionExactStep
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

theorem scalar_euler_cross_add (x : A)
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hExact : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    Module.length A (M₂ ⧸ LinearMap.range (x • (LinearMap.id : M₂ →ₗ[A] M₂))) +
        Module.length A (LinearMap.ker (x • (LinearMap.id : M₁ →ₗ[A] M₁))) +
        Module.length A (LinearMap.ker (x • (LinearMap.id : M₃ →ₗ[A] M₃))) =
      Module.length A (LinearMap.ker (x • (LinearMap.id : M₂ →ₗ[A] M₂))) +
        Module.length A (M₁ ⧸ LinearMap.range (x • (LinearMap.id : M₁ →ₗ[A] M₁))) +
        Module.length A (M₃ ⧸ LinearMap.range (x • (LinearMap.id : M₃ →ₗ[A] M₃))) := by
  apply EndomorphismEuler.endomorphism_euler_cross_add
    (x • LinearMap.id) (x • LinearMap.id) (x • LinearMap.id) f g hExact
  · ext m
    exact map_smul f x m
  · ext m
    exact map_smul g x m
  · exact hf
  · exact hg

theorem cyclic_ideal_step_cross_add (I : Ideal A) (f x : A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) +
        Module.length A (((I.colon {f}).colon {x}) ⧸
          (I.colon {f}).submoduleOf ((I.colon {f}).colon {x})) +
        Module.length A (((I ⊔ Ideal.span {f}).colon {x}) ⧸
          (I ⊔ Ideal.span {f}).submoduleOf ((I ⊔ Ideal.span {f}).colon {x})) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) +
        Module.length A (A ⧸ ((I.colon {f}) ⊔ Ideal.span {x})) +
        Module.length A (A ⧸ ((I ⊔ Ideal.span {f}) ⊔ Ideal.span {x})) := by
  let J : Ideal A := I ⊔ Ideal.span {f}
  let T : Submodule A (A ⧸ I) := Submodule.map I.mkQ J
  let eT : (A ⧸ I.colon {f}) ≃ₗ[A] T :=
    (W22.cyclicFactorEquiv I f).trans (W22.subquotientEquivImage I J)
  let eQ : ((A ⧸ I) ⧸ T) ≃ₗ[A] (A ⧸ J) :=
    Submodule.quotientQuotientEquivQuotient I J le_sup_left
  have h := scalar_euler_cross_add x T.subtype T.mkQ
    (LinearMap.exact_subtype_mkQ T) (Submodule.subtype_injective T)
    (Submodule.mkQ_surjective T)
  rw [scalar_kernel_length_eq eT.symm x, scalar_kernel_length_eq eQ x,
    scalar_cokernel_length_eq eT.symm x, scalar_cokernel_length_eq eQ x] at h
  change Module.length A ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) +
      Module.length A (LinearMap.ker (quotientMul (I.colon {f}) x)) +
      Module.length A (LinearMap.ker (quotientMul J x)) =
    Module.length A (LinearMap.ker (quotientMul I x)) +
      Module.length A ((A ⧸ I.colon {f}) ⧸ LinearMap.range (quotientMul (I.colon {f}) x)) +
      Module.length A ((A ⧸ J) ⧸ LinearMap.range (quotientMul J x)) at h
  simpa only [cokernel_length_eq_cut, kernel_length_eq_colon, J] using h

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_LocalIntersectionEulerFiltration
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A]

private theorem finite_cross_add_to_integer
    (a b c d e f : ℕ∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊤) (he : e ≠ ⊤) (hf : f ≠ ⊤)
    (h : a + b + c = d + e + f) :
    (a.toNat : ℤ) - d.toNat =
      ((e.toNat : ℤ) - b.toNat) + ((f.toNat : ℤ) - c.toNat) := by
  lift a to ℕ using ha
  lift b to ℕ using hb
  lift c to ℕ using hc
  lift d to ℕ using hd
  lift e to ℕ using he
  lift f to ℕ using hf
  have hn : a + b + c = d + e + f := by exact_mod_cast h
  simp only [ENat.toNat_natCast]
  omega

theorem cutEuler_cyclic_step (I : Ideal A) (f x : A)
    (hcut : ∀ J : Ideal A, Module.length A (A ⧸ (J ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ J : Ideal A,
      Module.length A ((J.colon {x}) ⧸ J.submoduleOf (J.colon {x})) ≠ ⊤) :
    cutEuler I x = cutEuler (I.colon {f}) x + cutEuler (I ⊔ Ideal.span {f}) x := by
  exact finite_cross_add_to_integer _ _ _ _ _ _
    (hcut I) (hker (I.colon {f})) (hker (I ⊔ Ideal.span {f}))
    (hker I) (hcut (I.colon {f})) (hcut (I ⊔ Ideal.span {f}))
    (cyclic_ideal_step_cross_add I f x)

theorem cutEuler_filtration (J : ℕ → Ideal A) (f : ℕ → A) (x : A) (n : ℕ)
    (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
    (hcut : ∀ I : Ideal A, Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ I : Ideal A,
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤) :
    cutEuler (J 0) x = (∑ i ∈ Finset.range n, cutEuler ((J i).colon {f i}) x) +
      cutEuler (J n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)),
      cutEuler_cyclic_step (J n) (f n) x hcut hker,
      ← hstep n (Nat.lt_succ_self n), Finset.sum_range_succ, add_assoc]

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionPrimeFactors
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem prime_quotientMul_injective (P : Ideal A) [P.IsPrime]
    (x : A) (hx : x ∉ P) : Function.Injective (quotientMul P x) := by
  have hx0 : Ideal.Quotient.mk P x ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hx
  intro y z hyz
  change x • y = x • z at hyz
  simp only [Algebra.smul_def] at hyz
  exact mul_left_cancel₀ hx0 hyz

theorem prime_colon_length_zero (P : Ideal A) [P.IsPrime]
    (x : A) (hx : x ∉ P) :
    Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x})) = 0 :=
  regular_colon_length_zero P x (prime_quotientMul_injective P x hx)

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionDimensionOne
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem maximal_factor_cut_eq_colon (P : Ideal A) [P.IsMaximal] (x : A) :
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
      Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x})) := by
  let : IsSimpleModule A (A ⧸ P) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  apply finite_length_cut_eq_colon P x
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_one A (A ⧸ P)]
  exact ENat.one_ne_top

theorem regular_not_mem_minimalPrime (x : A) (hx : x ∈ nonZeroDivisors A)
    (P : Ideal A) (hP : P ∈ minimalPrimes A) : x ∉ P := by
  exact fun hxP => Set.disjoint_left.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) hxP hx

theorem dimension_one_prime_factor_dichotomy
    [Ring.KrullDimLE 1 A] [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A)
    (P : Ideal A) [P.IsPrime] :
    (P ∈ minimalPrimes A ∧ Function.Injective (quotientMul P x)) ∨
    (P = IsLocalRing.maximalIdeal A ∧
      Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
        Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x}))) := by
  rcases (Ring.krullDimLE_one_iff.mp inferInstance) P inferInstance with hP | hP
  · exact Or.inl ⟨hP,
      prime_quotientMul_injective P x (regular_not_mem_minimalPrime x hx P hP)⟩
  · let : P.IsMaximal := hP
    exact Or.inr ⟨IsLocalRing.eq_maximalIdeal hP, maximal_factor_cut_eq_colon P x⟩

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ParameterKilledFiniteLength
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W06

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem isArtinianRing_quotient_parameter {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsArtinianRing (A ⧸ Ideal.span {x}) := by
  have hlength : IsFiniteLength A (A ⧸ Ideal.span {x}) :=
    isFiniteLength_quotient_span_singleton A hx
  have hart : IsArtinian A (A ⧸ Ideal.span {x}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).2
  exact isArtinian_of_tower A hart

variable {M : Type*} [AddCommGroup M] [Module A M]

theorem isFiniteLength_of_parameter_killed [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) (hkill : ∀ m : M, x • m = 0) :
    IsFiniteLength A M := by
  have ht : Module.IsTorsionBy A M x := fun {m} => hkill m
  have hs : Module.IsTorsionBySet A M (Ideal.span {x}) :=
    (Module.isTorsionBySet_span_singleton_iff x).mpr ht
  let : Module (A ⧸ Ideal.span {x}) M := hs.module
  let : IsScalarTower A (A ⧸ Ideal.span {x}) M := hs.isScalarTower
  let : IsArtinianRing (A ⧸ Ideal.span {x}) := isArtinianRing_quotient_parameter hx
  let : Module.Finite (A ⧸ Ideal.span {x}) M :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ Ideal.span {x}) M
  let : IsArtinian (A ⧸ Ideal.span {x}) M := inferInstance
  have hart : IsArtinian A M :=
    isArtinian_of_surjective_algebraMap (R := A ⧸ Ideal.span {x}) (S := A)
      (M := M) (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hart⟩

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in

theorem parameter_kills_mul_kernel (x : A) :
    ∀ m : LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M)), x • m = 0 := by
  intro m
  apply Subtype.ext
  change x • (m : M) = 0
  simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using m.property

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in

theorem parameter_kills_mul_cokernel (x : A) :
    ∀ m : M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M)), x • m = 0 := by
  have ht : Module.IsTorsionBy A
      (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) x :=
    (Module.isTorsionBy_quotient_iff _ x).mpr (fun m => ⟨m, rfl⟩)
  exact fun m => @ht m

theorem isFiniteLength_ker_parameter_mul [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) := by
  let : IsNoetherian A M := inferInstance
  let : Module.Finite A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) := inferInstance
  exact isFiniteLength_of_parameter_killed hx (parameter_kills_mul_kernel x)

theorem isFiniteLength_coker_parameter_mul [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) := by
  exact isFiniteLength_of_parameter_killed hx (parameter_kills_mul_cokernel x)

end PiExponentJets.W06

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_LocalIntersectionRegularEuler
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem regular_cut_length_ne_top (x : A) (hx : x ∈ nonZeroDivisors A) (I : Ideal A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤ := by
  rw [← cokernel_length_eq_cut]
  exact Module.length_ne_top_iff.mpr
    (W06.isFiniteLength_coker_parameter_mul (M := A ⧸ I) hx)

theorem regular_colon_length_ne_top (x : A) (hx : x ∈ nonZeroDivisors A) (I : Ideal A) :
    Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤ := by
  rw [← kernel_length_eq_colon]
  exact Module.length_ne_top_iff.mpr
    (W06.isFiniteLength_ker_parameter_mul (M := A ⧸ I) hx)

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem regular_colon_bot (x : A) (hx : x ∈ nonZeroDivisors A) :
    (⊥ : Ideal A).colon {x} = ⊥ := by
  ext a
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  exact mul_right_mem_nonZeroDivisors_eq_zero_iff hx

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem cutEuler_bot_regular (x : A) (hx : x ∈ nonZeroDivisors A) :
    cutEuler (⊥ : Ideal A) x =
      ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) := by
  have hz : Module.length A
      (((⊥ : Ideal A).colon {x}) ⧸ (⊥ : Ideal A).submoduleOf ((⊥ : Ideal A).colon {x})) = 0 := by
    rw [regular_colon_bot x hx]
    exact Module.length_eq_zero
  have hlen : Module.length A (A ⧸ ((⊥ : Ideal A) ⊔ Ideal.span {x})) =
      Module.length A (A ⧸ Ideal.span {x}) :=
    (Submodule.quotEquivOfEq _ _ (bot_sup_eq (Ideal.span {x}))).length_eq
  simp only [cutEuler, hz, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hlen

omit [IsNoetherianRing A] in
theorem cutEuler_prime_regular [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) (P : Ideal A) [P.IsPrime] :
    cutEuler P x = if P ∈ minimalPrimes A then
      ((Module.length A (A ⧸ (P ⊔ Ideal.span {x}))).toNat : ℤ) else 0 := by
  classical
  by_cases hp : P ∈ minimalPrimes A
  · have hz := prime_colon_length_zero P x (regular_not_mem_minimalPrime x hx P hp)
    simp [cutEuler, hp, hz]
  · rcases dimension_one_prime_factor_dichotomy x hx P with hmin | hmax
    · exact False.elim (hp hmin.1)
    · simp only [hp, ↓reduceIte, cutEuler, hmax.2, sub_self]

theorem exists_regular_onecut_sum_and_local_counts [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i < n, ((J i).colon {f i}).IsPrime) ∧
      (((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) =
        ∑ i ∈ Finset.range n, if (J i).colon {f i} ∈ minimalPrimes A then
          ((Module.length A (A ⧸ ((J i).colon {f i} ⊔ Ideal.span {x}))).toNat : ℤ) else 0) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  classical
  obtain ⟨n, J, f, hm, h0, hn, hs, hcounts⟩ :=
    exists_cyclic_filtration_all_local_counts_q68 (A := A)
  refine ⟨n, J, f, (fun i hi => (hs i hi).1), ?_, hcounts⟩
  have he := cutEuler_filtration J f x n (fun i hi => (hs i hi).2)
    (regular_cut_length_ne_top x hx) (regular_colon_length_ne_top x hx)
  rw [h0, hn, cutEuler_top, add_zero, cutEuler_bot_regular x hx] at he
  refine he.trans (Finset.sum_congr rfl ?_)
  intro i hi
  let : ((J i).colon {f i}).IsPrime := (hs i (Finset.mem_range.mp hi)).1
  exact cutEuler_prime_regular x hx ((J i).colon {f i})

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionMinimalSum
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [IsLocalRing A]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A] in
private theorem subtype_indicator_sum
    (S : Set (Ideal A)) [Fintype S] (P : Ideal A) (w : Ideal A → ℕ∞) :
    (∑ Q : S, if P = Q.val then w Q.val else 0) =
      if P ∈ S then w P else 0 := by
  classical
  by_cases hp : P ∈ S
  · rw [ite_eq_left hp]
    calc
      (∑ Q : S, if P = Q.val then w Q.val else 0) =
          (if P = P then w P else 0) := by
        apply Finset.sum_eq_single (⟨P, hp⟩ : S)
        · intro Q hQ hne
          have hne' : P ≠ Q.val := by
            intro h
            apply hne
            exact Subtype.ext h.symm
          simp only [hne', ↓reduceIte]
        · simp
      _ = w P := ite_eq_left rfl
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro Q hQ
    have hne : P ≠ Q.val := fun h => hp (h.symm ▸ Q.property)
    simp only [hne, ↓reduceIte]

theorem regular_ring_onecut_length_q68_oai (x : A) (hx : x ∈ nonZeroDivisors A) :
    Module.length A (A ⧸ Ideal.span {x}) =
      minimalPrimeCutSum (⊥ : Ideal A) x := by
  classical
  obtain ⟨n, J, f, hp, he, hcounts⟩ := exists_regular_onecut_sum_and_local_counts x hx
  let ps : ℕ → Ideal A := fun i => (J i).colon {f i}
  let w : Ideal A → ℕ∞ := fun P => Module.length A (A ⧸ (P ⊔ Ideal.span {x}))
  have hsumNat : (Module.length A (A ⧸ Ideal.span {x})).toNat =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then (w (ps i)).toNat else 0 := by
    exact_mod_cast he
  have hsumENat : ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℕ∞) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then ((w (ps i)).toNat : ℕ∞) else 0 := by
    exact_mod_cast hsumNat
  have hzeroCut : Module.length A (A ⧸ Ideal.span {x}) ≠ ⊤ := by
    exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton A hx)
  rw [ENat.natCast_toNat hzeroCut] at hsumENat
  have hsum : Module.length A (A ⧸ Ideal.span {x}) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := by
    refine hsumENat.trans (Finset.sum_congr rfl ?_)
    intro i hi
    split_ifs with hmin
    · exact ENat.natCast_toNat (regular_cut_length_ne_top x hx (ps i))
    · rfl
  let : Fintype ((⊥ : Ideal A).minimalPrimes) :=
    ((⊥ : Ideal A).finite_minimalPrimes_of_isNoetherianRing A).fintype
  have hterm (P : (⊥ : Ideal A).minimalPrimes) :
      (letI : P.val.IsPrime := P.property.1.1
       Module.length (Localization.AtPrime P.val)
          (Localization.AtPrime P.val ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P.val))) * w P.val) =
        ∑ i ∈ Finset.range n, if ps i = P.val then w P.val else 0 := by
    let : P.val.IsPrime := P.property.1.1
    rw [hcounts P.val P.property, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : ps i = P.val
    · simp only [ps] at h
      simp only [h, ↓reduceIte, one_mul, ps]
    · simp only [ps] at h
      simp only [h, ↓reduceIte, zero_mul, ps]
  calc
    Module.length A (A ⧸ Ideal.span {x}) =
        ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := hsum
    _ = ∑ i ∈ Finset.range n, ∑ P : (⊥ : Ideal A).minimalPrimes,
        if ps i = P.val then w P.val else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (subtype_indicator_sum ((⊥ : Ideal A).minimalPrimes) (ps i) w).symm
    _ = ∑ P : (⊥ : Ideal A).minimalPrimes, ∑ i ∈ Finset.range n,
        if ps i = P.val then w P.val else 0 := Finset.sum_comm
    _ = minimalPrimeCutSum (⊥ : Ideal A) x := by
      unfold minimalPrimeCutSum
      apply Finset.sum_congr rfl
      intro P hP
      exact (hterm P).symm

end PiExponentJets.W28.LocalIntersection

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length_q68_oai.{u_1} := @OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length_q68_oai.{u_1}
