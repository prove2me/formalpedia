-- Prove2me | solution 1 for OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:04:10.494416+00:00
-- url     : https://prove2.me/submissions/6b3bd3b4-75f8-439b-83ec-81e8aca051c7

import Mathlib
import Definitions.Def_OAIQ068A019

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulDualCone
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z W : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [Module R X] [Module R Y] [Module R Z] [Module R W]

theorem coneDifferential_dual_precomposition (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (α : Dual R Y) (β : Dual R Z) :
    (α.coprod β).comp (coneDifferential f g r) =
      (α.comp f).coprod (r • α - β.comp g) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change α (f x + r • y) + β (-g y) = α (f x) + (r • α - β.comp g) y
  change α (f x + r • y) + β (-g y) =
    α (f x) + (r • α y - β (g y))
  simp only [map_add, map_smul, map_neg, sub_eq_add_neg]
  abel

theorem coneDifferential_dual_equiv (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (dualProdDualEquivDual R X Y).toLinearMap.comp (dualConeDifferential f g r) =
      (coneDifferential f g r).dualMap.comp (dualProdDualEquivDual R Y Z).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨α, β⟩
  exact (coneDifferential_dual_precomposition f g r α β).symm

theorem dualConeDifferential_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R)
    (hhg : LinearMap.range h.dualMap = LinearMap.ker g.dualMap)
    (hgf : LinearMap.range g.dualMap = LinearMap.ker f.dualMap) :
    LinearMap.range (dualConeDifferential g h r) =
      LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    have hfg : f.dualMap (g.dualMap α) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap f.dualMap hgf) α
    have hgh : g.dualMap (h.dualMap β) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker h.dualMap g.dualMap hhg) β
    apply Prod.ext
    · exact hfg
    · change r • g.dualMap α - g.dualMap (r • α - h.dualMap β) = 0
      simp only [map_sub, map_smul, hgh, sub_zero, sub_self]
  · intro hab
    have ha : f.dualMap ab.1 = 0 := congrArg Prod.fst hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hamem : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgf]
      exact ha
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hamem
    have hcycle : g.dualMap (r • t - ab.2) = 0 := by
      simpa only [map_sub, map_smul, ht] using hb
    have hbmem : r • t - ab.2 ∈ LinearMap.range h.dualMap := by
      rw [hhg]
      exact hcycle
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hbmem
    refine ⟨(t, a), ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t - h.dualMap a = ab.2
      rw [ha]
      abel

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

theorem scalarConeTopBoundary_eval (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (r : R) (n : ℕ) (α : Module.Dual R (C.X (n + 1)))
    (β : Module.Dual R (C.X n)) (t : C.X (n + 1)) :
    (((W30.scalarConeComplex C r).d (n + 2) (n + 1)).hom.dualMap (α.coprod β)) (0, t) =
      r * α t - ((C.d (n + 1) n).hom.dualMap β) t := by
  have hd : (W30.scalarConeComplex C r).d (n + 2) (n + 1) =
      W30.scalarConeMap C r (n + 1) :=
    ChainComplex.of_d _ _ (n + 1)
  rw [hd]
  change α ((C.d (n + 2) (n + 1)).hom 0 + r • t) +
      β (-((C.d (n + 1) n).hom t)) = r * α t - β ((C.d (n + 1) n).hom t)
  simp only [map_zero, zero_add, map_smul, map_neg, smul_eq_mul, sub_eq_add_neg]

theorem scalarConeTopDualCoordinate_boundary
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (hbound : ∀ k, n + 1 < k → Subsingleton (C.X k))
    (e : C.X (n + 1) ≃ₗ[R] R)
    (α : Module.Dual R (C.X (n + 1))) (β : Module.Dual R (C.X n)) :
    scalarConeTopDualCoordinate C r (n + 1) hbound e
      (((W30.scalarConeComplex C r).d (n + 2) (n + 1)).hom.dualMap (α.coprod β)) =
      r * topDualCoordinate e α -
        topDualCoordinate e ((C.d (n + 1) n).hom.dualMap β) := by
  rw [scalarConeTopDualCoordinate_apply]
  exact scalarConeTopBoundary_eval C r n α β (e.symm 1)

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulDualTransport
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R A B C A' B' C' : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable [Module R A] [Module R B] [Module R C]
variable [Module R A'] [Module R B'] [Module R C']

theorem exact_of_equivalences (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B) (eC : C' ≃ₗ[R] C)
    (hf : eB.toLinearMap.comp f' = f.comp eA.toLinearMap)
    (hg : eC.toLinearMap.comp g' = g.comp eB.toLinearMap)
    (hex : LinearMap.range f' = LinearMap.ker g') :
    LinearMap.range f = LinearMap.ker g := by
  have hf_apply (a : A') : eB (f' a) = f (eA a) := LinearMap.congr_fun hf a
  have hg_apply (b : B') : eC (g' b) = g (eB b) := LinearMap.congr_fun hg b
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := eA.surjective a
    change g (f (eA a')) = 0
    rw [← hf_apply a', ← hg_apply (f' a')]
    have hz : g' (f' a') = 0 := by
      have hm : f' a' ∈ LinearMap.range f' := ⟨a', rfl⟩
      rw [hex] at hm
      exact hm
    rw [hz, map_zero]
  · intro hb
    obtain ⟨b', rfl⟩ := eB.surjective b
    have hz : g' b' = 0 := by
      apply eC.injective
      rw [map_zero, hg_apply b']
      exact hb
    have hm : b' ∈ LinearMap.range f' := by
      rw [hex]
      exact hz
    obtain ⟨a', ha'⟩ := hm
    refine ⟨eA a', ?_⟩
    rw [← hf_apply a', ha']

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_interior_exact
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (n : ℕ)
    (hlo : LinearMap.range (P.d (n + 1) n).hom.dualMap =
      LinearMap.ker (P.d (n + 2) (n + 1)).hom.dualMap)
    (hhi : LinearMap.range (P.d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker (P.d (n + 3) (n + 2)).hom.dualMap) :
    LinearMap.range ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap)
    (((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap)
    (dualConeDifferential (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r)
    (dualConeDifferential (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r)
    (dualProdDualEquivDual S (P.X (n + 1)) (P.X n))
    (dualProdDualEquivDual S (P.X (n + 2)) (P.X (n + 1)))
    (dualProdDualEquivDual S (P.X (n + 3)) (P.X (n + 2)))
  · have hd : (scalarConeComplex P r).d (n + 2) (n + 1) = scalarConeMap P r (n + 1) := by
      exact ChainComplex.of_d _ _ (n + 1)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r
  · have hd : (scalarConeComplex P r).d (n + 3) (n + 2) = scalarConeMap P r (n + 2) := by
      exact ChainComplex.of_d _ _ (n + 2)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r
  · exact dualConeDifferential_exact _ _ _ r hlo hhi

end PiExponentSiegelAux.W30

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

theorem dualConeBottom_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R)
    (hex : LinearMap.range g.dualMap = LinearMap.ker f.dualMap)
    (hinj : Function.Injective g.dualMap) :
    LinearMap.range (dualConeBottom g r) = LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  constructor
  · rintro ⟨α, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap f.dualMap hex) α
    · change r • g.dualMap α - g.dualMap (r • α) = 0
      rw [map_smul, sub_self]
  · intro hab
    have ha : f.dualMap ab.1 = 0 := congrArg Prod.fst hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hm : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hex]
      exact ha
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t = ab.2
      apply hinj
      rw [map_smul, ht]
      exact sub_eq_zero.mp hb

theorem dualConeBottom_injective (g : Y →ₗ[R] Z) (r : R)
    (hinj : Function.Injective g.dualMap) : Function.Injective (dualConeBottom g r) := by
  intro α β h
  exact hinj (congrArg Prod.fst h)

theorem dualConeBottom_endpoint_exact {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) (π : Dual R Y →ₗ[R] Q)
    (hfg : f.dualMap.comp g.dualMap = 0)
    (hgπ : LinearMap.range g.dualMap = LinearMap.ker π)
    (hinj : Function.Injective g.dualMap) (hr : IsSMulRegular Q r) :
    LinearMap.range (dualConeBottom g r) = LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  constructor
  · rintro ⟨α, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun hfg α
    · change r • g.dualMap α - g.dualMap (r • α) = 0
      rw [map_smul, sub_self]
  · intro hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hπg : π (g.dualMap ab.2) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap π hgπ) ab.2
    have hrπ : r • π ab.1 = 0 := by
      have h := congrArg π hb
      simpa only [map_sub, map_smul, hπg, sub_zero, map_zero] using h
    have hπa : π ab.1 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hm : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgπ]
      exact hπa
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t = ab.2
      apply hinj
      rw [map_smul, ht]
      exact sub_eq_zero.mp hb

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_one_exact (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hex : LinearMap.range (P.d 1 0).hom.dualMap =
      LinearMap.ker (P.d 2 1).hom.dualMap)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap) :
    LinearMap.range ((scalarConeComplex P r).d 1 0).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d 2 1).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d 1 0).hom.dualMap)
    (((scalarConeComplex P r).d 2 1).hom.dualMap)
    (dualConeBottom (P.d 1 0).hom r)
    (dualConeDifferential (P.d 2 1).hom (P.d 1 0).hom r)
    (LinearEquiv.refl S (Dual S (P.X 0)))
    (dualProdDualEquivDual S (P.X 1) (P.X 0))
    (dualProdDualEquivDual S (P.X 2) (P.X 1))
  · have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
    rw [hd]
    exact coneBottom_dual_equiv (P.d 1 0).hom r
  · have hd : (scalarConeComplex P r).d 2 1 = scalarConeMap P r 1 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 1
    rw [hd]
    exact coneDifferential_dual_equiv (P.d 2 1).hom (P.d 1 0).hom r
  · exact dualConeBottom_exact _ _ r hex hinj

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulDualEndpoint
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

theorem dualCone_endpoint_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R) (π : Dual R Y →ₗ[R] Q)
    (hfg : f.dualMap.comp g.dualMap = 0)
    (hgh : g.dualMap.comp h.dualMap = 0)
    (hhg : LinearMap.range h.dualMap = LinearMap.ker g.dualMap)
    (hgπ : LinearMap.range g.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range (dualConeDifferential g h r) =
      LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun hfg α
    · change r • g.dualMap α - g.dualMap (r • α - h.dualMap β) = 0
      have hz : g.dualMap (h.dualMap β) = 0 := LinearMap.congr_fun hgh β
      simp only [map_sub, map_smul, hz, sub_zero, sub_self]
  · intro hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hπg : π (g.dualMap ab.2) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap π hgπ) ab.2
    have hrπ : r • π ab.1 = 0 := by
      have h := congrArg π hb
      simpa only [map_sub, map_smul, hπg, sub_zero, map_zero] using h
    have hπa : π ab.1 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hamem : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgπ]
      exact hπa
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hamem
    have hcycle : g.dualMap (r • t - ab.2) = 0 := by
      simpa only [map_sub, map_smul, ht] using hb
    have hbmem : r • t - ab.2 ∈ LinearMap.range h.dualMap := by
      rw [hhg]
      exact hcycle
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hbmem
    refine ⟨(t, a), ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t - h.dualMap a = ab.2
      rw [ha]
      abel

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceAugmentation
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30

variable {R X Y : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]

theorem coneBottom_range_eq_sup (g : Y →ₗ[R] R) (r : R) (I : Ideal R)
    (hg : LinearMap.range g = I) :
    LinearMap.range (coneBottom g r) = I ⊔ Ideal.span {r} := by
  have heq : coneBottom g r = g.coprod (r • LinearMap.id) := rfl
  rw [heq, LinearMap.range_coprod, hg]
  congr 1
  ext z
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, Ideal.mem_span_singleton, dvd_def]
  exact exists_congr (fun _ => eq_comm)

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulTopAugmentation
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R A B C : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]

lemma range_comp_eq_of_surjective (f : B →ₗ[R] C) (g : A →ₗ[R] B)
    (hg : Function.Surjective g) : LinearMap.range (f.comp g) = LinearMap.range f := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨g a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hg b
    exact ⟨a, rfl⟩

theorem scalar_sub_range (e : A ≃ₗ[R] R) (g : B →ₗ[R] R) (r : R)
    (I : Ideal R) (hg : LinearMap.range g = I) :
    LinearMap.range
      (r • e.toLinearMap.comp (LinearMap.fst R A B) -
        g.comp (LinearMap.snd R A B)) = I ⊔ Ideal.span {r} := by
  let T : (A × B) →ₗ[R] (B × R) :=
    (-(LinearMap.snd R A B)).prod (e.toLinearMap.comp (LinearMap.fst R A B))
  have hT : Function.Surjective T := by
    rintro ⟨b, z⟩
    refine ⟨(e.symm z, -b), ?_⟩
    change (-(-b), e (e.symm z)) = (b, z)
    simp only [neg_neg, e.apply_symm_apply]
  have hmap : r • e.toLinearMap.comp (LinearMap.fst R A B) -
      g.comp (LinearMap.snd R A B) = (coneBottom g r).comp T := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change r • e a - g b = g (-b) + r • e a
    rw [map_neg]
    abel
  rw [hmap, range_comp_eq_of_surjective _ _ hT, coneBottom_range_eq_sup g r I hg]

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_top_dual_image
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (n : ℕ)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (e : P.X (n + 1) ≃ₗ[S] S) (I : Ideal S)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I) :
    LinearMap.range
      ((W31.scalarConeTopDualCoordinate P r (n + 1) hbound e).toLinearMap.comp
        ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap) =
      I ⊔ Ideal.span {r} := by
  let E := dualProdDualEquivDual S (P.X (n + 1)) (P.X n)
  let F := (W31.scalarConeTopDualCoordinate P r (n + 1) hbound e).toLinearMap.comp
    ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap
  have hmap : F.comp E.toLinearMap =
      r • (W31.topDualCoordinate e).toLinearMap.comp
          (LinearMap.fst S (Dual S (P.X (n + 1))) (Dual S (P.X n))) -
        ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap).comp
          (LinearMap.snd S (Dual S (P.X (n + 1))) (Dual S (P.X n))) := by
    apply LinearMap.ext
    rintro ⟨α, β⟩
    exact W31.scalarConeTopDualCoordinate_boundary P r n hbound e α β
  change LinearMap.range F = _
  rw [← range_comp_eq_of_surjective F E.toLinearMap E.surjective, hmap]
  exact scalar_sub_range (W31.topDualCoordinate e) _ r I hI

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

theorem coordinate_quotient_exact (f : A →ₗ[R] B) (e : B ≃ₗ[R] R)
    (I : Ideal R) (hI : LinearMap.range (e.toLinearMap.comp f) = I) :
    LinearMap.range f = LinearMap.ker (I.mkQ.comp e.toLinearMap) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    change I.mkQ (e (f a)) = 0
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    rw [← hI]
    exact ⟨a, rfl⟩
  · intro hb
    have hm : e b ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hb
    rw [← hI] at hm
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, e.injective ha⟩

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_zero_injective
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap) :
    Function.Injective ((scalarConeComplex P r).d 1 0).hom.dualMap := by
  have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
    ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
  rw [hd]
  change Function.Injective (coneBottom (P.d 1 0).hom r).dualMap
  intro α β h
  apply dualConeBottom_injective (P.d 1 0).hom r hinj
  apply (dualProdDualEquivDual S (P.X 1) (P.X 0)).injective
  have he (φ : Dual S (P.X 0)) :
      (dualProdDualEquivDual S (P.X 1) (P.X 0)) (dualConeBottom (P.d 1 0).hom r φ) =
        (coneBottom (P.d 1 0).hom r).dualMap φ :=
    LinearMap.congr_fun (coneBottom_dual_equiv (P.d 1 0).hom r) φ
  rw [he, he]
  exact h

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulDualStep
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open Module
universe u
variable {R : Type u} [CommRing R]

theorem chain_dual_comp_zero (P : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (P.d (n + 2) (n + 1)).hom.dualMap.comp (P.d (n + 1) n).hom.dualMap = 0 := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  intro x
  change α ((P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x)) = 0
  have hz : (P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x) = 0 :=
    LinearMap.congr_fun (chain_linear_comp_zero P n) x
  rw [hz, map_zero]

theorem scalarCone_dual_endpoint_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (π : Dual R (P.X (n + 2)) →ₗ[R] Q)
    (hlo : LinearMap.range (P.d (n + 1) n).hom.dualMap =
      LinearMap.ker (P.d (n + 2) (n + 1)).hom.dualMap)
    (hπ : LinearMap.range (P.d (n + 2) (n + 1)).hom.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap)
    (((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap)
    (dualConeDifferential (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r)
    (dualConeDifferential (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r)
    (dualProdDualEquivDual R (P.X (n + 1)) (P.X n))
    (dualProdDualEquivDual R (P.X (n + 2)) (P.X (n + 1)))
    (dualProdDualEquivDual R (P.X (n + 3)) (P.X (n + 2)))
  · have hd : (scalarConeComplex P r).d (n + 2) (n + 1) = scalarConeMap P r (n + 1) :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) (n + 1)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r
  · have hd : (scalarConeComplex P r).d (n + 3) (n + 2) = scalarConeMap P r (n + 2) :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) (n + 2)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r
  · exact dualCone_endpoint_exact _ _ _ r π
      (chain_dual_comp_zero P (n + 1)) (chain_dual_comp_zero P n) hlo hπ hr

theorem scalarCone_dual_one_endpoint_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (π : Dual R (P.X 1) →ₗ[R] Q)
    (hπ : LinearMap.range (P.d 1 0).hom.dualMap = LinearMap.ker π)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hr : IsSMulRegular Q r) :
    LinearMap.range ((scalarConeComplex P r).d 1 0).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d 2 1).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d 1 0).hom.dualMap)
    (((scalarConeComplex P r).d 2 1).hom.dualMap)
    (dualConeBottom (P.d 1 0).hom r)
    (dualConeDifferential (P.d 2 1).hom (P.d 1 0).hom r)
    (LinearEquiv.refl R (Dual R (P.X 0)))
    (dualProdDualEquivDual R (P.X 1) (P.X 0))
    (dualProdDualEquivDual R (P.X 2) (P.X 1))
  · have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
    rw [hd]
    exact coneBottom_dual_equiv (P.d 1 0).hom r
  · have hd : (scalarConeComplex P r).d 2 1 = scalarConeMap P r 1 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 1
    rw [hd]
    exact coneDifferential_dual_equiv (P.d 2 1).hom (P.d 1 0).hom r
  · exact dualConeBottom_endpoint_exact _ _ r π (chain_dual_comp_zero P 0) hπ hinj hr

theorem scalarCone_dual_low_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (π : Dual R (P.X (n + 1)) →ₗ[R] Q)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hπ : LinearMap.range (P.d (n + 1) n).hom.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    ∀ k, k < n + 1 →
      LinearMap.range ((scalarConeComplex P r).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((scalarConeComplex P r).d (k + 2) (k + 1)).hom.dualMap := by
  intro k hk
  by_cases hkn : k < n
  · cases k with
    | zero => exact scalarCone_dual_one_exact P r (hlow 0 hkn) hinj
    | succ k =>
      exact scalarCone_dual_interior_exact P r k (hlow k (by omega))
        (hlow (k + 1) hkn)
  · have hkn : k = n := by omega
    subst k
    cases n with
    | zero => exact scalarCone_dual_one_endpoint_exact P r π hπ hinj hr
    | succ n =>
      exact scalarCone_dual_endpoint_exact P r n π (hlow n (by omega)) hπ hr

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceQuotientTail
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.RegularSequenceQuotientTail
open RingTheory.Sequence
open scoped Pointwise

variable {R : Type*} [CommRing R]

theorem regular_quotient_cons_iff (I : Ideal R) (r : R) (rs : List R) :
    IsRegular (R ⧸ I) (r :: rs) ↔
      IsSMulRegular (R ⧸ I) r ∧
        IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs := by
  rw [isRegular_cons_iff]
  exact and_congr_right' ((quotientTailEquiv I r).isRegular_congr rs)

theorem regular_quotient_tail (I : Ideal R) (r : R) (rs : List R)
    (h : IsRegular (R ⧸ I) (r :: rs)) :
    IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs :=
  ((regular_quotient_cons_iff I r rs).mp h).2

end PiExponentJets.RegularSequenceQuotientTail

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

theorem iterateScalarCones_dual_low_exact_q68_oai (rs : List R) (n : ℕ)
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (I : Ideal R)
    (e : P.X (n + 1) ≃ₗ[R] R)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I)
    (hreg : RingTheory.Sequence.IsRegular (R ⧸ I) rs) :
    ∀ k, k + 1 < n + 1 + rs.length →
      LinearMap.range ((iterateScalarCones P rs).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((iterateScalarCones P rs).d (k + 2) (k + 1)).hom.dualMap := by
  induction rs generalizing n P I with
  | nil =>
    intro k hk
    exact hlow k (by simpa using hk)
  | cons r rs ih =>
    let P' := scalarConeComplex P r
    let I' := I ⊔ Ideal.span {r}
    let e' : P'.X (n + 2) ≃ₗ[R] R :=
      (W31.scalarConeTopEquiv P r (n + 1) hbound).trans e
    let π : Dual R (P.X (n + 1)) →ₗ[R] (R ⧸ I) :=
      I.mkQ.comp (W31.topDualCoordinate e).toLinearMap
    have hπ : LinearMap.range (P.d (n + 1) n).hom.dualMap = LinearMap.ker π :=
      coordinate_quotient_exact _ (W31.topDualCoordinate e) I hI
    have hr : IsSMulRegular (R ⧸ I) r :=
      ((RingTheory.Sequence.isRegular_cons_iff (R ⧸ I) r rs).mp hreg).1
    have htail : RingTheory.Sequence.IsRegular (R ⧸ I') rs :=
      PiExponentJets.RegularSequenceQuotientTail.regular_quotient_tail I r rs hreg
    have hbound' : ∀ k, n + 2 < k → Subsingleton (P'.X k) :=
      scalarCone_bounded P r (n + 1) hbound
    have hinj' : Function.Injective (P'.d 1 0).hom.dualMap :=
      scalarCone_dual_zero_injective P r hinj
    have hlow' : ∀ k, k < n + 1 → LinearMap.range (P'.d (k + 1) k).hom.dualMap =
        LinearMap.ker (P'.d (k + 2) (k + 1)).hom.dualMap :=
      scalarCone_dual_low_exact P r n π hinj hlow hπ hr
    have hI' : LinearMap.range
        ((W31.topDualCoordinate e').toLinearMap.comp (P'.d (n + 2) (n + 1)).hom.dualMap) = I' :=
      scalarCone_top_dual_image P r n hbound e I hI
    have h := ih (n + 1) P' I' e' hbound' hinj' hlow' hI' htail
    intro k hk
    exact h k (by simp only [List.length_cons] at hk; omega)

end PiExponentSiegelAux.W30

end

end OAI
end

theorem solution.{u} : type_of% @OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact_q68_oai.{u} := @OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact_q68_oai.{u}
