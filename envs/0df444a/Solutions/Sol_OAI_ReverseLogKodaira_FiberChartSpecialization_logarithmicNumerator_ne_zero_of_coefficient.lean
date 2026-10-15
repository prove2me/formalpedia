-- Prove2me | solution 1 for OAI.ReverseLogKodaira.FiberChartSpecialization.logarithmicNumerator_ne_zero_of_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:23:38.018861+00:00
-- url     : https://prove2.me/submissions/44bd4506-cfd9-42f4-af6d-023d646c3b73

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/NonzeroFiber.lean:L134-L198
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.FiberChartSpecialization.logarithmicNumerator_ne_zero_of_coefficient. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_NonzeroFiber

-- ---- from OAI.AlgebraicGeometry.LogKodaira.BaseChange ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
open scoped TensorProduct
namespace ReverseLogKodaira.DifferentialBaseChange

section Linear
variable (A B M N : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

end Linear

section Differentials
variable (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

end Differentials

section LinearProofs
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

lemma lift_bijective_of_basis {I : Type*} (b : Module.Basis I A M)
    (c : Module.Basis I B N) (f : M →ₗ[A] N) (hf : ∀ i, f (b i) = c i) :
    Function.Bijective (f.liftBaseChange B) := by
  have he : f.liftBaseChange B = ((b.baseChange B).equiv c (Equiv.refl I)).toLinearMap := by
    apply (b.baseChange B).ext
    intro i
    rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply]
    simp [Module.Basis.baseChange_apply, hf]
  rw [he]
  exact ((b.baseChange B).equiv c (Equiv.refl I)).bijective

lemma tensor_bijective_of_basis {I : Type*}
    (b : Module.Basis I A M) (c : Module.Basis I B N)
    (f : M →ₗ[A] N) (hf : ∀ i, f (b i) = c i) (m : ℕ) :
    Function.Bijective ((tensorScalarMap A B M N f m).liftBaseChange B) := by
  classical
  apply lift_bijective_of_basis (Basis.piTensorProduct fun _ : Fin m => b)
    (Basis.piTensorProduct fun _ : Fin m => c)
  intro i
  simp only [Basis.piTensorProduct_apply, tensorScalarMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  change PiTensorProduct.tprod B (fun j => f (b (i j))) = PiTensorProduct.tprod B (fun j => c (i j))
  congr 1
  funext j
  exact hf _

end LinearProofs

section DifferentialProofs
variable (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

 

end DifferentialProofs

end ReverseLogKodaira.DifferentialBaseChange

end
end

end OAI

-- ---- from OAI.AlgebraicGeometry.LogKodaira.NonzeroFiber ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.CanonicalSpecialization
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

theorem specialize_ne_zero_of_coefficient
    (R A B S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [Algebra.FormallySmooth A B] (n r m : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (d : Module.Basis (Fin r) C (KaehlerDifferential S C))
    (hd : ∀ i, KaehlerDifferential.map A S B C (c i) = d i)
    (q : Pluricanonical R B (n + r) m)
    (hq : algebraMap B C (pluricanonicalCoordinate R A B n r m b c q) ≠ 0) :
    specializePluricanonical R A B S C n r m b c q ≠ 0 := by
  classical
  let e := (basedRelativeCanonicalEquiv R A B n r b c).trans (determinantCoordinate c)
  let bb : Module.Basis PUnit.{1} B (Canonical R B (n+r)) :=
    (Module.Basis.singleton PUnit.{1} B).map e.symm
  let cc : Module.Basis PUnit.{1} C (Canonical S C r) :=
    (Module.Basis.singleton PUnit.{1} C).map (determinantCoordinate d).symm
  have hf (i : PUnit.{1}) : specializeCanonical R A B S C n r b c (bb i) = cc i := by
    simp only [bb, cc, Module.Basis.map_apply, Module.Basis.singleton_apply]
    change exteriorDifferentialMap A S B C r
      (basedRelativeCanonicalEquiv R A B n r b c
        ((basedRelativeCanonicalEquiv R A B n r b c).symm
          ((determinantCoordinate c).symm 1))) = (determinantCoordinate d).symm 1
    rw [LinearEquiv.apply_symm_apply]
    change exteriorDifferentialMap A S B C r ((1 : B) • exteriorPower.ιMulti B r c) =
      (1 : C) • exteriorPower.ιMulti C r d
    simp only [one_smul, exteriorDifferentialMap, exteriorScalarMap_wedge]
    congr 1
    funext j
    exact hd j
  have hinj := (tensor_bijective_of_basis bb cc
    (specializeCanonical R A B S C n r b c) hf m).1
  intro hz
  have ht : (1 : C) ⊗ₜ[B] q = 0 := by
    apply hinj
    simpa only [specializePluricanonical, LinearMap.liftBaseChange_tmul, one_smul, map_zero] using hz
  have heq := congrArg (fun w => TensorProduct.rid B C
    (TensorProduct.congr (LinearEquiv.refl B C)
      (pluricanonicalCoordinate R A B n r m b c) w)) ht
  apply hq
  simpa only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.rid_tmul,
    map_zero, Algebra.smul_def, mul_one] using heq

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization

lemma tensorKaehlerEquiv_one_tmul
    (A B S C : Type*) [CommRing A] [CommRing B] [CommRing S] [CommRing C]
    [Algebra A B] [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C] [Algebra.IsPushout A S B C]
    (v : KaehlerDifferential A B) :
    KaehlerDifferential.tensorKaehlerEquiv A S B C (1 ⊗ₜ[B] v) =
      KaehlerDifferential.map A S B C v := by
  have hh : ((KaehlerDifferential.tensorKaehlerEquiv A S B C).toLinearMap.restrictScalars B).comp
      (TensorProduct.mk B C (KaehlerDifferential A B) 1) =
      KaehlerDifferential.map A S B C := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨a, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, TensorProduct.mk_apply,
      KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul, KaehlerDifferential.map_D]
  exact LinearMap.congr_fun hh v

lemma exists_compatible_cotangent_basis
    (A B S C K : Type*) [CommRing A] [CommRing B] [CommRing S]
    [CommRing C] [CommRing K]
    [Algebra A B] [Algebra A S] [Algebra A C] [Algebra A K]
    [Algebra B C] [Algebra B K] [Algebra C K] [Algebra S C] [Algebra S K]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsScalarTower A B K] [IsScalarTower A S K]
    [IsScalarTower S C K] [IsScalarTower B C K]
    [Algebra.IsPushout A S B C] [Algebra.FormallyEtale C K]
    (r : ℕ) (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    ∃ d : Module.Basis (Fin r) K (KaehlerDifferential S K),
      ∀ i, KaehlerDifferential.map A S B K (c i) = d i := by
  let dC := (c.baseChange C).map (KaehlerDifferential.tensorKaehlerEquiv A S B C)
  let d := (dC.baseChange K).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S C K)
  refine ⟨d, fun i => ?_⟩
  have hd : ((KaehlerDifferential.map S S C K).restrictScalars B).comp
      (KaehlerDifferential.map A S B C) = KaehlerDifferential.map A S B K := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨a, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      KaehlerDifferential.map_D]
    rw [IsScalarTower.algebraMap_apply B C K]
  simp only [d, dC, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, tensorKaehlerEquiv_one_tmul]
  exact (LinearMap.congr_fun hd (c i)).symm

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

 

theorem logarithmicNumerator_ne_zero_of_coefficient
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1)),
      letI := hsm
      ∀ (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (t : Γ(X.scheme, V.1)), chartToFunctionField F.inclusion V.1 t ≠ 0 →
      ∀ q : Pluricanonical ℂ Γ(X.scheme, V.1) (n + F.variety.dimension) m,
        chartToFunctionField F.inclusion V.1
          (pluricanonicalCoordinate ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1)
            n F.variety.dimension m b c q) ≠ 0 →
        logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q ≠ 0 := by
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  let : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
  intro hsm
  let := hsm
  intro n m b c t ht q hq
  let := hsm
  let W := F.inclusion ⁻¹ᵁ V.1
  let A := Γ(Y.scheme, U.1)
  let B := Γ(X.scheme, V.1)
  let C := Γ(F.variety.scheme, W)
  let K := F.variety.scheme.functionField
  let : Algebra A ℂ := (complexPointEvaluation y U.1 hy).toAlgebra
  let : Algebra A C := ((F.variety.constants W).comp
    (complexPointEvaluation y U.1 hy)).toAlgebra
  let : Algebra B C := (F.inclusion.app V.1).hom.toAlgebra
  let : Algebra A K := ((algebraMap ℂ K).comp
    (complexPointEvaluation y U.1 hy)).toAlgebra
  let : Algebra B K := (chartToFunctionField F.inclusion V.1).toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun a =>
    (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
  let : IsScalarTower A ℂ C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => by
    exact (congrArg (fun g : A ⟶ C => g a)
      (fiber_affine_chart_pushout f y F U hy V e).2.w).symm
  let : IsScalarTower A ℂ K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun a =>
    (fiber_chart_base_scalar f y F U.1 hy V.1 e a).symm
  let : IsScalarTower B C K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsPushout A ℂ B C :=
    CommRingCat.isPushout_iff_isPushout.mp (fiber_affine_chart_pushout f y F U hy V e).2.flip
  let : IsAffineOpen W := (fiber_affine_chart_pushout f y F U hy V e).1
  let : IsFractionRing C K := functionField_isFractionRing_of_isAffineOpen F.variety.scheme W
    (fiber_affine_chart_pushout f y F U hy V e).1
  let : Algebra.FormallyEtale C K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors C)
  obtain ⟨d, hd⟩ := exists_compatible_cotangent_basis A B ℂ C K F.variety.dimension c
  have hn := specialize_ne_zero_of_coefficient ℂ A B ℂ K n F.variety.dimension m b c d hd q hq
  change ((chartToFunctionField F.inclusion V.1 t)^m)⁻¹ •
    specializePluricanonical ℂ A B ℂ K n F.variety.dimension m b c q ≠ 0
  exact smul_ne_zero (inv_ne_zero (pow_ne_zero m ht)) hn

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.RelativeCharts

 

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.DifferentialBaseChange

end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety
open DifferentialBaseChange CanonicalSpecialization FiberChartSpecialization

 

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1)),
      letI := hsm
      ∀ (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (t : Γ(X.scheme, V.1)), chartToFunctionField F.inclusion V.1 t ≠ 0 →
      ∀ q : Pluricanonical ℂ Γ(X.scheme, V.1) (n + F.variety.dimension) m,
        chartToFunctionField F.inclusion V.1
          (pluricanonicalCoordinate ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1)
            n F.variety.dimension m b c q) ≠ 0 →
        logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q ≠ 0 := by
  first
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.logarithmicNumerator_ne_zero_of_coefficient f y F U hy V e
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.logarithmicNumerator_ne_zero_of_coefficient
    | (apply OAI.ReverseLogKodaira.FiberChartSpecialization.logarithmicNumerator_ne_zero_of_coefficient <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.FiberChartSpecialization.logarithmicNumerator_ne_zero_of_coefficient <;> assumption)
