-- Prove2me | solution 1 for OAI.ReverseLogKodaira.FiberChartSpecialization.local_specialization_regular
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:25:07.217699+00:00
-- url     : https://prove2.me/submissions/2da62a60-4236-49aa-a713-13e97315541d

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/FiberCharts.lean:L158-L225
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.FiberChartSpecialization.local_specialization_regular. The node keeps its source
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
import Theorems.Thm_OAI_ReverseLogKodaira_LocalCanonical_range_pluricanonicalPullback

-- ---- from OAI.AlgebraicGeometry.LogKodaira.FiberCharts ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

 

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

lemma exterior_fiber_target_tower
    (A B S C K : Type*) [CommRing A] [CommRing B] [CommRing S] [CommRing C] [CommRing K]
    [Algebra A B] [Algebra A S] [Algebra A C] [Algebra A K]
    [Algebra B C] [Algebra B K] [Algebra C K] [Algebra S C] [Algebra S K]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsScalarTower A B K] [IsScalarTower A S K]
    [IsScalarTower S C K] [IsScalarTower B C K] (r : ℕ) :
    ((exteriorDifferentialMap S S C K r).restrictScalars B).comp
      (exteriorDifferentialMap A S B C r) = exteriorDifferentialMap A S B K r := by
  have hd : ((KaehlerDifferential.map S S C K).restrictScalars B).comp
      (KaehlerDifferential.map A S B C) = KaehlerDifferential.map A S B K := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      KaehlerDifferential.map_D]
    rw [IsScalarTower.algebraMap_apply B C K]
  apply LinearMap.ext_on (exteriorPower.ιMulti_span B r (KaehlerDifferential A B))
  rintro _ ⟨v, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    exteriorDifferentialMap, exteriorScalarMap_wedge]
  congr 1
  funext i
  exact LinearMap.congr_fun hd (v i)

lemma specialization_target_tower
    (R A B S C K : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing C] [CommRing K]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra A K]
    [Algebra B C] [Algebra B K] [Algebra C K] [Algebra S C] [Algebra S K]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsScalarTower A B K] [IsScalarTower A S K]
    [IsScalarTower S C K] [IsScalarTower B C K]
    [Algebra.FormallySmooth A B] (n r m : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    ((pluricanonicalMap S S C K r m).restrictScalars B).comp
      (specializePluricanonical R A B S C n r m b c) =
      specializePluricanonical R A B S K n r m b c := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change pluricanonicalMap S S C K r m
      (specializePluricanonical R A B S C n r m b c (PiTensorProduct.tprod B v)) =
    specializePluricanonical R A B S K n r m b c (PiTensorProduct.tprod B v)
  simp only [specializePluricanonical, pluricanonicalMap,
    tensorScalarMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.coe_restrictScalars]
  congr 1
  funext i
  exact LinearMap.congr_fun (exterior_fiber_target_tower A B S C K r)
    (basedRelativeCanonicalEquiv R A B n r b c (v i))

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

theorem local_specialization_regular
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
      (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (t : Γ(X.scheme, V.1)), chartToFunctionField F.inclusion V.1 t ≠ 0 →
      ∀ q : Pluricanonical ℂ Γ(X.scheme, V.1) (n + F.variety.dimension) m,
        (chartToFunctionField F.inclusion V.1 t)^m •
          logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q ∈
        F.variety.regularPluriformLattice
          ⟨F.inclusion ⁻¹ᵁ V.1, (fiber_affine_chart_pushout f y F U hy V e).1⟩ m := by
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  intro hsm n m b c t ht q
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
  have hn := LinearMap.congr_fun
    (CanonicalSpecialization.specialization_target_tower ℂ A B ℂ C K
      n F.variety.dimension m b c) q
  have hcancel : (chartToFunctionField F.inclusion V.1 t)^m •
      logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q =
      CanonicalSpecialization.specializePluricanonical ℂ A B ℂ K
        n F.variety.dimension m b c q := by
    change (chartToFunctionField F.inclusion V.1 t)^m •
      (((chartToFunctionField F.inclusion V.1 t)^m)⁻¹ •
        CanonicalSpecialization.specializePluricanonical ℂ A B ℂ K
          n F.variety.dimension m b c q) = _
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero m ht), one_smul]
  rw [hcancel]
  have hmem : pluricanonicalMap ℂ ℂ C K F.variety.dimension m
      (CanonicalSpecialization.specializePluricanonical ℂ A B ℂ C
        n F.variety.dimension m b c q) ∈
      F.variety.regularPluriformLattice
        ⟨W, (fiber_affine_chart_pushout f y F U hy V e).1⟩ m := by
    change _ ∈ Submodule.span C _
    rw [← LocalCanonical.range_pluricanonicalPullback ℂ C K F.variety.dimension m]
    exact ⟨_, rfl⟩
  exact hn ▸ hmem

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

 

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
      (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (t : Γ(X.scheme, V.1)), chartToFunctionField F.inclusion V.1 t ≠ 0 →
      ∀ q : Pluricanonical ℂ Γ(X.scheme, V.1) (n + F.variety.dimension) m,
        (chartToFunctionField F.inclusion V.1 t)^m •
          logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q ∈
        F.variety.regularPluriformLattice
          ⟨F.inclusion ⁻¹ᵁ V.1, (fiber_affine_chart_pushout f y F U hy V e).1⟩ m := by
  first
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.local_specialization_regular f y F U hy V e
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.local_specialization_regular
    | (apply OAI.ReverseLogKodaira.FiberChartSpecialization.local_specialization_regular <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.FiberChartSpecialization.local_specialization_regular <;> assumption)
