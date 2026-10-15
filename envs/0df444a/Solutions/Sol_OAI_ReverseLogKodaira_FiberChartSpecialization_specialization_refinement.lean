-- Prove2me | solution 1 for OAI.ReverseLogKodaira.FiberChartSpecialization.specialization_refinement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:26:39.976258+00:00
-- url     : https://prove2.me/submissions/8127fe9e-a5d3-441e-b0e3-9f963c30955d

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/FiberCharts.lean:L266-L342
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.FiberChartSpecialization.specialization_refinement. The node keeps its source
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
import Theorems.Thm_OAI_ReverseLogKodaira_BasedRelativeCanonical_based_relative_canonical_naturality
import Theorems.Thm_OAI_ReverseLogKodaira_LogarithmicSpecialization_logarithmic_specialization_equation_independent

-- ---- from OAI.AlgebraicGeometry.LogKodaira.Specialization ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

 
end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

lemma differential_map_fiber_tower
    (A B B' S C : Type*) [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] (x : KaehlerDifferential A B) :
    KaehlerDifferential.map A S B' C (KaehlerDifferential.map A A B B' x) =
      KaehlerDifferential.map A S B C x := by
  have h : ((KaehlerDifferential.map A S B' C).restrictScalars B).comp
      (KaehlerDifferential.map A A B B') = KaehlerDifferential.map A S B C := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      KaehlerDifferential.map_D]
    rw [IsScalarTower.algebraMap_apply B B' C]
  exact LinearMap.congr_fun h x

lemma exterior_map_fiber_tower
    (A B B' S C : Type*) [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] (r : ℕ) :
    ((exteriorDifferentialMap A S B' C r).restrictScalars B).comp
      (exteriorDifferentialMap A A B B' r) = exteriorDifferentialMap A S B C r := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span B r (KaehlerDifferential A B))
  rintro _ ⟨v, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    exteriorDifferentialMap, exteriorScalarMap_wedge]
  congr 1
  funext i
  exact differential_map_fiber_tower A B B' S C (v i)

lemma canonical_specialization_naturality
    (R A B B' S C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A B'] [Algebra R B'] [IsScalarTower R A B']
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower R B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A B']
    (n r : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (c' : Module.Basis (Fin r) B' (KaehlerDifferential A B')) :
    ((specializeCanonical R A B' S C n r b c').restrictScalars B).comp
        (exteriorDifferentialMap R R B B' (n + r)) =
      specializeCanonical R A B S C n r b c := by
  apply LinearMap.ext
  intro x
  have hnat := LinearMap.congr_fun
    (based_relative_canonical_naturality R A B B' n r b c c') x
  have hcomp := LinearMap.congr_fun (exterior_map_fiber_tower A B B' S C r)
    (basedRelativeCanonicalEquiv R A B n r b c x)
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe] at hnat hcomp
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    specializeCanonical, LinearEquiv.coe_coe]
  rw [hnat, hcomp]

 

theorem pluricanonical_specialization_naturality
    (R A B B' S C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A B'] [Algebra R B'] [IsScalarTower R A B']
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower R B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A B']
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (c' : Module.Basis (Fin r) B' (KaehlerDifferential A B')) :
    ((specializePluricanonical R A B' S C n r m b c').restrictScalars B).comp
        (pluricanonicalMap R R B B' (n + r) m) =
      specializePluricanonical R A B S C n r m b c := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change specializePluricanonical R A B' S C n r m b c'
      (pluricanonicalMap R R B B' (n + r) m (PiTensorProduct.tprod B v)) =
    specializePluricanonical R A B S C n r m b c (PiTensorProduct.tprod B v)
  simp only [specializePluricanonical, pluricanonicalMap,
    tensorScalarMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.coe_restrictScalars]
  change PiTensorProduct.tprod C (fun i => specializeCanonical R A B' S C n r b c'
      (exteriorDifferentialMap R R B B' (n + r) (v i))) =
    PiTensorProduct.tprod C (fun i => specializeCanonical R A B S C n r b c (v i))
  congr 1
  funext i
  exact LinearMap.congr_fun
    (canonical_specialization_naturality R A B B' S C n r b c c') (v i)

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FractionalCanonical
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.FractionalCanonical

namespace ReverseLogKodaira.LogarithmicSpecialization
-- [generator] trimmed: open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization

 

 

end ReverseLogKodaira.LogarithmicSpecialization

namespace ReverseLogKodaira.LogarithmicSpecialization
-- [generator] trimmed: open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization

lemma pluricanonical_map_tower
    (R B B' K : Type*) [CommRing R] [CommRing B] [CommRing B'] [CommRing K]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra R K] [Algebra B K] [Algebra B' K]
    [IsScalarTower R B K] [IsScalarTower R B' K] [IsScalarTower B B' K]
    (n m : ℕ) :
    ((pluricanonicalMap R R B' K n m).restrictScalars B).comp
      (pluricanonicalMap R R B B' n m) = pluricanonicalMap R R B K n m := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change pluricanonicalMap R R B' K n m
      (pluricanonicalMap R R B B' n m (PiTensorProduct.tprod B v)) =
    pluricanonicalMap R R B K n m (PiTensorProduct.tprod B v)
  simp only [pluricanonicalMap, tensorScalarMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars]
  congr 1
  funext i
  exact LinearMap.congr_fun (exterior_map_fiber_tower R B B' R K n) (v i)

lemma logarithmicPullback_naturality
    (R B B' K : Type*) [CommRing R] [CommRing B] [CommRing B'] [Field K]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra R K] [Algebra B K] [Algebra B' K]
    [IsScalarTower R B K] [IsScalarTower R B' K] [IsScalarTower B B' K]
    (n m : ℕ) (t : B) (u : Pluricanonical R B n m) :
    logarithmicPullback R B' K n m (algebraMap B B' t)
      (pluricanonicalMap R R B B' n m u) = logarithmicPullback R B K n m t u := by
  have h := LinearMap.congr_fun (pluricanonical_map_tower R B B' K n m) u
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h
  simp only [logarithmicPullback, LinearMap.smul_apply,
    ← IsScalarTower.algebraMap_apply B B' K, h]

lemma logarithmicSpecialize_naturality
    (R A B B' S C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A B'] [Algebra R B'] [IsScalarTower R A B']
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower R B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A B']
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (c' : Module.Basis (Fin r) B' (KaehlerDifferential A B'))
    (t : B) (u : Pluricanonical R B (n + r) m) :
    logarithmicSpecialize R A B' S C n r m b c' (algebraMap B B' t)
      (pluricanonicalMap R R B B' (n + r) m u) =
    logarithmicSpecialize R A B S C n r m b c t u := by
  have h := LinearMap.congr_fun
    (pluricanonical_specialization_naturality R A B B' S C n r m b c c') u
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h
  simp only [logarithmicSpecialize, LinearMap.smul_apply,
    ← IsScalarTower.algebraMap_apply B B' C, h]

 

end ReverseLogKodaira.LogarithmicSpecialization

namespace ReverseLogKodaira.LogarithmicSpecialization
-- [generator] trimmed: open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization

 

end ReverseLogKodaira.LogarithmicSpecialization

end

end OAI

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

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma chartToFunctionField_restrict
    {X F : SmoothProjectiveVariety} (i : F.scheme ⟶ X.scheme)
    (V V' : X.scheme.Opens) (h : V' ≤ V)
    [Nonempty (i ⁻¹ᵁ V)] [Nonempty (i ⁻¹ᵁ V')] (a : Γ(X.scheme, V)) :
    chartToFunctionField i V' (X.scheme.presheaf.map (homOfLE h).op a) =
      chartToFunctionField i V a := by
  have hn := congrArg (fun g : Γ(X.scheme, V) ⟶ Γ(F.scheme, i ⁻¹ᵁ V') => g a)
    (i.naturality (homOfLE h).op)
  change F.scheme.germToFunctionField (i ⁻¹ᵁ V')
    (i.app V' (X.scheme.presheaf.map (homOfLE h).op a)) = _
  have hn' : i.app V' (X.scheme.presheaf.map (homOfLE h).op a) =
      F.scheme.presheaf.map
        (homOfLE (show i ⁻¹ᵁ V' ≤ i ⁻¹ᵁ V from fun z hz => h hz)).op (i.app V a) := hn
  rw [hn']
  exact F.scheme.presheaf.germ_res_apply
    (homOfLE (show i ⁻¹ᵁ V' ≤ i ⁻¹ᵁ V from fun z hz => h hz))
    (genericPoint F.scheme) _ (i.app V a)

lemma constants_restrict (X : SmoothProjectiveVariety)
    (V V' : X.scheme.Opens) (h : V' ≤ V) [Nonempty V] [Nonempty V'] (a : ℂ) :
    X.scheme.presheaf.map (homOfLE h).op (X.constants V a) = X.constants V' a := by
  apply X.scheme.germToFunctionField_injective V'
  change algebraMap Γ(X.scheme, V') X.scheme.functionField
      (X.scheme.presheaf.map (homOfLE h).op (X.constants V a)) =
    algebraMap Γ(X.scheme, V') X.scheme.functionField (X.constants V' a)
  exact (X.scheme.presheaf.germ_res_apply (homOfLE h) (genericPoint X.scheme) _ _).trans
    ((X.germ_constants V a).trans (X.germ_constants V' a).symm)

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

 

theorem specialization_refinement
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V V' : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1) (hV : V'.1 ≤ V.1)
    [Nonempty V.1] [Nonempty V'.1]
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] [Nonempty (F.inclusion ⁻¹ᵁ V'.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V'.1) :=
      (f.hom.appLE U.1 V'.1 (hV.trans e)).hom.toAlgebra
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
      (hsm' : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V'.1))
      (n r m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin r) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (c' : Module.Basis (Fin r) Γ(X.scheme, V'.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V'.1)))
      (t : Γ(X.scheme, V.1)) (t' : Γ(X.scheme, V'.1)),
      chartToFunctionField F.inclusion V.1 t ≠ 0 →
      chartToFunctionField F.inclusion V'.1 t' ≠ 0 →
      ∀ (q : Pluricanonical ℂ Γ(X.scheme, V.1) (n+r) m)
        (q' : Pluricanonical ℂ Γ(X.scheme, V'.1) (n+r) m),
      logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField (n+r) m t q =
        logarithmicPullback ℂ Γ(X.scheme, V'.1) X.scheme.functionField (n+r) m t' q' →
      logarithmicNumerator f y F U hy V e hsm n r m b c t q =
        logarithmicNumerator f y F U hy V' (hV.trans e) hsm' n r m b c' t' q' := by
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V'.1) :=
    (f.hom.appLE U.1 V'.1 (hV.trans e)).hom.toAlgebra
  intro hsm hsm' n r m b c c' t t' ht ht' q q' heq
  let := hsm
  let := hsm'
  let A := Γ(Y.scheme, U.1)
  let B := Γ(X.scheme, V.1)
  let B' := Γ(X.scheme, V'.1)
  let K := X.scheme.functionField
  let C := F.variety.scheme.functionField
  let : Algebra B B' := (X.scheme.presheaf.map (homOfLE hV).op).hom.toAlgebra
  let : Algebra A ℂ := (complexPointEvaluation y U.1 hy).toAlgebra
  let : Algebra A C := ((algebraMap ℂ C).comp
    (complexPointEvaluation y U.1 hy)).toAlgebra
  let : Algebra B C := (chartToFunctionField F.inclusion V.1).toAlgebra
  let : Algebra B' C := (chartToFunctionField F.inclusion V'.1).toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun a =>
    (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
  let : IsScalarTower ℂ A B' := IsScalarTower.of_algebraMap_eq fun a =>
    (appLE_constants f.hom f.over_base U.1 V'.1 (hV.trans e) a).symm
  let : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a =>
    (congrArg (fun g : A ⟶ B' => g a)
      (f.hom.appLE_map e (homOfLE hV).op)).symm
  let : IsScalarTower ℂ B B' := IsScalarTower.of_algebraMap_eq fun a =>
    (constants_restrict X V.1 V'.1 hV a).symm
  let : IsScalarTower B B' K := IsScalarTower.of_algebraMap_eq fun a =>
    (X.scheme.presheaf.germ_res_apply (homOfLE hV) (genericPoint X.scheme) _ a).symm
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a =>
    (fiber_chart_base_scalar f y F U.1 hy V.1 e a).symm
  let : IsScalarTower A B' C := IsScalarTower.of_algebraMap_eq fun a =>
    (fiber_chart_base_scalar f y F U.1 hy V'.1 (hV.trans e) a).symm
  let : IsScalarTower A ℂ C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower B B' C := IsScalarTower.of_algebraMap_eq fun a =>
    (chartToFunctionField_restrict F.inclusion V.1 V'.1 hV a).symm
  let := functionField_isFractionRing_of_isAffineOpen X.scheme V'.1 V'.2
  have hpb : logarithmicPullback ℂ B' K (n+r) m (algebraMap B B' t)
      (pluricanonicalMap ℂ ℂ B B' (n+r) m q) = logarithmicPullback ℂ B' K (n+r) m t' q' :=
    (logarithmicPullback_naturality ℂ B B' K (n+r) m t q).trans heq
  have htref : algebraMap B' C (algebraMap B B' t) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply B B' C]
    exact ht
  have he := logarithmic_specialization_equation_independent ℂ A B' K ℂ C
    n r m b c' (algebraMap B B' t) t' htref ht'
    (pluricanonicalMap ℂ ℂ B B' (n+r) m q) q' hpb
  have hn := logarithmicSpecialize_naturality ℂ A B B' ℂ C n r m b c c' t q
  exact hn.symm.trans he

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V V' : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1) (hV : V'.1 ≤ V.1)
    [Nonempty V.1] [Nonempty V'.1]
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] [Nonempty (F.inclusion ⁻¹ᵁ V'.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V'.1) :=
      (f.hom.appLE U.1 V'.1 (hV.trans e)).hom.toAlgebra
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
      (hsm' : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V'.1))
      (n r m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin r) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (c' : Module.Basis (Fin r) Γ(X.scheme, V'.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V'.1)))
      (t : Γ(X.scheme, V.1)) (t' : Γ(X.scheme, V'.1)),
      chartToFunctionField F.inclusion V.1 t ≠ 0 →
      chartToFunctionField F.inclusion V'.1 t' ≠ 0 →
      ∀ (q : Pluricanonical ℂ Γ(X.scheme, V.1) (n+r) m)
        (q' : Pluricanonical ℂ Γ(X.scheme, V'.1) (n+r) m),
      logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField (n+r) m t q =
        logarithmicPullback ℂ Γ(X.scheme, V'.1) X.scheme.functionField (n+r) m t' q' →
      logarithmicNumerator f y F U hy V e hsm n r m b c t q =
        logarithmicNumerator f y F U hy V' (hV.trans e) hsm' n r m b c' t' q' := by
  first
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.specialization_refinement f y F U hy V V' e hV
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.specialization_refinement
    | (apply OAI.ReverseLogKodaira.FiberChartSpecialization.specialization_refinement <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.FiberChartSpecialization.specialization_refinement <;> assumption)
