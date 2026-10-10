-- Prove2me | solution 1 for MazurTransfer.presentation_ratio_principal_over_perfect_field
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T22:58:03.61534+00:00
-- url     : https://prove2.me/submissions/847f1776-d2c1-49fb-b748-6e3633ed4ee2

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete helper proofs adapted from official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: actual divisor presentations over a perfect field with
the full constant-field property explicit. Named downstream consumer:
the unchanged order-13 arithmetic Picard group correspondence.
Original public statements are unchanged; no private implementation imports.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
universe u
namespace MazurTransfer.PublicPresentationRatioHelpers
open WithZero
theorem exists_not_mem_placesOf {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (U : X.Opens) (hU : IsAffineOpen U) [hUne : Nonempty U] :
    letI := (baseToFunctionField x).toAlgebra
    ∃ v₀ : Place K X.functionField, v₀ ∉ placesOf x U := by
  letI := (baseToFunctionField x).toAlgebra
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one x
  have hne : U ≠ ⊤ := by
    intro h
    apply hNA
    have hT : IsAffineOpen (⊤ : X.Opens) := h ▸ hU
    haveI : IsAffine (⊤ : X.Opens) := hT
    exact IsAffine.of_isIso X.topIso.inv
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ U := by
    by_contra hall
    exact hne (eq_top_iff.mpr fun z _ => by_contra fun hz => hall ⟨z, hz⟩)
  have hUne' : ((U : Set X)).Nonempty := let ⟨⟨z, hz⟩⟩ := hUne; ⟨z, hz⟩
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hUne')
  have hyη : y ≠ genericPoint X := fun h => hy (h ▸ hη)
  obtain ⟨v₀, hv₀⟩ := exists_place_range_stalk_eq x y (isClosed_singleton_of_ne_genericPoint x y hyη)
  refine ⟨v₀, ?_⟩
  rintro ⟨y', hy'U, -, hv₀'⟩
  have : y' = y := eq_of_range_stalk_eq x y' y (hv₀'.trans hv₀.symm)
  exact hy (this ▸ hy'U)

theorem exp_eq_mul_exp_of_forall_mem_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Set (Place K F)) (D D' : Divisor K F) (g : F)
    (hiff : ∀ f : F, f ∈ lSpaceOn S D' ↔ ∃ f₀ ∈ lSpaceOn S D, f = g * f₀)
    (v : Place K F) (hv : v ∈ S)
    (hatt : ∃ f : F, f ∈ lSpaceOn S D ∧ v.adicValuation f = exp (D v))
    (hatt' : ∃ f : F, f ∈ lSpaceOn S D' ∧ v.adicValuation f = exp (D' v)) :
    exp (D' v) = v.adicValuation g * exp (D v) := by
  apply le_antisymm
  · obtain ⟨f', hf', hval'⟩ := hatt'
    obtain ⟨f₀, hf₀, rfl⟩ := (hiff f').mp hf'
    rw [← hval', Valuation.map_mul]
    exact mul_le_mul_right (hf₀ v hv) _
  · obtain ⟨f, hf, hval⟩ := hatt
    have hgf : g * f ∈ lSpaceOn S D' := (hiff (g * f)).mpr ⟨f, hf, rfl⟩
    have := hgf v hv
    rwa [Valuation.map_mul, hval] at this

end MazurTransfer.PublicPresentationRatioHelpers
open MazurTransfer.PublicPresentationRatioHelpers

theorem solution
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (M : X.Modules)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ g : X.functionField, g ≠ 0 ∧
      (∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m) ∧
      (∀ v : AlgebraicCurve.Place K X.functionField, D v = D' v + v.ord g) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D - D') := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra

  haveI hcurve : IsCurveOver K X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one x (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType K X.functionField := essFiniteType_functionField x

  obtain ⟨g, hg, hmul⟩ :=
    Scheme.Modules.exists_forall_eq_mul_of_presentations M φ φ' hnat hnat' hsmul hsmul' hinj hinj' hsec
  have hord : ∀ v : Place K X.functionField, D v = D' v + v.ord g := by
    intro v

    obtain ⟨y, hy, hvy⟩ := exists_closedPoint_range_stalk_eq x v
    obtain ⟨U, hUaff, hyU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (Opens.mem_top y)
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    have hvS : v ∈ placesOf x U := ⟨y, hyU, hy, hvy⟩
    obtain ⟨v₀, hv₀⟩ := exists_not_mem_placesOf x U hUaff

    haveI : Nonempty (Place K X.functionField) := ⟨v⟩
    obtain ⟨-, hL0, γ, D₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
    haveI := hL0

    have hiff : ∀ f : X.functionField,
        f ∈ lSpaceOn (placesOf x U) D' ↔ ∃ f₀ ∈ lSpaceOn (placesOf x U) D, f = g * f₀ := by
      intro f
      have hD : ∀ f₀, f₀ ∈ lSpaceOn (placesOf x U) D ↔ f₀ ∈ Set.range (φ U) := fun f₀ => by
        rw [hrange U hUaff inferInstance]; rfl
      have hD' : f ∈ lSpaceOn (placesOf x U) D' ↔ f ∈ Set.range (φ' U) := by
        rw [hrange' U hUaff inferInstance]; rfl
      rw [hD']
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨φ U m, (hD _).mpr ⟨m, rfl⟩, hmul U m⟩
      · rintro ⟨f₀, hf₀, rfl⟩
        obtain ⟨m, rfl⟩ := (hD f₀).mp hf₀
        exact ⟨m, hmul U m⟩
    have key := exp_eq_mul_exp_of_forall_mem_iff (placesOf x U) D D' g hiff v hvS
      (exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt hγ (placesOf x U) hv₀ D v hvS)
      (exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt hγ (placesOf x U) hv₀ D' v hvS)
    rw [Place.adicValuation_eq_exp_neg_ord v hg, ← WithZero.exp_add] at key
    have := WithZero.exp_injective key
    linarith
  refine ⟨g, hg, hmul, hord, g, hg, fun v => ?_⟩
  rw [Finsupp.sub_apply, hord v]
  ring

#print axioms solution
