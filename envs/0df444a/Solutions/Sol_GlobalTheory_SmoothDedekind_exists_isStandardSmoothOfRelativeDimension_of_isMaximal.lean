-- Prove2me | solution 1 for GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:15.624402+00:00
-- url     : https://prove2.me/submissions/9aa2028d-3405-48de-9339-493f97d596b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
import Theorems.Thm_GlobalTheory_SmoothDedekind_exists_point_of_isMaximal
import Theorems.Thm_GlobalTheory_SmoothDedekind_exists_isStandardSmoothOfRelativeDimension_of_localization
import Theorems.Thm_GlobalTheory_finite_field_of_finiteType_int


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
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing
namespace GlobalTheory.SmoothDedekind
theorem _root_.solution (o : Type) [CommRing o]
    [IsDedekindDomain o] [CharZero o] [Algebra.FiniteType ℤ o]
    {A : Type} [CommRing A] [Algebra o A] [Algebra.FiniteType o A] [Module.Flat o A] {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (FractionRing o ⊗[o] A),
      (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] A) ⧸ p))
    (ht : ∀ (C : Type) [Field C] [IsAlgClosed C] (r : ℕ) (g : A →+* TrivSqZeroExt C (Fin r → C)),
      (∀ c : o, (g (algebraMap o A c)).snd = 0) →
      (∀ lam : (Fin r → C) →ₗ[C] C, (∀ a, lam (g a).snd = 0) → lam = 0) → r ≤ d)
    (q : Ideal A) [q.IsMaximal] :
    ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d o (Localization.Away f) := by
  let m := q.under o
  have : Algebra.FiniteType ℤ A := .trans (S := o) ‹_› ‹_›
  have : Finite (A ⧸ q) := by
    let := Ideal.Quotient.field q
    have h : ((Ideal.Quotient.mk q).comp (algebraMap ℤ A)).FiniteType :=
      (RingHom.finiteType_algebraMap.mpr ‹_›).comp_surjective Ideal.Quotient.mk_surjective
    refine @finite_field_of_finiteType_int _ _ (RingHom.finiteType_algebraMap.mp ?_)
    exact (congrArg RingHom.FiniteType (RingHom.ext_int _ _)).mp h
  let e : m.ResidueField →ₐ[o] q.ResidueField := Ideal.ResidueField.mapₐ m q (Algebra.ofId o A) rfl
  have : Finite m.ResidueField := .of_injective e e.toRingHom.injective
  have hm : m ≠ ⊥ := fun h ↦ by
    have : Finite o := .of_injective (algebraMap o m.ResidueField)
      ((RingHom.injective_iff_ker_eq_bot _).mpr (m.ker_algebraMap_residueField.trans h))
    exact not_finite o
  have : m.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hm
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o hm
    (Localization.AtPrime m)
  let χ : m.ResidueField ⊗[o] A →ₐ[o] q.ResidueField :=
    Algebra.TensorProduct.lift e (IsScalarTower.toAlgHom o A _) fun _ _ ↦ .all _ _
  let ψ : A →+* m.ResidueField ⊗[o] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[o] m.ResidueField ⊗[o] A).toRingHom
  have hψ : Function.Surjective ψ :=
    TensorProduct.mk_surjective o A _ m.algebraMap_residueField_surjective
  have hχψ (a : A) : χ (ψ a) = algebraMap A _ a := by simp [χ, ψ]
  have hχ : Function.Surjective χ.toRingHom := fun y ↦ by
    obtain ⟨a, rfl⟩ := q.algebraMap_residueField_surjective y
    exact ⟨_, hχψ a⟩
  let x := RingHom.ker χ.toRingHom
  have : x.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ
  have hq : x.comap ψ = q := by
    ext a
    rw [← Ideal.algebraMap_residueField_eq_zero (I := q), ← hχψ]
    rfl
  obtain ⟨C, _, _, r, g, h₁, h₂, h₃⟩ := exists_point_of_isMaximal m.ResidueField x
  have hr : r ≤ d := by
    refine ht C r (g.comp ψ) (fun c ↦ ?_) fun lam h ↦ h₃ lam fun b ↦ ?_
    · have := h₂ (algebraMap o _ c)
      rw [← IsScalarTower.algebraMap_apply,
        ← (Algebra.TensorProduct.includeRight : A →ₐ[o] m.ResidueField ⊗[o] A).commutes] at this
      exact this
    · obtain ⟨a, rfl⟩ := hψ b
      exact h a
  rw [← hq]
  exact exists_isStandardSmoothOfRelativeDimension_of_localization o (Localization.AtPrime m)
    (FractionRing o) m.primeCompl hd x (h₁.trans hr)
end GlobalTheory.SmoothDedekind
