-- Prove2me | solution 1 for N25.GlobalKummer.psi_cocycle_restricted_character
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:03.820291+00:00
-- url     : https://prove2.me/submissions/65670c83-5ab9-4f1f-a5e7-653ea60aeb4e

import Mathlib
import Definitions.Def_N25_GlobalKummerSequence
import Theorems.Thm_N25_characterField_comparison
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Theorems.Thm_N25_characterField_classNumber_le_seven
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance psiRestrictedPrimeSeventyOne_s9cc59a : Fact (Nat.Prime 71) := ⟨by decide⟩

private theorem psi_cocycle_mul (c : groupCohomology.cocycles₁ psiRep) (σ τ : Gal) :
    c (σ * τ) = (psi σ : ZMod 71) * c τ + c σ := by
  have hraw : c (σ * τ) = psiRep.ρ σ (c τ) + c σ :=
    (groupCohomology.mem_cocycles₁_iff c).mp c.property σ τ
  have hρ : psiRep.ρ σ (c τ) = (psi σ : ZMod 71) * c τ := rfl
  exact hraw.trans (congrArg (fun z => z + c σ) hρ)

/-- Restricting a genuine finite-level psi-line cocycle to the field cut out
by psi produces a genuine finite-level additive character over the actual
quintic field, whose class number is at most seven. -/
theorem _root_.solution
    (c : groupCohomology.cocycles₁ psiRep)
    (hc : groupCohomology.IsLevelConstant₁ (MonoidHom.id Gal) c) :
    ∃ j : characterField →ₐ[ℚ] AlgebraicClosure ℚ,
      letI : Algebra characterField (AlgebraicClosure ℚ) := j.toRingHom.toAlgebra
      letI : IsScalarTower ℚ characterField (AlgebraicClosure ℚ) := IsScalarTower.of_algHom j
      IsGalois characterField (AlgebraicClosure ℚ) ∧
      (∀ τ : AlgebraicClosure ℚ ≃ₐ[characterField] AlgebraicClosure ℚ,
        psi (τ.restrictScalars ℚ) = 1) ∧
      (∀ σ : Gal, psi σ = 1 → ∀ x : characterField, σ (j x) = j x) ∧
      ∃ f : (AlgebraicClosure ℚ ≃ₐ[characterField] AlgebraicClosure ℚ) →*
          Multiplicative (ZMod 71),
        (∀ σ, f σ = Multiplicative.ofAdd (c (σ.restrictScalars ℚ))) ∧
        (∃ E : IntermediateField characterField (AlgebraicClosure ℚ),
          FiniteDimensional characterField E ∧ E.fixingSubgroup ≤ f.ker) ∧
        NumberField.classNumber characterField ≤ 7 := by
  classical
  obtain ⟨e⟩ := characterField_comparison.2
  let j : characterField →ₐ[ℚ] AlgebraicClosure ℚ :=
    (IntermediateField.fixedField psi.ker).val.comp e.toAlgHom
  letI : Algebra characterField (AlgebraicClosure ℚ) := j.toRingHom.toAlgebra
  letI : IsScalarTower ℚ characterField (AlgebraicClosure ℚ) := IsScalarTower.of_algHom j
  have hpsi (σ : AlgebraicClosure ℚ ≃ₐ[characterField] AlgebraicClosure ℚ) :
      psi (σ.restrictScalars ℚ) = 1 := by
    have hfix : σ.restrictScalars ℚ ∈ (IntermediateField.fixedField psi.ker).fixingSubgroup := by
      intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      exact σ.commutes y
    rwa [characterField_comparison.1] at hfix
  let f : (AlgebraicClosure ℚ ≃ₐ[characterField] AlgebraicClosure ℚ) →*
      Multiplicative (ZMod 71) :=
    { toFun := fun σ => Multiplicative.ofAdd (c (σ.restrictScalars ℚ))
      map_one' := by
        change Multiplicative.ofAdd (c 1) = 1
        rw [groupCohomology.cocycles₁_map_one]
        rfl
      map_mul' := by
        intro σ τ
        change Multiplicative.ofAdd (c (σ.restrictScalars ℚ * τ.restrictScalars ℚ)) =
          Multiplicative.ofAdd (c (σ.restrictScalars ℚ)) *
            Multiplicative.ofAdd (c (τ.restrictScalars ℚ))
        have hcc := psi_cocycle_mul c (σ.restrictScalars ℚ) (τ.restrictScalars ℚ)
        rw [hpsi, Units.val_one, one_mul] at hcc
        exact congrArg Multiplicative.ofAdd (hcc.trans (add_comm _ _)) }
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic characterField (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (L := characterField)
  haveI : IsAlgClosure characterField (AlgebraicClosure ℚ) :=
    (isAlgClosure_iff characterField (AlgebraicClosure ℚ)).mpr ⟨inferInstance, inferInstance⟩
  haveI : Algebra.IsSeparable characterField (AlgebraicClosure ℚ) :=
    IsAlgClosure.separable characterField (AlgebraicClosure ℚ)
  haveI : Normal characterField (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal characterField (AlgebraicClosure ℚ)
  haveI : IsGalois characterField (AlgebraicClosure ℚ) := ⟨⟩
  have hjfix (σ : Gal) (hσ : psi σ = 1) (x : characterField) : σ (j x) = j x := by
    exact (e x).property ⟨σ, hσ⟩
  refine ⟨j, inferInstance, hpsi, hjfix, f, fun _ => rfl, ?_, characterField_classNumber_le_seven⟩
  obtain ⟨F, hF, hFlevel⟩ := hc
  letI : Algebra ℚ F := F.algebra'
  letI : FiniteDimensional ℚ F := hF
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  have hFadjoin : IntermediateField.adjoin ℚ {(α : AlgebraicClosure ℚ)} = F := by
    have hmaptop : (⊤ : IntermediateField ℚ F).map F.val = F := by
      ext x
      constructor
      · rintro ⟨y, _, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, by trivial, rfl⟩
    have hh := congrArg (fun T : IntermediateField ℚ F => T.map F.val) hα
    change (IntermediateField.adjoin ℚ {α}).map F.val = (⊤ : IntermediateField ℚ F).map F.val at hh
    rw [IntermediateField.adjoin_map, Set.image_singleton, hmaptop] at hh
    exact hh
  let E : IntermediateField characterField (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin characterField {(α : AlgebraicClosure ℚ)}
  haveI : FiniteDimensional characterField E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (α : AlgebraicClosure ℚ))
  refine ⟨E, inferInstance, ?_⟩
  intro σ hσ
  have hFE : F ≤ E.restrictScalars ℚ := by
    rw [← hFadjoin, IntermediateField.adjoin_le_iff]
    exact fun x hx => IntermediateField.subset_adjoin characterField _ hx
  have hfix : σ.restrictScalars ℚ ∈ F.fixingSubgroup := by
    intro x
    exact hσ ⟨(x : AlgebraicClosure ℚ), hFE x.property⟩
  have hz := hFlevel 1 (σ.restrictScalars ℚ) hfix
  have hczero : c (σ.restrictScalars ℚ) = 0 := by simpa only [one_mul, groupCohomology.cocycles₁_map_one] using hz
  change Multiplicative.ofAdd (c (σ.restrictScalars ℚ)) = 1
  rw [hczero]
  rfl

end N25.GlobalKummer
