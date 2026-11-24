-- Prove2me | solution 1 for GlobalTheory.specialisation_numberField_and_countable_values
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:42.924828+00:00
-- url     : https://prove2.me/submissions/86e3ab5d-e945-4812-9f12-c55cb03d0aee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Theorems.Thm_GlobalTheory_exists_ringHom_extend_of_finiteType
import Theorems.Thm_GlobalTheory_exists_specialisation_finite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private lemma exists_algHom_extend_of_fg_ne_zero {k L M : Type*} [Field k] [Field L] [Algebra k L]
    [Field M] [IsAlgClosed M] [Algebra k M] (F : IntermediateField k L) (σ : F →ₐ[k] M)
    (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ ρ : R →ₐ[k] M, (∀ (x : R) (hx : (x : L) ∈ F), ρ x = σ ⟨x, hx⟩) ∧ ρ r ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := hR
  have hrL : (r : L) ≠ 0 := fun h => hr (Subtype.ext h)
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F L, A = Algebra.adjoin F ↑(insert ((r : L)⁻¹) s) := ⟨_, rfl⟩
  haveI : Algebra.FiniteType F A :=
    (Subalgebra.fg_iff_finiteType A).1 ⟨insert ((r : L)⁻¹) s, hA.symm⟩
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.exists_ringHom_extend_of_finiteType F A M σ.toRingHom
  have hgen : ∀ y ∈ insert ((r : L)⁻¹) s, y ∈ A := fun y hy => by
    rw [hA]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hy)
  have hle : ∀ x ∈ R, x ∈ A := by
    intro x hx
    rw [← hs] at hx
    have hsub : Algebra.adjoin k (s : Set L) ≤ A.restrictScalars k :=
      Algebra.adjoin_le fun y hy => (Subalgebra.mem_restrictScalars k).2
        (hgen y (Finset.mem_insert_of_mem (Finset.mem_coe.1 hy)))
    exact (Subalgebra.mem_restrictScalars k).1 (hsub hx)
  let ι : R →+* A :=
    { toFun := fun x => ⟨x, hle x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hι : ∀ (x : R) (hx : (x : L) ∈ F), ι x = algebraMap F A ⟨x, hx⟩ :=
    fun _ _ => Subtype.ext rfl
  have hcomm : ∀ a : k, φ (ι (algebraMap k R a)) = algebraMap k M a := by
    intro a
    have h1 : ι (algebraMap k R a) = algebraMap F A (algebraMap k F a) := Subtype.ext (by
      change algebraMap k L a = algebraMap F L (algebraMap k F a)
      exact IsScalarTower.algebraMap_apply k F L a)
    rw [h1, hφ]
    exact σ.commutes a
  refine ⟨{ toRingHom := φ.comp ι, commutes' := hcomm }, fun x hx => ?_, ?_⟩
  · show φ (ι x) = σ ⟨x, hx⟩
    rw [hι x hx, hφ]
    rfl
  · have hinv : ι r * ⟨(r : L)⁻¹, hgen _ (Finset.mem_insert_self _ _)⟩ = 1 :=
      Subtype.ext (by simp [ι, hrL])
    have := congrArg φ hinv
    rw [map_mul, map_one] at this
    exact left_ne_zero_of_mul_eq_one this
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG →
    ∀ (c r : R), r ≠ 0 →
    (∃ (K₁ : IntermediateField k ℂ) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      (IsAlgebraic k c → (ρ c : ℂ) = c)) ∧
    (∀ S : Set ℂ, S.Countable → (∀ ρ : R →ₐ[k] ℂ, ρ c ∈ S) → IsAlgebraic k c) := by
  intro k _ R hR c r hr
  refine ⟨?_, fun S hS hρ => ?_⟩
  · obtain ⟨K₁, ρ, hfin, hr₁, hfix⟩ := _root_.GlobalTheory.exists_specialisation_finite R hR r hr
    exact ⟨K₁, ρ, hfin, hr₁, hfix c⟩
  by_contra hc
  have hct : Transcendental k (c : ℂ) := fun h =>
    hc ((isAlgebraic_algHom_iff R.val Subtype.val_injective).1 h)
  have key : ∀ z : ℂ, Transcendental ℚ z → z ∈ S := by
    intro z hz
    have hzk : Transcendental k z := fun h => hz (h.restrictScalars ℚ)
    let e₁ := RatFunc.algEquivOfTranscendental (c : ℂ) hct
    let e₂ := RatFunc.algEquivOfTranscendental z hzk
    let σ : IntermediateField.adjoin k {(c : ℂ)} →ₐ[k] ℂ :=
      (IntermediateField.adjoin k {z}).val.comp (e₂.toAlgHom.comp e₁.symm.toAlgHom)
    have hcmem : (c : ℂ) ∈ IntermediateField.adjoin k {(c : ℂ)} :=
      IntermediateField.mem_adjoin_simple_self k (c : ℂ)
    have hσ : σ ⟨c, hcmem⟩ = z := by
      have h1 : e₁.symm ⟨c, hcmem⟩ = RatFunc.X := by
        rw [AlgEquiv.symm_apply_eq]
        exact Subtype.ext (RatFunc.algEquivOfTranscendental_X (c : ℂ) hct).symm
      show ((e₂ (e₁.symm ⟨c, hcmem⟩) : IntermediateField.adjoin k {z}) : ℂ) = z
      rw [h1]
      exact RatFunc.algEquivOfTranscendental_X z hzk
    obtain ⟨ρ, hfix, -⟩ :=
      exists_algHom_extend_of_fg_ne_zero (IntermediateField.adjoin k {(c : ℂ)}) σ R hR 1 one_ne_zero
    have h := hρ ρ
    rwa [hfix c hcmem, hσ] at h
  have hcover : (Set.univ : Set ℂ) ⊆ S ∪ {z | IsAlgebraic ℚ z} := fun z _ => by
    by_cases h : IsAlgebraic ℚ z
    · exact Or.inr h
    · exact Or.inl (key z h)
  exact not_countable_complex ((hS.union (Algebraic.countable ℚ ℂ)).mono hcover)
end _root_.GlobalTheory
end GlobalTheory
