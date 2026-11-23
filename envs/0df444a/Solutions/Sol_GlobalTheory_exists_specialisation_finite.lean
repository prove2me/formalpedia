-- Prove2me | solution 1 for GlobalTheory.exists_specialisation_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:02.764441+00:00
-- url     : https://prove2.me/submissions/28bbac79-ac9e-48d2-b3da-1084fac21d56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Theorems.Thm_GlobalTheory_exists_ringHom_extend_of_finiteType
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
theorem _root_.solution {k L : Type*} [Field k] [Field L]
    [Algebra k L] [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ (K₁ : IntermediateField k L) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      ∀ c : R, IsAlgebraic k c → (ρ c : L) = c := by
  classical
  haveI : IsAlgClosed (algebraicClosure k L) := IsAlgClosure.isAlgClosed k
  obtain ⟨ρ₁, hfix, hr₁⟩ :=
    exists_algHom_extend_of_fg_ne_zero (algebraicClosure k L) (AlgHom.id k _) R hR r hr
  let ρ₀ : R →ₐ[k] L := (algebraicClosure k L).val.comp ρ₁
  have halg : ∀ x : R, IsAlgebraic k (ρ₀ x) := fun x => mem_algebraicClosure_iff.1 (ρ₁ x).2
  haveI : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := k) (A := R)
  haveI : Finite (ρ₀ '' (t : Set R)) := (t.finite_toSet.image _).to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k (ρ₀ '' (t : Set R))) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨x, -, rfl⟩ := hy
      exact (halg x).isIntegral
  have hmem : ∀ x : R, ρ₀ x ∈ IntermediateField.adjoin k (ρ₀ '' (t : Set R)) := by
    intro x
    have hx : x ∈ Algebra.adjoin k (t : Set R) := by rw [ht]; exact Algebra.mem_top
    have h1 : ρ₀ x ∈ Algebra.adjoin k (ρ₀ '' (t : Set R)) := by
      rw [← AlgHom.map_adjoin]; exact ⟨x, hx, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  refine ⟨IntermediateField.adjoin k (ρ₀ '' (t : Set R)),
    { toFun := fun x => ⟨ρ₀ x, hmem x⟩
      map_one' := Subtype.ext (map_one ρ₀)
      map_mul' := fun x y => Subtype.ext (map_mul ρ₀ x y)
      map_zero' := Subtype.ext (map_zero ρ₀)
      map_add' := fun x y => Subtype.ext (map_add ρ₀ x y)
      commutes' := fun a => Subtype.ext (ρ₀.commutes a) }, hfin, fun h => hr₁ ?_, fun c hc => ?_⟩
  · have h' : ρ₀ r = 0 := congrArg Subtype.val h
    exact Subtype.ext h'
  · have hcL : (c : L) ∈ algebraicClosure k L := mem_algebraicClosure_iff.2 (hc.algHom R.val)
    show ((ρ₁ c : algebraicClosure k L) : L) = c
    rw [hfix c hcL]
    rfl
end _root_.GlobalTheory
end GlobalTheory
