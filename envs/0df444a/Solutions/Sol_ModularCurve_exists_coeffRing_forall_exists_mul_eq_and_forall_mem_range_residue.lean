-- Prove2me | solution 1 for ModularCurve.exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/59f8d300-c386-57c0-9218-77a90428b475

import Mathlib
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (S : Finset (AlgebraicClosure ℚ)) (k₀ : Subfield (ResidueField ↥A)) [Finite ↥k₀] :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (ρO' : R p →+* O')
      (ιA' : O' →+* ↥A) (_ : Function.Injective ιA') (_ : IsLocalHom ιA') (_ : ιA'.comp ρO' = ρ)
      (jO' : O' →+* AlgebraicClosure ℚ) (_ : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (_ : A.subtype.comp ιA' = jO')
      (_ : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ),
      (∀ c ∈ S, ∃ a b : O', jO' b ≠ 0 ∧ c * jO' b = jO' a) ∧
      (∀ ξ : ResidueField ↥A, ξ ∈ k₀ → ξ ∈ Set.range ((IsLocalRing.residue ↥A).comp ιA')) := by
  classical

  have hsurj : Function.Surjective (IsLocalRing.residue ↥A) := IsLocalRing.residue_surjective
  choose lift hlift using fun ξ : ↥k₀ => hsurj (ξ : ResidueField ↥A)

  let T : Set (AlgebraicClosure ℚ) :=
    (↑S : Set (AlgebraicClosure ℚ)) ∪ Set.range (fun ξ : ↥k₀ => ((lift ξ : ↥A) : AlgebraicClosure ℚ))
  have hTfin : T.Finite := S.finite_toSet.union (Set.finite_range _)
  haveI : Finite ↥T := hTfin.to_subtype
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ T
  haveI : FiniteDimensional ℚ ↥L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hTL : T ⊆ (L : Set (AlgebraicClosure ℚ)) := IntermediateField.subset_adjoin ℚ T
  let O : ValuationSubring ↥L := A.comap (algebraMap ↥L (AlgebraicClosure ℚ))
  have hmemO : ∀ x : ↥L, x ∈ O ↔ (x : AlgebraicClosure ℚ) ∈ A := fun x => Iff.rfl
  haveI hDVR : IsDiscreteValuationRing ↥O := ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime L A (Fact.out) hA

  let ι : ↥O →+* ↥A :=
    ((algebraMap ↥L (AlgebraicClosure ℚ)).comp O.subtype).codRestrict A (fun x => (hmemO x.1).mp x.2)
  have hιval : ∀ x : ↥O, ((ι x : ↥A) : AlgebraicClosure ℚ) = ((x : ↥L) : AlgebraicClosure ℚ) := fun x => rfl
  have hinj : Function.Injective ι := by
    intro x y hxy
    have h := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hxy
    simp only [hιval] at h
    exact Subtype.ext (Subtype.ext h)
  have hloc : IsLocalHom ι := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have hy' : ((x : ↥L) : AlgebraicClosure ℚ) * ((y : ↥A) : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hy
      simpa [hιval] using this
    have hx0 : ((x : ↥L) : AlgebraicClosure ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hy'
    have hxL0 : (x : ↥L) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
    have hinv : ((x : ↥L))⁻¹ ∈ O := by
      rw [hmemO]
      have : (((x : ↥L))⁻¹ : ↥L) = ((((x : ↥L) : AlgebraicClosure ℚ))⁻¹ : AlgebraicClosure ℚ) := by
        push_cast; rfl
      rw [this, ← eq_inv_of_mul_eq_one_right hy']
      exact y.2
    exact isUnit_iff_exists_inv.mpr ⟨⟨(x : ↥L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hxL0)⟩

  have hρval : ∀ r : R p, ((ρ r : ↥A) : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := by
    intro r
    have := RingHom.congr_fun hρ r
    simp at this
    exact this
  let ρO : R p →+* ↥O :=
    ((algebraMap ℚ ↥L).comp (GaloisRep.ratLocalizedAt p).subtype).codRestrict O (fun r => by
      rw [hmemO]
      have : ((algebraMap ℚ ↥L (r : ℚ) : ↥L) : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) :=
        (IsScalarTower.algebraMap_apply ℚ ↥L (AlgebraicClosure ℚ) (r : ℚ)).symm
      rw [RingHom.comp_apply, Subring.coe_subtype, this, ← hρval]
      exact (ρ r).2)
  have hιρ : ι.comp ρO = ρ := by
    refine RingHom.ext fun r => Subtype.ext ?_
    rw [RingHom.comp_apply, hιval, hρval]
    exact (IsScalarTower.algebraMap_apply ℚ ↥L (AlgebraicClosure ℚ) (r : ℚ)).symm

  refine ⟨↥O, inferInstance, inferInstance, hDVR, ρO, ι, hinj, hloc, hιρ, A.subtype.comp ι, ?_, rfl, ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, hιρ, hρ]
  · rw [RingHom.comp_assoc, hιρ]
  ·
    intro c hc
    have hcL : c ∈ L := hTL (Or.inl hc)
    by_cases hcO : (⟨c, hcL⟩ : ↥L) ∈ O
    · refine ⟨⟨⟨c, hcL⟩, hcO⟩, 1, by simp, ?_⟩
      simp [hιval]
    · have hc0 : (⟨c, hcL⟩ : ↥L) ≠ 0 := by
        rintro h; exact hcO (h ▸ O.zero_mem)
      have hcinv : (⟨c, hcL⟩ : ↥L)⁻¹ ∈ O := (O.mem_or_inv_mem _).resolve_left hcO
      have hc0' : c ≠ 0 := fun h => hc0 (Subtype.ext h)
      refine ⟨1, ⟨(⟨c, hcL⟩ : ↥L)⁻¹, hcinv⟩, ?_, ?_⟩
      · simp [hιval, hc0']
      · simp [hιval, hc0']
  ·
    intro ξ hξ
    have hxL : ((lift ⟨ξ, hξ⟩ : ↥A) : AlgebraicClosure ℚ) ∈ L := hTL (Or.inr ⟨⟨ξ, hξ⟩, rfl⟩)
    have hxO : (⟨_, hxL⟩ : ↥L) ∈ O := by rw [hmemO]; exact (lift ⟨ξ, hξ⟩).2
    refine ⟨⟨⟨_, hxL⟩, hxO⟩, ?_⟩
    have : ι ⟨⟨_, hxL⟩, hxO⟩ = lift ⟨ξ, hξ⟩ := Subtype.ext (hιval _)
    rw [RingHom.comp_apply, this, hlift]

end S_ModularCurve_exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue
end P2MW
export P2MW.S_ModularCurve_exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue (solution)
