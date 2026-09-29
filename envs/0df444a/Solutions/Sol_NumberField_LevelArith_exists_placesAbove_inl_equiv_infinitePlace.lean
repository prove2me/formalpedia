-- Prove2me | solution 1 for NumberField.LevelArith.exists_placesAbove_inl_equiv_infinitePlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/14a6dbac-f44c-5f2b-ac83-59320436f754

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_placesAbove_inl_equiv_infinitePlace

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

local instance PlacesInf.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance PlacesInf.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance PlacesInf.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
noncomputable local instance PlacesInf.algebraQbarComplex : Algebra (AlgebraicClosure ℚ) ℂ :=
  complexEmbedding.toRingHom.toAlgebra
local instance PlacesInf.towerQbarComplex : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

namespace PlacesInf

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma algebraMap_qbar_complex (z : Qbar) : algebraMap Qbar ℂ z = complexEmbedding z := rfl

lemma mem_archimedeanDecomposition_iff (d : Γ) : d ∈ archimedeanDecomposition ↔ d = 1 ∨ d = complexConjugation := by
  constructor
  · intro hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    rw [zpow_eq_zpow_emod' k complexConjugation_sq]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      have : (k % (2 : ℕ) : ℤ) = 0 := by exact_mod_cast h
      rw [this, zpow_zero]
    · right
      have : (k % (2 : ℕ) : ℤ) = 1 := by exact_mod_cast h
      rw [this, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

lemma mem_range_inl_iff (S : Finset Nat.Primes) (d : Γ) :
    d ∈ (extArithLoc S (Sum.inl ())).range ↔ d = 1 ∨ d = complexConjugation := by
  rw [← mem_archimedeanDecomposition_iff, extArithLoc_inl]
  constructor
  · rintro ⟨z, rfl⟩; exact z.2
  · intro hd; exact ⟨⟨d, hd⟩, rfl⟩

variable (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L)

noncomputable def emb (x : Γ) : ↥(levelField K L hKL) →+* ℂ :=
  complexEmbedding.toRingHom.comp (((x⁻¹ : Γ) : Qbar →+* Qbar).comp (algebraMap ↥(levelField K L hKL) Qbar))

lemma emb_apply (x : Γ) (y : ↥(levelField K L hKL)) : emb K L hKL x y = complexEmbedding (x⁻¹ (y : Qbar)) := rfl

lemma emb_mul_conj (x : Γ) : emb K L hKL (x * complexConjugation) = NumberField.ComplexEmbedding.conjugate (emb K L hKL x) := by
  apply RingHom.ext
  intro y
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, emb_apply, emb_apply, mul_inv_rev, complexConjugation_inv,
    AlgEquiv.mul_apply, complexEmbedding_complexConjugation]

lemma emb_left_mul_of_mem (x : Γ) {s : Γ} (hs : s ∈ L.fixingSubgroup) : emb K L hKL (s * x) = emb K L hKL x := by
  apply RingHom.ext
  intro y
  rw [emb_apply, emb_apply, mul_inv_rev, AlgEquiv.mul_apply]
  congr 2
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (L.fixingSubgroup.inv_mem hs) _
    ((IntermediateField.mem_extendScalars hKL).1 y.2)

lemma emb_eq_emb_iff (x₁ x₂ : Γ) : emb K L hKL x₁ = emb K L hKL x₂ ↔ x₂ * x₁⁻¹ ∈ L.fixingSubgroup := by
  constructor
  · intro h
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have := RingHom.congr_fun h ⟨y, (IntermediateField.mem_extendScalars hKL).2 hy⟩
    rw [emb_apply, emb_apply] at this
    have h2 : x₁⁻¹ y = x₂⁻¹ y := complexEmbedding.toRingHom.injective this
    rw [AlgEquiv.mul_apply, h2]
    exact AlgEquiv.apply_symm_apply x₂ y
  · intro h
    have : x₂ = (x₂ * x₁⁻¹) * x₁ := by group
    rw [this, emb_left_mul_of_mem K L hKL x₁ h]

variable [Normal ↥K ↥(levelField K L hKL)]

lemma emb_left_mul_gamma (γ : ↥K.fixingSubgroup) (x : Γ) :
    emb K L hKL ((γ : Γ) * x) = (emb K L hKL x).comp ((levelGal K L hKL γ).symm : ↥(levelField K L hKL) →+* ↥(levelField K L hKL)) := by
  apply RingHom.ext
  intro y
  rw [RingHom.comp_apply, emb_apply, emb_apply, mul_inv_rev, AlgEquiv.mul_apply]
  congr 2
  have h1 : (levelGal K L hKL γ).symm = levelGal K L hKL γ⁻¹ := by
    rw [map_inv]; rfl
  rw [RingHom.coe_coe, h1, levelGal_apply_coe]
  rfl

end PlacesInf

namespace PlacesInf

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L) (S : Finset Nat.Primes)

abbrev X : Type := Γ ⧸ (extArithLoc S (Sum.inl ())).range

noncomputable def placeX : X S → NumberField.InfinitePlace ↥(levelField K L hKL) :=
  Quotient.lift (fun x : Γ => NumberField.InfinitePlace.mk (emb K L hKL x)) fun a b hab => by
    have hab' : a⁻¹ * b ∈ (extArithLoc S (Sum.inl ())).range := QuotientGroup.leftRel_apply.1 hab
    have hb : b = a * (a⁻¹ * b) := by group
    show NumberField.InfinitePlace.mk (emb K L hKL a) = NumberField.InfinitePlace.mk (emb K L hKL b)
    rcases (mem_range_inl_iff S _).1 hab' with h | h
    · rw [hb, h, mul_one]
    · rw [hb, h, emb_mul_conj, NumberField.InfinitePlace.mk_conjugate_eq]

lemma placeX_mk (x : Γ) : placeX K L hKL S (x : X S) = NumberField.InfinitePlace.mk (emb K L hKL x) := rfl

noncomputable def placeQ : placesAbove L S (Sum.inl ()) → NumberField.InfinitePlace ↥(levelField K L hKL) :=
  Quotient.lift (placeX K L hKL S) fun a b hab => by
    change (MulAction.orbitRel ↥L.fixingSubgroup (X S)) a b at hab
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
    obtain ⟨s, rfl⟩ := hab
    induction b using QuotientGroup.induction_on with
    | H x =>
      show placeX K L hKL S ((((s : Γ) * x : Γ) : X S)) = placeX K L hKL S (x : X S)
      rw [placeX_mk, placeX_mk, emb_left_mul_of_mem K L hKL x s.2]

lemma placeQ_mk_mk (x : Γ) :
    placeQ K L hKL S (Quotient.mk'' (x : X S)) = NumberField.InfinitePlace.mk (emb K L hKL x) := rfl

variable (hnorm : IsNormalLevel K L) [Normal ↥K ↥(levelField K L hKL)]

lemma placeQ_smul (γ : ↥K.fixingSubgroup) (q : placesAbove L S (Sum.inl ())) :
    placeQ K L hKL S ((orbitQuotientAction K L hnorm (X S)).smul γ q) = levelGal K L hKL γ • placeQ K L hKL S q := by
  induction q using Quotient.inductionOn' with
  | h c =>
    induction c using QuotientGroup.induction_on with
    | H x =>
      show placeQ K L hKL S (Quotient.mk'' ((((γ : Γ) * x : Γ) : X S))) = _
      rw [placeQ_mk_mk, placeQ_mk_mk, NumberField.InfinitePlace.smul_mk, emb_left_mul_gamma]

omit [Normal ↥K ↥(levelField K L hKL)] in
lemma placeQ_injective : Function.Injective (placeQ K L hKL S) := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn' with
  | h c₁ =>
  induction q₂ using Quotient.inductionOn' with
  | h c₂ =>
  induction c₁ using QuotientGroup.induction_on with
  | H x₁ =>
  induction c₂ using QuotientGroup.induction_on with
  | H x₂ =>
  rw [placeQ_mk_mk, placeQ_mk_mk, NumberField.InfinitePlace.mk_eq_iff] at h

  have key : ∀ x₁' : Γ, (x₁' : X S) = (x₁ : X S) → emb K L hKL x₁' = emb K L hKL x₂ →
      (Quotient.mk'' (x₁ : X S) : placesAbove L S (Sum.inl ())) = Quotient.mk'' (x₂ : X S) := by
    intro x₁' hx₁' he
    rw [emb_eq_emb_iff] at he
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨⟨(x₂ * x₁'⁻¹)⁻¹, L.fixingSubgroup.inv_mem he⟩, ?_⟩
    rw [← hx₁']
    show ((((x₂ * x₁'⁻¹)⁻¹ * x₂ : Γ)) : X S) = (x₁' : X S)
    congr 1
    group
  rcases h with h | h
  · exact key x₁ rfl h
  · refine key (x₁ * complexConjugation) ?_ (by rw [emb_mul_conj]; exact h)
    exact QuotientGroup.mk_mul_of_mem x₁ ((mem_range_inl_iff S _).2 (Or.inr rfl))

omit [Normal ↥K ↥(levelField K L hKL)] in
lemma placeQ_surjective : Function.Surjective (placeQ K L hKL S) := by
  intro w
  let φ : ↥(levelField K L hKL) →+* ℂ := w.embedding
  letI : Algebra ↥(levelField K L hKL) ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic ↥K Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥K
  haveI : Algebra.IsAlgebraic ↥(levelField K L hKL) Qbar := Algebra.IsAlgebraic.tower_top (K := ↥K) _
  let Φ : Qbar →ₐ[↥(levelField K L hKL)] ℂ := IsAlgClosed.lift
  let Φ' : Qbar →ₐ[ℚ] ℂ := Φ.toRingHom.toRatAlgHom
  let x : Γ := Φ'.restrictNormal' Qbar
  have hx : ∀ z : Qbar, complexEmbedding (x z) = Φ' z := fun z => by
    have := AlgHom.restrictNormal_commutes Φ' Qbar z
    exact this
  refine ⟨Quotient.mk'' ((x⁻¹ : Γ) : X S), ?_⟩
  rw [placeQ_mk_mk, ← NumberField.InfinitePlace.mk_embedding w]
  congr 1
  apply RingHom.ext
  intro y
  rw [emb_apply, inv_inv, hx]
  show Φ (algebraMap ↥(levelField K L hKL) Qbar y) = φ y
  rw [Φ.commutes]
  rfl

end PlacesInf

open PlacesInf in
theorem solution
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) :
    ∃ e : placesAbove L S (Sum.inl ()) ≃ NumberField.InfinitePlace ↥(levelField K L hKL),
      ∀ (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inl ())),
        e ((orbitQuotientAction K L hnorm ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)).smul γ x) =
          levelGal K L hKL γ • e x :=
  ⟨Equiv.ofBijective (placeQ K L hKL S) ⟨placeQ_injective K L hKL S, placeQ_surjective K L hKL S⟩,
    placeQ_smul K L hKL S hnorm⟩

end S_NumberField_LevelArith_exists_placesAbove_inl_equiv_infinitePlace
end P2MW
export P2MW.S_NumberField_LevelArith_exists_placesAbove_inl_equiv_infinitePlace (solution)
