-- Prove2me | solution 1 for IsGaloisGroup.exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/567812cd-f326-597e-8db5-0238ce7dcd20

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard

set_option autoImplicit false

namespace ReynoldsKit

open scoped BigOperators

variable {O B : Type*} [CommRing O] [CommRing B] [Algebra O B]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B]

def osum (b : B) : B := ∑ g : G, g • b

theorem smul_osum (h : G) (b : B) : h • osum G b = osum G b := by
  unfold osum
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => rfl)

omit [SMulCommClass G O B] in
theorem osum_add (b c : B) : osum G (b + c) = osum G b + osum G c := by
  unfold osum; rw [← Finset.sum_add_distrib]; simp_rw [smul_add]

omit [SMulCommClass G O B] in
theorem osum_mul_of_invariant (a b : B) (ha : ∀ g : G, g • a = a) : osum G (a * b) = a * osum G b := by
  unfold osum; rw [Finset.mul_sum]; simp_rw [smul_mul', ha]

omit [SMulCommClass G O B] in
theorem osum_of_invariant (b : B) (hb : ∀ g : G, g • b = b) : osum G b = (Fintype.card G : B) * b := by
  unfold osum; simp_rw [hb]; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable (u : O) (hu : u * (Fintype.card G : O) = 1)

def rey (b : B) : B := algebraMap O B u * osum G b

theorem smul_rey (h : G) (b : B) : h • rey G u b = rey G u b := by
  unfold rey; rw [smul_mul', smul_algebraMap, smul_osum]

omit [SMulCommClass G O B] in
include hu in
theorem rey_of_invariant (b : B) (hb : ∀ g : G, g • b = b) : rey G u b = b := by
  unfold rey
  rw [osum_of_invariant G b hb, ← mul_assoc, ← map_natCast (algebraMap O B), ← map_mul, hu, map_one, one_mul]

omit [SMulCommClass G O B] in
theorem rey_add (b c : B) : rey G u (b + c) = rey G u b + rey G u c := by
  unfold rey; rw [osum_add, mul_add]

omit [SMulCommClass G O B] in
theorem rey_zero : rey G u (0 : B) = 0 := by
  unfold rey osum; simp

omit [SMulCommClass G O B] in
theorem rey_mul_of_invariant (a b : B) (ha : ∀ g : G, g • a = a) : rey G u (a * b) = a * rey G u b := by
  unfold rey; rw [osum_mul_of_invariant G a b ha]; ring

theorem rey_algebraMap_mul (r : O) (b : B) : rey G u (algebraMap O B r * b) = algebraMap O B r * rey G u b :=
  rey_mul_of_invariant G u _ _ (fun g => smul_algebraMap g r)

omit [SMulCommClass G O B] in
include hu in

theorem rey_sub_mem (J : Ideal B) (b : B) (hb : ∀ g : G, g • b - b ∈ J) : rey G u b - b ∈ J := by
  have h1 : rey G u b - b = algebraMap O B u * ∑ g : G, (g • b - b) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_sub, ← mul_assoc,
      ← map_natCast (algebraMap O B), ← map_mul, hu, map_one, one_mul]
    rfl
  rw [h1]
  exact Ideal.mul_mem_left _ _ (J.sum_mem fun g _ => hb g)

end ReynoldsKit

open ReynoldsKit

theorem solution
    (O A B : Type) [CommRing O] [IsNoetherianRing O] [CommRing A] [CommRing B]
    [Algebra O A] [Algebra O B] [Algebra A B] [IsScalarTower O A B] [Algebra.FiniteType O B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G O B]
    [IsGaloisGroup G A B] [FaithfulSMul A B]
    (hG : IsUnit ((Nat.card G : ℕ) : O)) :
    (∃ r : B →ₗ[A] A, ∀ a : A, r (algebraMap A B a) = a) ∧
    (∀ 𝔞 : Ideal O,
      (∀ a : A, algebraMap A B a ∈ 𝔞.map (algebraMap O B) → a ∈ 𝔞.map (algebraMap O A)) ∧
      (∀ b : B, (∀ g : G, g • b - b ∈ 𝔞.map (algebraMap O B)) →
        ∃ a : A, algebraMap A B a - b ∈ 𝔞.map (algebraMap O B))) ∧
    Module.Finite A B ∧ Algebra.FiniteType O A ∧
    (Module.Flat O B → Module.Flat O A) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B

  obtain ⟨u, hu⟩ : ∃ u : O, u * (Fintype.card G : O) = 1 :=
    ⟨((hG.unit⁻¹ : Oˣ) : O), by rw [← Nat.card_eq_fintype_card]; exact hG.val_inv_mul⟩

  have hA : ∀ a : A, ∀ g : G, g • algebraMap A B a = algebraMap A B a := fun a g => smul_algebraMap g a

  let toA : B → A := fun b => (IsGaloisGroup.ringEquivFixedPoints G A B).symm ⟨rey G u b, fun g => smul_rey G u g b⟩
  have htoA : ∀ b : B, algebraMap A B (toA b) = rey G u b := fun b =>
    IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply G A B ⟨rey G u b, fun g => smul_rey G u g b⟩
  have htoA_alg : ∀ a : A, toA (algebraMap A B a) = a := fun a =>
    hinj (by rw [htoA, rey_of_invariant G u hu _ (hA a)])

  let r : B →ₗ[A] A :=
    { toFun := toA
      map_add' := fun b c => hinj (by rw [map_add, htoA, htoA, htoA, rey_add])
      map_smul' := fun a b => hinj (by
        rw [RingHom.id_apply, htoA, Algebra.smul_def, smul_eq_mul, map_mul, htoA,
          rey_mul_of_invariant G u _ _ (hA a)]) }
  refine ⟨⟨r, htoA_alg⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro 𝔞
    refine ⟨?_, ?_⟩
    · intro a ha

      have key : ∀ x ∈ 𝔞.map (algebraMap O B), ∀ c : B,
          ∃ a' ∈ 𝔞.map (algebraMap O A), algebraMap A B a' = rey G u (c * x) := by
        intro x hx
        refine Submodule.span_induction (p := fun x _ => ∀ c : B,
          ∃ a' ∈ 𝔞.map (algebraMap O A), algebraMap A B a' = rey G u (c * x)) ?_ ?_ ?_ ?_ hx
        · rintro y ⟨s, hs, rfl⟩ c
          refine ⟨algebraMap O A s * toA c, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hs), ?_⟩
          rw [map_mul, htoA, ← IsScalarTower.algebraMap_apply, mul_comm c, rey_algebraMap_mul]
        · intro c
          exact ⟨0, Ideal.zero_mem _, by rw [map_zero, mul_zero, rey_zero]⟩
        · intro x y _ _ hx hy c
          obtain ⟨a₁, ha₁, e₁⟩ := hx c
          obtain ⟨a₂, ha₂, e₂⟩ := hy c
          exact ⟨a₁ + a₂, Ideal.add_mem _ ha₁ ha₂, by rw [map_add, e₁, e₂, mul_add, rey_add]⟩
        · intro d x _ hx c
          obtain ⟨a₁, ha₁, e₁⟩ := hx (c * d)
          exact ⟨a₁, ha₁, by rw [e₁, smul_eq_mul, mul_assoc]⟩
      obtain ⟨a', ha', e⟩ := key _ ha 1
      rw [one_mul, rey_of_invariant G u hu _ (hA a)] at e
      rw [← hinj e]
      exact ha'
    · intro b hb
      exact ⟨toA b, by rw [htoA]; exact rey_sub_mem G u hu _ b hb⟩
  ·
    haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
    haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType O A B
    exact Algebra.IsIntegral.finite
  ·
    haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
    haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType O A B
    haveI hfin : Module.Finite A B := Algebra.IsIntegral.finite
    exact ⟨fg_of_fg_of_fg O A B Algebra.FiniteType.out (Module.finite_def.mp hfin) hinj⟩
  ·
    intro hflat
    haveI := hflat
    let i : A →ₗ[O] B := (IsScalarTower.toAlgHom O A B).toLinearMap
    let rO : B →ₗ[O] A := r.restrictScalars O
    exact Module.Flat.of_retract i rO (by
      ext a
      exact htoA_alg a)

end S_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard
end P2MW
export P2MW.S_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard (solution)
