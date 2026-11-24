-- Prove2me | solution 1 for GlobalTheory.QNorm.two_mul_index_sqs_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:50.427592+00:00
-- url     : https://prove2.me/submissions/c50884f3-c37c-432e-90c6-a908978a7198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulIndexSqsInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
private theorem mem_sqs_iff_exists_sq {G : Type} [CommGroup G] (U : Subgroup G) (x : G) :
    x ∈ sqs U ↔ ∃ y ∈ U, y ^ 2 = x := by
  simp [sqs, Subgroup.mem_map]
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) →
      (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε →
      (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) →
      2 * (sqs (⊤ : Subgroup A)).index =
        (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) *
          (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker := by
  intro A _ σ ε hσ h90 hε1 hε2 hσε h2
  set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB
  set N : Subgroup A := (MonoidHom.id A * σ).ker with hN
  set S : Subgroup A := sqs (⊤ : Subgroup A) with hS
  have memB : ∀ a, a ∈ B ↔ σ a = a := fun a => Iff.rfl
  have memN : ∀ a, a ∈ N ↔ a * σ a = 1 := fun a => Iff.rfl
  have memS : ∀ a, a ∈ S ↔ ∃ y, y ^ 2 = a := fun a => by
    rw [hS, mem_sqs_iff_exists_sq]; simp
  let f : A →* A := MonoidHom.id A / σ
  have hf : ∀ a, f a = a / σ a := fun a => rfl
  have hker : ∀ a, f a = 1 ↔ a ∈ B := fun a => by
    rw [hf, memB, div_eq_one, eq_comm]
  have hrange : f.range = N := by
    ext x
    rw [memN, MonoidHom.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      rw [hf, map_div, hσ]; simp
    · intro hx
      obtain ⟨b, hb⟩ := h90 x hx
      exact ⟨b, hb.symm⟩
  have hcomap : B ⊔ S = (sqs N).comap f := by
    apply le_antisymm
    · apply sup_le
      · intro a ha
        rw [Subgroup.mem_comap, (hker a).2 ha]
        exact one_mem _
      · intro a ha
        obtain ⟨y, rfl⟩ := (memS a).1 ha
        rw [Subgroup.mem_comap, mem_sqs_iff_exists_sq]
        exact ⟨f y, hrange ▸ ⟨y, rfl⟩, (map_pow f y 2).symm⟩
    · intro a ha
      rw [Subgroup.mem_comap, mem_sqs_iff_exists_sq] at ha
      obtain ⟨c, hc, hca⟩ := ha
      rw [← hrange] at hc
      obtain ⟨b, rfl⟩ := hc
      have h1 : a / b ^ 2 ∈ B := by
        rw [← hker, map_div, map_pow, hca, div_self']
      have : a = a / b ^ 2 * b ^ 2 := by simp
      rw [this]
      exact Subgroup.mul_mem_sup h1 ((memS _).2 ⟨b, rfl⟩)
  have e1 : (B ⊔ S).index = (sqs N).relIndex N := by
    rw [hcomap, Subgroup.index_comap, hrange]
  have e2 : S.relIndex (B ⊔ S) * (B ⊔ S).index = S.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have e3 : S.relIndex (B ⊔ S) = S.relIndex B := Subgroup.relIndex_sup_right B S
  have hle : sqs B ≤ S ⊓ B := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (mem_sqs_iff_exists_sq _ _).1 ha
    exact ⟨(memS _).2 ⟨y, rfl⟩, pow_mem hy 2⟩
  have e4 : (sqs B).relIndex (S ⊓ B) * (S ⊓ B).relIndex B = (sqs B).relIndex B :=
    Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_right
  have e5 : (S ⊓ B).relIndex B = S.relIndex B := Subgroup.inf_relIndex_right S B
  have hεB : ε ∈ B := hσε
  have key : ∀ y, y ^ 2 ∈ sqs B ↔ f y = 1 := by
    intro y
    rw [mem_sqs_iff_exists_sq, hker]
    constructor
    · rintro ⟨b, hb, hby⟩
      have : (y / b) ^ 2 = 1 := by rw [div_pow, hby, div_self']
      have hyb : y / b ∈ B := by
        rcases h2 _ this with h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact hεB
      simpa using mul_mem hyb hb
    · intro hy
      exact ⟨y, hy, rfl⟩
  obtain ⟨a0, ha0⟩ := h90 ε (by rw [hσε, ← sq, hε2])
  rw [← hf] at ha0
  have e6 : (sqs B).relIndex (S ⊓ B) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    have h0 : a0 ^ 2 ∈ S ⊓ B :=
      ⟨(memS _).2 ⟨a0, rfl⟩, (hker _).1 (by rw [map_pow, ← ha0, hε2])⟩
    refine ⟨⟨a0 ^ 2, h0⟩, ?_⟩
    rintro ⟨x, hxS, hxB⟩
    obtain ⟨y, rfl⟩ := (memS x).1 hxS
    have hy : f y ^ 2 = 1 := by rw [← map_pow]; exact (hker _).2 hxB
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [← mul_pow, key, key, map_mul, ← ha0]
    rcases h2 _ hy with h | h
    · rw [h, one_mul]
      exact Or.inr ⟨rfl, hε1⟩
    · rw [h, ← sq]
      exact Or.inl ⟨hε2, hε1⟩
  rw [← e2, e1, e3, ← e4, e5, e6, mul_assoc]
end GlobalTheory.QNorm
