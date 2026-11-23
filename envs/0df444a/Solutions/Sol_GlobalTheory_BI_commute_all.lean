-- Prove2me | solution 1 for GlobalTheory.BI.commute_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:46.649935+00:00
-- url     : https://prove2.me/submissions/e95bb641-ea5f-4455-a252-efe0190a3dce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (M : Type) [Monoid M] (φ : G →* M), _root_.GlobalTheory.BI.AbByP G → (∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, φ a * φ b = φ b * φ a) → ∀ b ∈ B, ∀ g : G, φ b * φ g = φ g * φ b) → ∀ a b : G, φ a * φ b = φ b * φ a := by
  intro G _ _ M _ φ hG hyp
  obtain ⟨p, hp, A, hAn, hAc, hpow⟩ := hG
  let Z : Subgroup G :=
    { carrier := {b | ∀ g, φ b * φ g = φ g * φ b}
      mul_mem' := fun {x y} hx hy g => by
        rw [map_mul, mul_assoc, hy g, ← mul_assoc, hx g, mul_assoc]
      one_mem' := fun g => by simp
      inv_mem' := fun {x} hx g => by
        have h1 : φ x⁻¹ * φ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h2 : φ x * φ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        calc φ x⁻¹ * φ g = φ x⁻¹ * φ g * (φ x * φ x⁻¹) := by rw [h2, mul_one]
          _ = φ x⁻¹ * (φ x * φ g) * φ x⁻¹ := by rw [hx g]; simp only [mul_assoc]
          _ = φ g * φ x⁻¹ := by rw [← mul_assoc, h1, one_mul] }
  have hZ : ∀ b, b ∈ Z ↔ ∀ g, φ b * φ g = φ g * φ b := fun b => Iff.rfl
  have hZn : Z.Normal := ⟨fun b hb g => by
    rw [hZ] at hb ⊢
    intro h
    have e : φ (g * b * g⁻¹) = φ b := by
      rw [map_mul, map_mul, ← hb g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [e]
    exact hb h⟩
  have hAZ : A ≤ Z := fun a ha => (hZ a).2 (hyp A hAn (fun x hx y hy => by
    rw [← map_mul, ← map_mul, hAc x hx y hy]) a ha)
  suffices hZtop : Z = ⊤ by
    intro a b
    exact (hZ a).1 (hZtop ▸ Subgroup.mem_top a) b
  by_contra hne
  have hP : IsPGroup p (G ⧸ Z) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := hpow g
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hAZ hk⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (G ⧸ Z) := QuotientGroup.nontrivial_iff.mpr hne
  haveI := hP.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (G ⧸ Z))
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (z : G ⧸ Z)
  have hzc : ∀ q : G ⧸ Z, ∀ i : ℤ, q * (z : G ⧸ Z) ^ i = (z : G ⧸ Z) ^ i * q := fun q i =>
    ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ z.2 i)) q)
  let C : Subgroup G := (Subgroup.zpowers (z : G ⧸ Z)).comap (QuotientGroup.mk' Z)
  have hmemC : ∀ c ∈ C, ∃ i : ℤ, ∃ b ∈ Z, c = g ^ i * b := by
    intro c hc
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine ⟨i, (g ^ i)⁻¹ * c, ?_, by group⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hg]
    exact hi
  have hCn : C.Normal := ⟨fun c hc h => by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hi ⊢
    rw [← hi, hzc, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hCc : ∀ x ∈ C, ∀ y ∈ C, φ x * φ y = φ y * φ x := by
    intro x hx y hy
    obtain ⟨i, b1, hb1, rfl⟩ := hmemC x hx
    obtain ⟨j, b2, hb2, rfl⟩ := hmemC y hy
    rw [hZ] at hb1 hb2
    have key : ∀ (i j : ℤ) (b1 b2 : G), (∀ g, φ b1 * φ g = φ g * φ b1) →
        φ (g ^ i * b1) * φ (g ^ j * b2) = φ (g ^ (i + j)) * (φ b1 * φ b2) := by
      intro i j b1 b2 hb1
      rw [map_mul, map_mul, mul_assoc, ← mul_assoc (φ b1), hb1, mul_assoc, ← mul_assoc,
        ← map_mul, ← zpow_add]
    rw [key i j b1 b2 hb1, key j i b2 b1 hb2, add_comm, hb1 b2]
  have hgC : g ∈ C := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp [hg]⟩
  have hgZ : g ∈ Z := (hZ g).2 (hyp C hCn hCc g hgC)
  apply hz1
  apply Subtype.ext
  rw [← hg]
  exact (QuotientGroup.eq_one_iff g).mpr hgZ
end _root_.GlobalTheory.BI
end GlobalTheory.BI
