-- Prove2me | solution 1 for GlobalTheory.exists_weight_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:49.531788+00:00
-- url     : https://prove2.me/submissions/9b8a4c3a-f1c1-48c1-a021-bd2734430fe5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsWeightIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G)
    (lam : B →* Lˣ) (v : V) (hB : B.Normal) (hv : v ≠ 0)
    (hlam : ∀ b : B, ρ b v = (lam b : L) • v)
    (hT : ∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) :
    ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧
      (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  have hc : (Fintype.card B : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set s : Module.End L V := ∑ b : B, (((lam b)⁻¹ : Lˣ) : L) • ρ b with hs
  set e : Module.End L V := (Fintype.card B : L)⁻¹ • s with he
  have h1 : ∀ b : B, ρ b * s = (lam b : L) • s := by
    intro b
    rw [hs, Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ ?_
    intro c
    simp only [Equiv.coe_mulLeft, map_mul, Subgroup.coe_mul, smul_smul, mul_smul_comm]
    congr 1
    simp [mul_comm]
  have h1e : ∀ b : B, ρ b * e = (lam b : L) • e := by
    intro b
    rw [he, mul_smul_comm, h1, smul_comm]
  have h2 : ∀ f : Module.End L V, (∀ b : B, ρ b * f = (lam b : L) • f) → e * f = f := by
    intro f hf
    rw [he, smul_mul_assoc, hs, Finset.sum_mul]
    have : ∀ b : B, ((((lam b)⁻¹ : Lˣ) : L) • ρ b) * f = f := by
      intro b
      rw [smul_mul_assoc, hf, smul_smul]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hev : e v = v := by
    rw [he, hs]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, hlam, smul_smul, Units.inv_mul, one_smul,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let κ : G → B ≃* B := fun g => (MulAut.conjNormal (H := B) g⁻¹)
  have hκ : ∀ g (b : B), (κ g b : G) = g⁻¹ * b * g := by
    intro g b
    simp [κ]
  have hcomm : ∀ g (b : B), ρ b * ρ g = ρ g * ρ (κ g b) := by
    intro g b
    rw [← map_mul, ← map_mul, hκ]
    congr 1
    group
  refine ⟨e, ?_, h2 e h1e, h1e, ?_, ?_⟩
  · intro h
    rw [h] at hev
    exact hv hev.symm
  · intro t ht
    have ht' := (hT t).1 ht
    rw [he, mul_smul_comm, smul_mul_assoc, hs, Finset.mul_sum, Finset.sum_mul]
    congr 1
    symm
    refine Fintype.sum_equiv (κ t).toEquiv _ _ ?_
    intro b
    have := ht' b (κ t b) (hκ t b)
    rw [smul_mul_assoc, mul_smul_comm, hcomm, ← this]
    rfl
  · intro g hg
    let f : B →* L := (Units.coeHom L).comp (lam⁻¹ * lam.comp (κ g).toMonoidHom)
    have hf : f ≠ 1 := by
      intro h
      apply hg
      rw [hT]
      intro b b' hb
      have hb' : b' = κ g b := Subtype.ext (by rw [hb, hκ])
      have h3 : f b = 1 := by rw [h]; rfl
      have h4 : (lam b)⁻¹ * lam (κ g b) = 1 := Units.ext h3
      rw [hb']
      exact (inv_mul_eq_one.mp h4).symm
    have h0 := sum_hom_units_eq_zero f hf
    have : s * ρ g * e = 0 := by
      rw [hs, Finset.sum_mul, Finset.sum_mul]
      have : ∀ b : B, ((((lam b)⁻¹ : Lˣ) : L) • ρ b) * ρ g * e = f b • (ρ g * e) := by
        intro b
        rw [smul_mul_assoc, smul_mul_assoc, hcomm, mul_assoc, h1e, mul_smul_comm, smul_smul]
        rfl
      simp only [this]
      rw [← Finset.sum_smul, h0, zero_smul]
    calc e * ρ g * e = (Fintype.card B : L)⁻¹ • (s * ρ g * e) := by
          rw [← smul_mul_assoc, ← smul_mul_assoc]
      _ = 0 := by rw [this, smul_zero]
end GlobalTheory
