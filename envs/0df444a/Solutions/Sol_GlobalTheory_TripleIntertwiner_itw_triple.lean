-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.itw_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:29.453864+00:00
-- url     : https://prove2.me/submissions/0789274a-c01a-4b5e-8127-04840e5464e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
import Theorems.Thm_GlobalTheory_TripleIntertwiner_itw_eq
import Theorems.Thm_GlobalTheory_TripleIntertwiner_proj_triple
import Theorems.Thm_GlobalTheory_TripleIntertwiner_gauss_triple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]
variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A B C : AddSubgroup V}
    (fA : (A ⊓ B ⊓ C).relIndex A ≠ 0) (fB : (A ⊓ B ⊓ C).relIndex B ≠ 0) (fC : (A ⊓ B ⊓ C).relIndex C ≠ 0)
    (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1) (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (cC : ∀ x ∈ C, ∀ y ∈ C, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (f : F) (hf : ∀ x ∈ A, W x f = f)
    (h1 : ∀ x ∈ B, W x (itw W A B f) = itw W A B f)
    (h2 : ∀ x ∈ C, W x (itw W B C (itw W A B f)) = itw W B C (itw W A B f))
    (h3 : ∀ x ∈ C, W x (itw W A C f) = itw W A C f)
    (h4 : ∀ x ∈ B, W x (itw W C B (itw W A C f)) = itw W C B (itw W A C f)) :
    ∃ μ μ' : ℂ, μ ^ 4 = μ' ^ 4 ∧ itw W C A (itw W B C (itw W A B f)) = μ • f ∧
      itw W B A (itw W C B (itw W A C f)) = μ' • f := by
  set A₀ := A ⊓ B ⊓ C with hA₀
  have hA : A₀ ≤ A := inf_le_left.trans inf_le_left
  have hB : A₀ ≤ B := inf_le_left.trans inf_le_right
  have hC : A₀ ≤ C := inf_le_right
  haveI : Finite (A ⧸ A₀.addSubgroupOf A) := Nat.finite_of_card_ne_zero fA
  haveI : Finite (B ⧸ A₀.addSubgroupOf B) := Nat.finite_of_card_ne_zero fB
  haveI : Finite (C ⧸ A₀.addSubgroupOf C) := Nat.finite_of_card_ne_zero fC
  letI : Fintype (A ⧸ A₀.addSubgroupOf A) := Fintype.ofFinite _
  letI : Fintype (B ⧸ A₀.addSubgroupOf B) := Fintype.ofFinite _
  letI : Fintype (C ⧸ A₀.addSubgroupOf C) := Fintype.ofFinite _
  obtain ⟨r1, s1, e1⟩ := itw_eq H hA hB cB f hf
  obtain ⟨r2, s2, e2⟩ := itw_eq H hB hC cC _ h1
  obtain ⟨r3, s3, e3⟩ := itw_eq H hC hA cA _ h2
  obtain ⟨r4, s4, e4⟩ := itw_eq H hA hC cC f hf
  obtain ⟨r5, s5, e5⟩ := itw_eq H hC hB cB _ h3
  obtain ⟨r6, s6, e6⟩ := itw_eq H hB hA cA _ h4
  have t1 := proj_triple H hB hC cA cB cC hsd f hf
  have t2 := proj_triple H hC hB cA cC cB hsd f hf
  have g := gauss_triple H hA hB hC cA cB cC
  generalize (∑ z : C ⧸ A₀.addSubgroupOf C, ∑ y : B ⧸ A₀.addSubgroupOf B,
        if rep z + rep y ∈ A then c (rep z) (rep y) else 0) = S at t1 g
  generalize (∑ y : B ⧸ A₀.addSubgroupOf B, ∑ z : C ⧸ A₀.addSubgroupOf C,
        if rep y + rep z ∈ A then c (rep y) (rep z) else 0) = S' at t2 g
  refine ⟨r3 * r2 * r1 * ((A₀.relIndex A : ℂ) * S), r6 * r5 * r4 * ((A₀.relIndex A : ℂ) * S'), ?_, ?_, ?_⟩
  rotate_left
  · rw [e3, e2, e1]
    simp only [map_smul, ← Finset.smul_sum]
    rw [t1, smul_smul, smul_smul, smul_smul]
  · rw [e6, e5, e4]
    simp only [map_smul, ← Finset.smul_sum]
    rw [t2, smul_smul, smul_smul, smul_smul]
  · rw [inf_comm C A] at s3
    rw [inf_comm C B] at s5
    rw [inf_comm B A] at s6
    have hr : (r3 * r2 * r1) ^ 2 = (r6 * r5 * r4) ^ 2 := by
      set a := (A₀.relIndex A : ℂ)
      set b := (A₀.relIndex B : ℂ)
      set d := (A₀.relIndex C : ℂ)
      set ab := (A₀.relIndex (A ⊓ B) : ℂ)
      set ac := (A₀.relIndex (A ⊓ C) : ℂ)
      set bc := (A₀.relIndex (B ⊓ C) : ℂ)
      have p1 : (r3 * r2 * r1) ^ 2 * (a * b * d * ab * ac * bc) = 1 := by
        calc _ = (r1 ^ 2 * (b * ab)) * (r2 ^ 2 * (d * bc)) * (r3 ^ 2 * (a * ac)) := by ring
          _ = 1 := by rw [s1, s2, s3]; ring
      have p2 : (r6 * r5 * r4) ^ 2 * (a * b * d * ab * ac * bc) = 1 := by
        calc _ = (r4 ^ 2 * (d * ac)) * (r5 ^ 2 * (b * bc)) * (r6 ^ 2 * (a * ab)) := by ring
          _ = 1 := by rw [s4, s5, s6]; ring
      rw [eq_inv_of_mul_eq_one_left p1, eq_inv_of_mul_eq_one_left p2]
    have hr4 : (r3 * r2 * r1) ^ 4 = (r6 * r5 * r4) ^ 4 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, pow_mul, hr]
    rw [mul_pow, mul_pow (r6 * r5 * r4), hr4, mul_pow (A₀.relIndex A : ℂ), mul_pow (A₀.relIndex A : ℂ), g]
end GlobalTheory.TripleIntertwiner
