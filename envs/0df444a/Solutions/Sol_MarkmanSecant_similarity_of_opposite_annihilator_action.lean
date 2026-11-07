-- Prove2me | solution 1 for MarkmanSecant.similarity_of_opposite_annihilator_action
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T04:30:44.554201+00:00
-- url     : https://prove2.me/submissions/2bd5cc2a-c387-45b2-a52e-99a664024a8d

import Theorems.Thm_MarkmanSecant_annih_isotropic
import Mathlib.LinearAlgebra.Dimension.Finrank

open MarkmanSecant Matrix
open scoped ExteriorAlgebra

private lemma pair_add_left {n : ℕ} (x y z : VC n) :
    pairV (x + y) z = pairV x z + pairV y z := by
  have hw : wPart (x + y) = wPart x + wPart y := rfl
  have ht : tPart (x + y) = tPart x + tPart y := rfl
  simp only [pairV, hw, ht, add_dotProduct, dotProduct_add]
  ring

private lemma pair_add_right {n : ℕ} (x y z : VC n) :
    pairV x (y + z) = pairV x y + pairV x z := by
  have hw : wPart (y + z) = wPart y + wPart z := rfl
  have ht : tPart (y + z) = tPart y + tPart z := rfl
  simp only [pairV, hw, ht, add_dotProduct, dotProduct_add]
  ring

private lemma pair_smul_left {n : ℕ} (c : ℂ) (x z : VC n) :
    pairV (c • x) z = c * pairV x z := by
  have hw : wPart (c • x) = c • wPart x := rfl
  have ht : tPart (c • x) = c • tPart x := rfl
  simp only [pairV, hw, ht, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

private lemma pair_smul_right {n : ℕ} (c : ℂ) (x z : VC n) :
    pairV x (c • z) = c * pairV x z := by
  have hw : wPart (c • z) = c • wPart z := rfl
  have ht : tPart (c • z) = c • tPart z := rfl
  simp only [pairV, hw, ht, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem solution (n : ℕ) (s t : Spinor n)
    (hs : IsEvenPureSpinor s) (ht : IsEvenPureSpinor t)
    (hst : annih s ⊓ annih t = ⊥) (c : ℂ) (f : VC n →ₗ[ℂ] VC n)
    (hfs : ∀ v ∈ annih s, f v = c • v)
    (hft : ∀ v ∈ annih t, f v = (-c) • v) :
    f ∘ₗ f = c ^ 2 • LinearMap.id ∧
      ∀ v w : VC n, pairV (f v) (f w) = -(c ^ 2) * pairV v w := by
  have hdim : Module.finrank ℂ (VC n) = 2 * n + 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hsup : annih s ⊔ annih t = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq (annih s) (annih t)
    rw [hst, finrank_bot, hs.2.2, ht.2.2] at h
    rw [hdim]
    omega
  have dec (v : VC n) : ∃ x ∈ annih s, ∃ y ∈ annih t, x + y = v := by
    apply Submodule.mem_sup.mp
    rw [hsup]
    trivial
  constructor
  · apply LinearMap.ext
    intro v
    obtain ⟨x, hx, y, hy, rfl⟩ := dec v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_add, map_smul, hfs x hx, hft y hy, smul_smul, neg_mul_neg, pow_two, smul_add]
  · intro v w
    obtain ⟨x, hx, y, hy, rfl⟩ := dec v
    obtain ⟨z, hz, u, hu, rfl⟩ := dec w
    have hxz := MarkmanSecant.annih_isotropic n s hs.2.1 x z hx hz
    have hyu := MarkmanSecant.annih_isotropic n t ht.2.1 y u hy hu
    rw [map_add, map_add, hfs x hx, hft y hy, hfs z hz, hft u hu]
    simp only [pair_add_left, pair_add_right, pair_smul_left, pair_smul_right, hxz, hyu]
    ring

#print axioms solution
