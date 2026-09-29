-- Prove2me | solution 1 for MegiddoLP.FixedDim.oracle_caseI
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:37:00.416021+00:00
-- url     : https://prove2.me/submissions/9eb30cca-4ade-4227-affc-b5a14ad0db4a

import Mathlib
import Definitions.Def_Polyhedron

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

theorem aux_oci_step {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (b : Fin n → ℝ)
    (xs w : Fin (d + 1) → ℝ) (hxs : xs ∈ polyhedron A b)
    (hw : ∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ w) :
    ∃ ε : ℝ, 0 < ε ∧ xs + ε • w ∈ polyhedron A b := by
  have hxs' : b ≤ A *ᵥ xs := hxs
  have key : ∀ i, ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      b i ≤ A i ⬝ᵥ xs + ε * A i ⬝ᵥ w := by
    intro i
    have hi : b i ≤ A i ⬝ᵥ xs := hxs' i
    rcases hi.lt_or_eq with hlt | heq
    · have ht : Filter.Tendsto (fun ε : ℝ => A i ⬝ᵥ xs + ε * A i ⬝ᵥ w) (nhds 0)
          (nhds (A i ⬝ᵥ xs)) := by
        have : Continuous (fun ε : ℝ => A i ⬝ᵥ xs + ε * A i ⬝ᵥ w) := by fun_prop
        simpa using this.tendsto 0
      exact nhdsWithin_le_nhds ((ht.eventually (lt_mem_nhds hlt)).mono fun ε h => h.le)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have h1 := hw i heq.symm
      have h2 : 0 ≤ ε * A i ⬝ᵥ w := mul_nonneg (le_of_lt hε) h1
      linarith
  have hall := (Filter.eventually_all.2 key).and self_mem_nhdsWithin
  obtain ⟨ε, hε, hpos⟩ := hall.exists
  refine ⟨ε, hpos, ?_⟩
  intro i
  show b i ≤ A i ⬝ᵥ (xs + ε • w)
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  exact hε i

theorem aux_oci_side {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (b : Fin n → ℝ)
    (c xs : Fin (d + 1) → ℝ) (hxs : xs ∈ polyhedron A b) (hxd : xs (Fin.last d) = 0)
    (σ : ℝ) (hσ : σ * σ = 1) :
    (∃ y ∈ polyhedron A b, 0 < σ * y (Fin.last d) ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = σ ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0 := by
  constructor
  · rintro ⟨y, hy, hyd, hcy⟩
    set r := σ * y (Fin.last d) with hr
    have hy' : b ≤ A *ᵥ y := hy
    have hrinv : 0 < r⁻¹ := inv_pos.2 hyd
    refine ⟨r⁻¹ • (y - xs), ?_, ?_, ?_⟩
    · have hyr : y (Fin.last d) = σ * r := by
        rw [hr, ← mul_assoc, hσ, one_mul]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hxd, sub_zero]
      rw [hyr]
      field_simp
    · intro i hi
      rw [dotProduct_smul, dotProduct_sub, smul_eq_mul, hi]
      have : b i ≤ A i ⬝ᵥ y := hy' i
      exact mul_nonneg hrinv.le (by linarith)
    · rw [dotProduct_smul, dotProduct_sub, smul_eq_mul]
      exact mul_neg_of_pos_of_neg hrinv (by linarith)
  · rintro ⟨z, hzd, hzI, hcz⟩
    obtain ⟨ε, hε, hmem⟩ := aux_oci_step A b xs z hxs hzI
    refine ⟨xs + ε • z, hmem, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxd, hzd, zero_add]
      have : σ * (ε * σ) = ε := by
        calc σ * (ε * σ) = ε * (σ * σ) := by ring
          _ = ε := by rw [hσ, mul_one]
      rw [this]; exact hε
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have : ε * c ⬝ᵥ z < 0 := mul_neg_of_pos_of_neg hε hcz
      linarith

end MegiddoLP.FixedDim

open Matrix LinearOptimization MegiddoLP.FixedDim

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (b : Fin n → ℝ)
    (c xs : Fin (d + 1) → ℝ)
    (hxs : IsLpOptimal c (polyhedron A b ∩ {x | x (Fin.last d) = 0}) xs) :
    ((∃ y ∈ polyhedron A b, 0 < y (Fin.last d) ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
    ((∃ y ∈ polyhedron A b, y (Fin.last d) < 0 ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
    ¬ ((∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
       (∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0)) ∧
    ((¬ ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) →
     (¬ ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) →
     IsLpOptimal c (polyhedron A b) xs) := by
  obtain ⟨⟨hxP, hxd⟩, hopt⟩ := hxs
  have hxd' : xs (Fin.last d) = 0 := hxd
  have P1 : (∃ y ∈ polyhedron A b, 0 < y (Fin.last d) ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0 := by
    have := aux_oci_side A b c xs hxP hxd' 1 (by norm_num)
    simpa using this
  have P2 : (∃ y ∈ polyhedron A b, y (Fin.last d) < 0 ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0 := by
    have := aux_oci_side A b c xs hxP hxd' (-1) (by norm_num)
    simpa using this
  refine ⟨P1, P2, ?_, ?_⟩
  · rintro ⟨⟨z1, hz1d, hz1I, hcz1⟩, ⟨z2, hz2d, hz2I, hcz2⟩⟩
    have hwI : ∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ (z1 + z2) := by
      intro i hi
      rw [dotProduct_add]
      have := hz1I i hi
      have := hz2I i hi
      linarith
    obtain ⟨ε, hε, hmem⟩ := aux_oci_step A b xs (z1 + z2) hxP hwI
    have hd : (xs + ε • (z1 + z2)) (Fin.last d) = 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxd', hz1d, hz2d]
      ring
    have hle := hopt _ ⟨hmem, hd⟩
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_add] at hle
    have : ε * (c ⬝ᵥ z1 + c ⬝ᵥ z2) < 0 := mul_neg_of_pos_of_neg hε (by linarith)
    linarith
  · intro h1 h2
    refine ⟨hxP, fun y hy => ?_⟩
    by_contra hlt
    push Not at hlt
    rcases lt_trichotomy (y (Fin.last d)) 0 with h | h | h
    · exact h2 (P2.1 ⟨y, hy, h, hlt⟩)
    · have := hopt y ⟨hy, h⟩
      linarith
    · exact h1 (P1.1 ⟨y, hy, h, hlt⟩)
