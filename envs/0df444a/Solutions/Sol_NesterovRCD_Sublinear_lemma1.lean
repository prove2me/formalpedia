-- Prove2me | solution 1 for NesterovRCD.Sublinear.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:35:18.457978+00:00
-- url     : https://prove2.me/submissions/3d1c6c52-3b86-4d8e-a56d-36912927b4d0

import Mathlib
set_option autoImplicit false
open Matrix

theorem lemma1_main {m k : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (y : Fin k → (Fin m → ℝ)) (L b : Fin k → ℝ) (hL : ∀ i, 0 < L i)
    (hab : ∀ i, y i ⬝ᵥ (A *ᵥ y i) ≤ L i * b i) :
    (∑ i, y i) ⬝ᵥ (A *ᵥ ∑ i, y i) ≤ (∑ i, L i) * ∑ i, b i := by
  set z : Fin m → ℝ := ∑ i, y i with hz
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [hz]
  have hS : 0 < ∑ i, L i :=
    Finset.sum_pos (fun i _ => hL i) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
  set S := ∑ i, L i with hSdef
  have hT : Aᵀ = A := by simpa using hA.1.eq
  have hsymm : ∀ v w : Fin m → ℝ, v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v) := by
    intro v w
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have hcross : ∑ i, y i ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ (A *ᵥ z) := by
    rw [hz, ← sum_dotProduct]
  have hexp : ∀ i, (y i - (L i / S) • z) ⬝ᵥ (A *ᵥ (y i - (L i / S) • z)) =
      y i ⬝ᵥ (A *ᵥ y i) - 2 * (L i / S) * (y i ⬝ᵥ (A *ᵥ z)) +
        (L i / S) ^ 2 * (z ⬝ᵥ (A *ᵥ z)) := by
    intro i
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hsymm z (y i)]
    ring
  have hnn : ∀ i, 0 ≤ y i ⬝ᵥ (A *ᵥ y i) - 2 * (L i / S) * (y i ⬝ᵥ (A *ᵥ z)) +
        (L i / S) ^ 2 * (z ⬝ᵥ (A *ᵥ z)) := by
    intro i
    rw [← hexp]
    exact hA.dotProduct_mulVec_nonneg _
  have hsum : 0 ≤ ∑ i, (1 / L i) * (y i ⬝ᵥ (A *ᵥ y i) - 2 * (L i / S) * (y i ⬝ᵥ (A *ᵥ z)) +
        (L i / S) ^ 2 * (z ⬝ᵥ (A *ᵥ z))) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by have := hL i; positivity) (hnn i)
  have hcalc : ∑ i, (1 / L i) * (y i ⬝ᵥ (A *ᵥ y i) - 2 * (L i / S) * (y i ⬝ᵥ (A *ᵥ z)) +
        (L i / S) ^ 2 * (z ⬝ᵥ (A *ᵥ z))) =
      ∑ i, (y i ⬝ᵥ (A *ᵥ y i)) / L i - (z ⬝ᵥ (A *ᵥ z)) / S := by
    have : ∀ i, (1 / L i) * (y i ⬝ᵥ (A *ᵥ y i) - 2 * (L i / S) * (y i ⬝ᵥ (A *ᵥ z)) +
        (L i / S) ^ 2 * (z ⬝ᵥ (A *ᵥ z))) =
        (y i ⬝ᵥ (A *ᵥ y i)) / L i - (2 / S) * (y i ⬝ᵥ (A *ᵥ z)) +
          (L i / S ^ 2) * (z ⬝ᵥ (A *ᵥ z)) := by
      intro i
      have := (hL i).ne'
      field_simp
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hcross]
    rw [← Finset.sum_div, ← hSdef]
    field_simp
    ring
  have hle : ∑ i, (y i ⬝ᵥ (A *ᵥ y i)) / L i ≤ ∑ i, b i := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [div_le_iff₀ (hL i)]
    linarith [hab i, mul_comm (L i) (b i)]
  have : (z ⬝ᵥ (A *ᵥ z)) / S ≤ ∑ i, b i := by linarith
  rw [div_le_iff₀ hS] at this
  linarith

theorem solution {m k : ℕ} (blk : Fin m → Fin k) (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (B : Fin k → Matrix (Fin m) (Fin m) ℝ) (L : Fin k → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hB : ∀ (i : Fin k) (x : Fin m → ℝ),
      0 ≤ (fun j => if blk j = i then x j else 0) ⬝ᵥ
        (B i *ᵥ fun j => if blk j = i then x j else 0))
    (hAB : ∀ (i : Fin k) (x : Fin m → ℝ),
      (fun j => if blk j = i then x j else 0) ⬝ᵥ (A *ᵥ fun j => if blk j = i then x j else 0)
        ≤ L i * ((fun j => if blk j = i then x j else 0) ⬝ᵥ
          (B i *ᵥ fun j => if blk j = i then x j else 0)))
    (x : Fin m → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ (∑ i, L i) *
      ∑ i, (fun j => if blk j = i then x j else 0) ⬝ᵥ
        (B i *ᵥ fun j => if blk j = i then x j else 0) := by
  set y : Fin k → (Fin m → ℝ) := fun i j => if blk j = i then x j else 0 with hy
  have hxy : ∑ i, y i = x := by
    funext j
    simp [hy, Finset.sum_apply]
  have hyi : ∀ i, (fun j => if blk j = i then x j else 0) = y i := fun i => rfl
  simp only [hyi] at hB hAB ⊢
  set b : Fin k → ℝ := fun i => y i ⬝ᵥ (B i *ᵥ y i) with hb
  have hb0 : ∀ i, 0 ≤ b i := fun i => hB i x
  have key : ∀ ε : ℝ, 0 < ε → x ⬝ᵥ (A *ᵥ x) ≤ (∑ i, L i + k * ε) * ∑ i, b i := by
    intro ε hε
    have h := lemma1_main A hA y (fun i => L i + ε) b (fun i => by have := hL i; positivity) (by
      intro i
      have := hAB i x
      have := hb0 i
      show _ ≤ (L i + ε) * b i
      nlinarith [hAB i x])
    rw [hxy] at h
    simpa [Finset.sum_add_distrib] using h
  have hc : 0 ≤ (k : ℝ) * ∑ i, b i := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hb0 i)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / ((k : ℝ) * ∑ i, b i + 1) := by positivity
  have h1 := key _ hδ
  have h2 : ε / ((k : ℝ) * ∑ i, b i + 1) * ((k : ℝ) * ∑ i, b i) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith
