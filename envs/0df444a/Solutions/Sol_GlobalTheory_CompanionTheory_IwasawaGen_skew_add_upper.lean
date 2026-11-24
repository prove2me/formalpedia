-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:45.735881+00:00
-- url     : https://prove2.me/submissions/bf0f2f34-680f-4f64-b7c7-316bd6045d47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CartanDecompositionLieAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwasawaGen
namespace GlobalTheory.CompanionTheory.IwasawaGen
theorem _root_.solution {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hanti : Antitone h)
    (hf : ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤)
    (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hreg : ∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) :
    ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  intro X hX
  obtain ⟨P, hP, P_ent⟩ : ∃ P ∈ 𝔤, ∀ i j, P i j = if h j < h i then X i j else 0 := by
    refine ⟨_, hf (fun t => if 0 < t then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h j < h i
    · simp [hij]
    · simp [hij]
  obtain ⟨Z, hZ, Z_ent⟩ : ∃ Z ∈ 𝔤, ∀ i j, Z i j = if h i = h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t = 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i = h j
    · simp [hij]
    · simp [hij, sub_eq_zero]
  obtain ⟨M, hM, M_ent⟩ : ∃ M ∈ 𝔤, ∀ i j, M i j = if h i < h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t < 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i < h j
    · simp [hij]
    · simp [hij]
  have hsum : X = P + Z + M := by
    ext i j
    simp only [Matrix.add_apply, P_ent, Z_ent, M_ent]
    rcases lt_trichotomy (h i) (h j) with hij | hij | hij
    · simp [hij, hij.ne, not_lt.2 hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt.2 hij.le]
  set Y : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (Z + Zᴴ) with hYdef
  have hY : Y ∈ 𝔤 := 𝔤.smul_mem _ (𝔤.add_mem hZ (hstar Z hZ))
  have Y_herm : Yᴴ = Y := by
    ext i j
    simp [hYdef, Matrix.conjTranspose_apply, add_comm]
  have Y_ent : ∀ i j, h i ≠ h j → Y i j = 0 := by
    intro i j hij
    simp [hYdef, Matrix.conjTranspose_apply, Z_ent, hij, hij.symm]
  have Y_comm : Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : h i = h j
    · rw [hij, mul_comm]
    · rw [Y_ent i j hij]; simp
  have Y_diag : Y.IsDiag := hreg Y hY Y_herm Y_comm
  refine ⟨(1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ, ?_, P + Y + Mᴴ, ?_, ?_, ?_, ?_⟩
  · exact 𝔤.sub_mem (𝔤.add_mem (𝔤.smul_mem _ (𝔤.sub_mem hZ (hstar Z hZ))) hM) (hstar M hM)
  · exact 𝔤.add_mem (𝔤.add_mem hP hY) (hstar M hM)
  · have hZsplit : Z = (1 / 2 : ℝ) • (Z - Zᴴ) + Y := by
      rw [hYdef, ← smul_add]
      have : Z - Zᴴ + (Z + Zᴴ) = (2 : ℝ) • Z := by
        rw [two_smul]; abel
      rw [this, smul_smul]; norm_num
    calc X = P + Z + M := hsum
      _ = P + ((1 / 2 : ℝ) • (Z - Zᴴ) + Y) + M := by rw [← hZsplit]
      _ = (1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ + (P + Y + Mᴴ) := by abel
  · simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_trivial]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply]
    simp only [smul_eq_mul, Complex.real_smul, smul_sub]
    ring
  · intro i j hji
    have hji' : j < i := hji
    have hle : h i ≤ h j := hanti hji'.le
    have h1 : P i j = 0 := by
      rw [P_ent, if_neg (not_lt.2 hle)]
    have h2 : Y i j = 0 := Y_diag hji'.ne'
    have h3 : Mᴴ i j = 0 := by
      rw [Matrix.conjTranspose_apply, M_ent, if_neg (not_lt.2 hle)]; simp
    simp only [Matrix.add_apply, h1, h2, h3, add_zero]
end GlobalTheory.CompanionTheory.IwasawaGen
