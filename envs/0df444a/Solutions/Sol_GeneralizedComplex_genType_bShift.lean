-- Prove2me | solution 1 for GeneralizedComplex.genType_bShift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:31:32.742784+00:00
-- url     : https://prove2.me/submissions/485b7d9f-9403-4ed7-8866-727adb96fe3f

import Mathlib
import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GCAux2
open GeneralizedComplex

lemma bShift_pairing' {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = -B)
    (u v : GIdx N → ℝ) :
    pairing (bShift B *ᵥ u) (bShift B *ᵥ v) = pairing u v := by
  unfold pairing bShift vecPart formPart
  simp only [fromBlocks_mulVec, Sum.elim_inl, Sum.elim_inr, one_mulVec, zero_mulVec, add_zero]
  have key : ∀ X Y : Fin N → ℝ, (Bᵀ *ᵥ X) ⬝ᵥ Y = -((Bᵀ *ᵥ Y) ⬝ᵥ X) := by
    intro X Y
    have h1 : (Bᵀ *ᵥ Y) ⬝ᵥ X = (B *ᵥ X) ⬝ᵥ Y := by
      rw [mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm]
    rw [h1, hB, neg_mulVec, neg_dotProduct]
  simp only [add_dotProduct]
  have := key (u ∘ Sum.inl) (v ∘ Sum.inl)
  simp only [Function.comp_def] at this ⊢
  linarith

lemma bShift_mul {𝕜 : Type*} [CommRing 𝕜] {N : ℕ} (B C : Matrix (Fin N) (Fin N) 𝕜) :
    bShift B * bShift C = bShift (B + C) := by
  unfold bShift
  rw [fromBlocks_multiply]
  simp [transpose_add, add_comm]

lemma bShift_zero {𝕜 : Type*} [CommRing 𝕜] {N : ℕ} : bShift (0 : Matrix (Fin N) (Fin N) 𝕜) = 1 := by
  unfold bShift; simp

lemma bShift_map {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) :
    (bShift B).map (fun x : ℝ => (x : ℂ)) = bShift (B.map (fun x : ℝ => (x : ℂ))) := by
  unfold bShift
  rw [fromBlocks_map]
  simp [transpose_map]

lemma vec_bShift {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (w : GIdx N → ℂ) :
    LinearMap.funLeft ℂ ℂ Sum.inl (bShift C *ᵥ w) = LinearMap.funLeft ℂ ℂ Sum.inl w := by
  ext i
  simp [bShift, fromBlocks_mulVec, LinearMap.funLeft_apply]

lemma map_mul' {N : ℕ} (A B : Matrix (GIdx N) (GIdx N) ℝ) :
    (A * B).map (fun x : ℝ => (x : ℂ)) = A.map (fun x : ℝ => (x : ℂ)) * B.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

lemma mem_plusI {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (v : GIdx N → ℂ) :
    v ∈ plusIEigenspace J ↔ J.map (fun x : ℝ => (x : ℂ)) *ᵥ v = Complex.I • v := by
  simp [plusIEigenspace, sub_eq_zero]

theorem main {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = -B) :
    IsGenAlmostComplex (bShift B * J * bShift (-B)) ∧
      genType (plusIEigenspace (bShift B * J * bShift (-B))) = genType (plusIEigenspace J) := by
  have i1 : bShift (-B) * bShift B = 1 := by rw [bShift_mul]; simp [bShift_zero]
  have i2 : bShift B * bShift (-B) = 1 := by rw [bShift_mul]; simp [bShift_zero]
  have hB' : (-B)ᵀ = -(-B) := by rw [transpose_neg, hB]
  constructor
  · constructor
    · calc bShift B * J * bShift (-B) * (bShift B * J * bShift (-B))
          = bShift B * J * (bShift (-B) * bShift B) * J * bShift (-B) := by simp only [Matrix.mul_assoc]
        _ = bShift B * (J * J) * bShift (-B) := by rw [i1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = -1 := by rw [hJ.sq_eq_neg_one]; simp [i2]
    · intro u v
      simp only [← mulVec_mulVec]
      rw [bShift_pairing' B hB, hJ.pairing_mulVec, bShift_pairing' (-B) hB']
  · unfold genType
    suffices hT : tangentProjection (plusIEigenspace (bShift B * J * bShift (-B))) =
        tangentProjection (plusIEigenspace J) by rw [hT]
    set c := fun x : ℝ => (x : ℂ)
    have hM : (bShift B * J * bShift (-B)).map c =
        bShift (B.map c) * J.map c * bShift ((-B).map c) := by
      rw [map_mul', map_mul', bShift_map, bShift_map]
    have j1 : bShift ((-B).map c) * bShift (B.map c) = 1 := by
      rw [← bShift_map, ← bShift_map, ← map_mul', i1]; simp
    have j2 : bShift (B.map c) * bShift ((-B).map c) = 1 := by
      rw [← bShift_map, ← bShift_map, ← map_mul', i2]; simp
    ext x
    simp only [tangentProjection, Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨bShift ((-B).map c) *ᵥ v, ?_, vec_bShift _ _⟩
      rw [mem_plusI] at hv ⊢
      rw [hM] at hv
      have := congrArg (fun w => bShift ((-B).map c) *ᵥ w) hv
      simp only [mulVec_mulVec, ← Matrix.mul_assoc, j1, Matrix.one_mul, mulVec_smul] at this
      rw [← mulVec_mulVec] at this
      exact this
    · rintro ⟨w, hw, rfl⟩
      refine ⟨bShift (B.map c) *ᵥ w, ?_, vec_bShift _ _⟩
      rw [mem_plusI] at hw ⊢
      rw [hM, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, j1, Matrix.mul_one,
        ← mulVec_mulVec, hw, mulVec_smul]

end GCAux2

open GeneralizedComplex in
theorem solution {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = -B) :
    IsGenAlmostComplex (bShift B * J * bShift (-B)) ∧
      genType (plusIEigenspace (bShift B * J * bShift (-B))) = genType (plusIEigenspace J) :=
  GCAux2.main J hJ B hB
