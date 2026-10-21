-- Prove2me | solution 1 for GraphLQGame.Equilibrium.remark_2_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:41:20.947615+00:00
-- url     : https://prove2.me/submissions/5da47344-c1cc-4c4d-b63c-56fea772b165

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph

set_option autoImplicit false
open GraphLQGame.Equilibrium
open Matrix

namespace GLEAux

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma lap_eq :
    lap G = Matrix.diagonal (fun i => ((G.degree i : ℝ))⁻¹) * G.adjMatrix ℝ - 1 := by
  ext i j
  simp only [lap, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.one_apply,
    SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

lemma lap_mulVec (v : Fin n → ℝ) (i : Fin n) :
    (lap G *ᵥ v) i = ((G.degree i : ℝ))⁻¹ * (G.adjMatrix ℝ *ᵥ v) i - v i := by
  rw [lap_eq, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    Matrix.mulVec_diagonal]

lemma Av_le (v : Fin n → ℝ) (m : ℝ) (h : ∀ j, v j ≤ m) (i : Fin n) :
    (G.adjMatrix ℝ *ᵥ v) i ≤ (G.degree i : ℝ) * m := by
  have h1 : (G.adjMatrix ℝ *ᵥ v) i ≤ (G.adjMatrix ℝ *ᵥ Function.const _ m) i := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_le_sum
    intro j _
    refine mul_le_mul_of_nonneg_left (h j) ?_
    rw [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  rwa [SimpleGraph.adjMatrix_mulVec_const_apply] at h1

lemma Av_ge (v : Fin n → ℝ) (m : ℝ) (h : ∀ j, m ≤ v j) (i : Fin n) :
    (G.degree i : ℝ) * m ≤ (G.adjMatrix ℝ *ᵥ v) i := by
  have h1 : (G.adjMatrix ℝ *ᵥ Function.const _ m) i ≤ (G.adjMatrix ℝ *ᵥ v) i := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_le_sum
    intro j _
    refine mul_le_mul_of_nonneg_left (h j) ?_
    rw [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  rwa [SimpleGraph.adjMatrix_mulVec_const_apply] at h1

lemma exists_eigvec (l : ℝ) (hl : l ∈ (lap G).charpoly.roots) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ lap G *ᵥ v = l • v := by
  have h0 : (lap G).charpoly.IsRoot l := (Polynomial.mem_roots'.mp hl).2
  rw [Polynomial.IsRoot.def, Matrix.eval_charpoly] at h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec] at hv0
  have : (Matrix.scalar (Fin n) l) *ᵥ v = l • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [this] at hv0
  exact (sub_eq_zero.mp hv0).symm

lemma upper_aux (hN : NoIsolated G) (l : ℝ) (w : Fin n → ℝ) (hw : lap G *ᵥ w = l • w) (k : Fin n)
    (hk : ∀ j, w j ≤ w k) (hpos : 0 < w k) : l ≤ 0 := by
  have hdk : 0 < (G.degree k : ℝ) := by exact_mod_cast hN k
  have hup := Av_le G w (w k) hk k
  have heq := congrFun hw k
  rw [lap_mulVec] at heq
  simp only [Pi.smul_apply, smul_eq_mul] at heq
  have h1 : ((G.degree k : ℝ))⁻¹ * (G.adjMatrix ℝ *ᵥ w) k ≤ w k := by
    rw [inv_mul_le_iff₀ hdk]; linarith
  by_contra hcon
  push_neg at hcon
  have := mul_pos hcon hpos
  linarith

lemma eig_bounds (hN : NoIsolated G) (l : ℝ) (v : Fin n → ℝ) (hv : v ≠ 0)
    (hlv : lap G *ᵥ v = l • v) : -2 ≤ l ∧ l ≤ 0 := by
  have hex : ∃ j, v j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨j0, hj0⟩ := hex
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|)
    ⟨j0, Finset.mem_univ _⟩
  have hm : 0 < |v k| := lt_of_lt_of_le (abs_pos.mpr hj0) (hk j0 (Finset.mem_univ _))
  have hb : ∀ j, -|v k| ≤ v j ∧ v j ≤ |v k| := fun j => abs_le.mp (hk j (Finset.mem_univ _))
  have hdk : 0 < (G.degree k : ℝ) := by exact_mod_cast hN k
  have hup := Av_le G v (|v k|) (fun j => (hb j).2) k
  have hlo := Av_ge G v (-|v k|) (fun j => (hb j).1) k
  have heq := congrFun hlv k
  rw [lap_mulVec] at heq
  simp only [Pi.smul_apply, smul_eq_mul] at heq
  have h1 : ((G.degree k : ℝ))⁻¹ * (G.adjMatrix ℝ *ᵥ v) k ≤ |v k| := by
    rw [inv_mul_le_iff₀ hdk]; linarith
  have h2 : -|v k| ≤ ((G.degree k : ℝ))⁻¹ * (G.adjMatrix ℝ *ᵥ v) k := by
    rw [le_inv_mul_iff₀ hdk]; linarith
  have h3 : |l * v k| ≤ 2 * |v k| := by
    rw [← heq, abs_le]
    constructor <;> linarith [(hb k).1, (hb k).2]
  rw [abs_mul] at h3
  have h5 : |l| ≤ 2 := le_of_mul_le_mul_right (by linarith) hm
  refine ⟨by linarith [(abs_le.mp h5).1], ?_⟩
  rcases lt_or_gt_of_ne hj0 with hneg | hpos
  · -- use -v
    have hw : lap G *ᵥ (-v) = l • (-v) := by
      rw [Matrix.mulVec_neg, hlv, smul_neg]
    obtain ⟨k', _, hk'⟩ := Finset.exists_max_image Finset.univ (fun j => (-v) j)
      ⟨j0, Finset.mem_univ _⟩
    refine upper_aux G hN l (-v) hw k' (fun j => hk' j (Finset.mem_univ _)) ?_
    have := hk' j0 (Finset.mem_univ _)
    simp only [Pi.neg_apply] at this ⊢
    linarith
  · obtain ⟨k', _, hk'⟩ := Finset.exists_max_image Finset.univ (fun j => v j)
      ⟨j0, Finset.mem_univ _⟩
    refine upper_aux G hN l v hlv k' (fun j => hk' j (Finset.mem_univ _)) ?_
    have := hk' j0 (Finset.mem_univ _)
    linarith

lemma lap_hermitian_charpoly (hN : NoIsolated G) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, S.IsHermitian ∧ (lap G).charpoly = S.charpoly := by
  have hsq : ∀ i, 0 < Real.sqrt (G.degree i : ℝ) := fun i =>
    Real.sqrt_pos.mpr (by exact_mod_cast hN i)
  set E : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => (Real.sqrt (G.degree i : ℝ))⁻¹)
    with hE
  set F : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => Real.sqrt (G.degree i : ℝ))
    with hF
  have hEF : E * F = 1 := by
    have : (fun i => (Real.sqrt (G.degree i : ℝ))⁻¹ * Real.sqrt (G.degree i : ℝ)) =
        fun _ => (1 : ℝ) := by
      funext i; exact inv_mul_cancel₀ (hsq i).ne'
    rw [hE, hF, Matrix.diagonal_mul_diagonal, this, Matrix.diagonal_one]
  have hFE : F * E = 1 := by
    have : (fun i => Real.sqrt (G.degree i : ℝ) * (Real.sqrt (G.degree i : ℝ))⁻¹) =
        fun _ => (1 : ℝ) := by
      funext i; exact mul_inv_cancel₀ (hsq i).ne'
    rw [hE, hF, Matrix.diagonal_mul_diagonal, this, Matrix.diagonal_one]
  have hEE : E * E = Matrix.diagonal (fun i => ((G.degree i : ℝ))⁻¹) := by
    have : (fun i => (Real.sqrt (G.degree i : ℝ))⁻¹ * (Real.sqrt (G.degree i : ℝ))⁻¹) =
        fun i => ((G.degree i : ℝ))⁻¹ := by
      funext i
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    rw [hE, Matrix.diagonal_mul_diagonal, this]
  refine ⟨E * G.adjMatrix ℝ * E - 1, ?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    have hA : (G.adjMatrix ℝ)ᵀ = G.adjMatrix ℝ := SimpleGraph.isSymm_adjMatrix (G := G) (α := ℝ)
    have hEt : Eᵀ = E := by rw [hE, Matrix.diagonal_transpose]
    unfold Matrix.IsSymm
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one,
      hA, hEt, Matrix.mul_assoc]
  · have hL : lap G = E * (E * G.adjMatrix ℝ * E - 1) * F := by
      rw [lap_eq]
      calc Matrix.diagonal (fun i => ((G.degree i : ℝ))⁻¹) * G.adjMatrix ℝ - 1
          = (E * E) * G.adjMatrix ℝ * (E * F) - E * F := by rw [hEE, hEF, Matrix.mul_one]
        _ = E * (E * G.adjMatrix ℝ * E) * F - E * 1 * F := by
          simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = E * (E * G.adjMatrix ℝ * E - 1) * F := by rw [Matrix.mul_sub, Matrix.sub_mul]
    have := Matrix.charpoly_units_conj
      (⟨E, F, hEF, hFE⟩ : (Matrix (Fin n) (Fin n) ℝ)ˣ) (E * G.adjMatrix ℝ * E - 1)
    rw [hL]
    have hu : E⁻¹ = F := Matrix.inv_eq_right_inv hEF
    have hv : ((⟨E, F, hEF, hFE⟩ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) = E :=
      rfl
    rw [hv, hu] at this
    exact this

end GLEAux

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hN : NoIsolated G) :
    (lap G).charpoly.roots.card = n ∧
      (∀ l ∈ (lap G).charpoly.roots, -2 ≤ l ∧ l ≤ 0) ∧
      (lap G).mulVec (fun _ => (1 : ℝ)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS, hchar⟩ := GLEAux.lap_hermitian_charpoly G hN
    rw [hchar, hS.roots_charpoly_eq_eigenvalues]
    simp
  · intro l hl
    obtain ⟨v, hv, hlv⟩ := GLEAux.exists_eigvec G l hl
    exact GLEAux.eig_bounds G hN l v hv hlv
  · ext i
    have hdk : (G.degree i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
    have h1 := GLEAux.lap_mulVec G (fun _ => (1 : ℝ)) i
    have h2 : (G.adjMatrix ℝ *ᵥ (fun _ => (1 : ℝ))) i = G.degree i * 1 :=
      SimpleGraph.adjMatrix_mulVec_const_apply (a := (1 : ℝ))
    rw [h1, h2]
    simp [hdk]
