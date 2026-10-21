-- Prove2me | solution 1 for GraphLQGame.Equilibrium.QG_eq_Qmu
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:45:03.422364+00:00
-- url     : https://prove2.me/submissions/685fed07-a279-4a12-8a47-df54fb0972e4

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
import Definitions.Def_GraphLQGame_Equilibrium_Spectral

set_option autoImplicit false
open GraphLQGame.Equilibrium
open Matrix MeasureTheory
open scoped ENNReal

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

namespace GLEAux

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma roots_card (hN : NoIsolated G) : (lap G).charpoly.roots.card = n := by
  obtain ⟨S, hS, hchar⟩ := lap_hermitian_charpoly G hN
  rw [hchar, hS.roots_charpoly_eq_eigenvalues]
  simp

lemma roots_bounds (hN : NoIsolated G) : ∀ l ∈ (lap G).charpoly.roots, -2 ≤ l ∧ l ≤ 0 := by
  intro l hl
  obtain ⟨v, hv, hlv⟩ := exists_eigvec G l hl
  exact eig_bounds G hN l v hv hlv

lemma det_eq_prod (hN : NoIsolated G) (x : ℝ) :
    (1 - x • lap G).det = ((lap G).charpoly.roots.map (fun l => 1 - x * l)).prod := by
  have hcard := roots_card G hN
  have hP : ((lap G).charpoly.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod =
      (lap G).charpoly :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic _)
      (by rw [hcard, Matrix.charpoly_natDegree_eq_dim]; simp)
  by_cases hx : x = 0
  · subst hx
    simp
  · have h1 : (lap G).charpoly.eval x⁻¹ =
        ((lap G).charpoly.roots.map (fun a => x⁻¹ - a)).prod := by
      conv_lhs => rw [← hP]
      rw [Polynomial.eval_multiset_prod, Multiset.map_map]
      simp [Function.comp]
    have h2 : (lap G).charpoly.eval x⁻¹ = (Matrix.scalar (Fin n) x⁻¹ - lap G).det :=
      Matrix.eval_charpoly _ _
    have h3 : (1 : Matrix (Fin n) (Fin n) ℝ) - x • lap G =
        x • (Matrix.scalar (Fin n) x⁻¹ - lap G) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply]
        rw [mul_sub, mul_inv_cancel₀ hx]
      · simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply, hij]
    rw [h3, Matrix.det_smul, Fintype.card_fin, ← h2, h1]
    have h4 : ((lap G).charpoly.roots.map (fun l => 1 - x * l)) =
        (lap G).charpoly.roots.map (fun l => x * (x⁻¹ - l)) :=
      Multiset.map_congr rfl (fun l _ => by field_simp)
    rw [h4, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]

lemma int_sum_dirac (s : Multiset ℝ) (f : ℝ → ℝ) (A : Set ℝ) [DecidablePred (· ∈ A)] :
    Integrable f ((s.map (fun l => Measure.dirac l)).sum.restrict A) ∧
      ∫ l in A, f l ∂(s.map (fun l => Measure.dirac l)).sum =
        (s.map (fun a => if a ∈ A then f a else 0)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hs : ((a ::ₘ s).map (fun l => Measure.dirac l)).sum =
        Measure.dirac a + (s.map (fun l => Measure.dirac l)).sum := by
      simp [Multiset.map_cons, Multiset.sum_cons]
    have hd : Integrable f ((Measure.dirac a).restrict A) ∧
        ∫ l in A, f l ∂(Measure.dirac a) = if a ∈ A then f a else 0 := by
      refine ⟨?_, setIntegral_dirac f a A⟩
      rw [restrict_dirac]
      split_ifs
      · exact integrable_dirac (by simp)
      · exact integrable_zero_measure
    rw [hs, Measure.restrict_add]
    refine ⟨hd.1.add_measure ih1, ?_⟩
    rw [integral_add_measure hd.1 ih1, ih2, hd.2, Multiset.map_cons, Multiset.sum_cons]

end GLEAux

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 0 < n)
    (hN : NoIsolated G) (x : ℝ) (hx : 0 ≤ x) :
    QG G x = (((lap G).charpoly.roots.map (fun l => 1 - x * l)).prod) ^ ((n : ℝ)⁻¹) ∧
      QG G x = Qmu (specMeasure G) x := by
  have hdet := GLEAux.det_eq_prod G hN x
  have hbd := GLEAux.roots_bounds G hN
  have hcard := GLEAux.roots_card G hN
  have h1 : QG G x = (((lap G).charpoly.roots.map (fun l => 1 - x * l)).prod) ^ ((n : ℝ)⁻¹) := by
    unfold QG
    rw [hdet]
  refine ⟨h1, ?_⟩
  rw [h1]
  set R := (lap G).charpoly.roots with hR
  have hpos : ∀ l ∈ R, 0 < 1 - x * l := by
    intro l hl
    have := hbd l hl
    nlinarith [this.1, this.2]
  have hprodpos : 0 < (R.map (fun l => 1 - x * l)).prod := by
    apply Multiset.prod_pos
    intro a ha
    obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.mp ha
    exact hpos l hl
  unfold Qmu specMeasure
  have hint := (GLEAux.int_sum_dirac R (fun l => Real.log (1 - x * l)) (Set.Icc (-2 : ℝ) 0)).2
  rw [Measure.restrict_smul, integral_smul_measure, hint]
  have hmap : R.map (fun a => if a ∈ Set.Icc (-2 : ℝ) 0 then Real.log (1 - x * a) else 0) =
      R.map (fun a => Real.log (1 - x * a)) := by
    apply Multiset.map_congr rfl
    intro a ha
    have := hbd a ha
    rw [if_pos ⟨this.1, this.2⟩]
  rw [hmap]
  have hlog : Real.log ((R.map (fun l => 1 - x * l)).prod) =
      (R.map (fun a => Real.log (1 - x * a))).sum := by
    rw [Real.log_multiset_prod, Multiset.map_map]
    · rfl
    · intro a ha
      obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.mp ha
      exact (hpos l hl).ne'
  rw [Real.rpow_def_of_pos hprodpos, hlog]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, mul_comm]
