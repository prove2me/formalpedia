-- Prove2me | solution 1 for NelderMeadLD.Dim2.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:40:36.139907+00:00
-- url     : https://prove2.me/submissions/4909ed99-7f86-4448-9eea-4809a940daa8

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology


namespace NelderMeadLD.Dim2

lemma g56_insertPos_le {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) :
    insertPos f x v ≤ n := by
  unfold insertPos
  calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

lemma g56_mem_prefix {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) (hs : Sorted f x)
    (i : Fin n) : f (x i.castSucc) ≤ f v ↔ i.val < insertPos f x v := by
  unfold insertPos
  set S := (Finset.univ : Finset (Fin n)).filter (fun i => f (x i.castSucc) ≤ f v) with hS
  constructor
  · intro hi
    have : Finset.Iic i ⊆ S := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans (hs _ _ (by simpa using hj)) hi
    have := Finset.card_le_card this
    rw [Fin.card_Iic] at this
    omega
  · intro hi
    by_contra hne
    have : S ⊆ Finset.Iio i := by
      intro j hj
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hji
      push Not at hji
      exact hne (le_trans (hs _ _ (by simpa using hji)) hj)
    have := Finset.card_le_card this
    rw [Fin.card_Iio] at this
    omega

lemma g56_key {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) (hs : Sorted f x)
    (k : ℕ) (hk : k < n) : f (x ⟨k, by omega⟩) ≤ f v ↔ k < insertPos f x v :=
  g56_mem_prefix f x v hs ⟨k, hk⟩

lemma g56_iv_lt {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) (i : Fin (n + 1))
    (h : i.val < insertPos f x v) : insertVertex f x v i = x i := by
  simp [insertVertex, h]

lemma g56_iv_eq {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) (i : Fin (n + 1))
    (h : i.val = insertPos f x v) : insertVertex f x v i = v := by
  simp [insertVertex, h]

lemma g56_iv_gt {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) (i : Fin (n + 1))
    (h : insertPos f x v < i.val) : insertVertex f x v i = x ⟨i.val - 1, by omega⟩ := by
  have h1 : ¬ i.val < insertPos f x v := by omega
  have h2 : ¬ i.val = insertPos f x v := by omega
  simp [insertVertex, h1, h2]

lemma g56_sorted_iv {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) (hs : Sorted f x) :
    Sorted f (insertVertex f x v) := by
  have hp := g56_insertPos_le f x v
  have key := g56_key f x v hs
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_trichotomy i.val (insertPos f x v) with h1 | h1 | h1 <;>
    rcases lt_trichotomy j.val (insertPos f x v) with h2 | h2 | h2
  · rw [g56_iv_lt _ _ _ _ h1, g56_iv_lt _ _ _ _ h2]; exact hs _ _ hij
  · rw [g56_iv_lt _ _ _ _ h1, g56_iv_eq _ _ _ _ h2]
    have := (key i.val (by omega)).2 h1; simpa using this
  · rw [g56_iv_lt _ _ _ _ h1, g56_iv_gt _ _ _ _ h2]
    have h3 := (key i.val (by omega)).2 h1
    have h4 : ¬ f (x ⟨j.val - 1, by omega⟩) ≤ f v := fun h => by
      have := (key (j.val - 1) (by omega)).1 h; omega
    simp only [Fin.eta] at h3
    push Not at h4; linarith
  · omega
  · rw [g56_iv_eq _ _ _ _ h1, g56_iv_eq _ _ _ _ h2]
  · rw [g56_iv_eq _ _ _ _ h1, g56_iv_gt _ _ _ _ h2]
    have h4 : ¬ f (x ⟨j.val - 1, by omega⟩) ≤ f v := fun h => by
      have := (key (j.val - 1) (by omega)).1 h; omega
    push Not at h4; linarith
  · omega
  · omega
  · rw [g56_iv_gt _ _ _ _ h1, g56_iv_gt _ _ _ _ h2]
    exact hs _ _ (by rw [Fin.mk_le_mk]; omega)

lemma g56_run_sorted {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ) (Δ : ℕ → Fin (n + 1) → E n)
    (hrun : IsNMRun f ρ χ γ σ Δ) : ∀ k, Sorted f (Δ k)
  | 0 => hrun.1
  | k + 1 => by
    by_cases h : move f ρ χ γ (Δ k) = NelderMeadLD.Conv1D.Move.shrink
    · exact ((hrun.2 k).1 h).2.1
    · rw [(hrun.2 k).2 h]; exact g56_sorted_iv _ _ _ (g56_run_sorted f ρ χ γ σ Δ hrun k)

lemma g56_accepted_lt {n : ℕ} (f : E n → ℝ) (ρ χ γ : ℝ) (x : Fin (n + 1) → E n) (hs : Sorted f x)
    (h : move f ρ χ γ x ≠ NelderMeadLD.Conv1D.Move.shrink) :
    f (trial x (tau ρ χ γ (move f ρ χ γ x))) < f (x (Fin.last n)) := by
  have h1n : f (x 0) ≤ f (x (nextWorst n)) := hs _ _ (Fin.zero_le _)
  have hnw : f (x (nextWorst n)) ≤ f (x (Fin.last n)) := hs _ _ (Fin.le_last _)
  simp only [move] at h ⊢
  split_ifs at h ⊢ <;> first | exact absurd rfl h | (simp only [tau]; linarith)

lemma g56_nonshrink_values {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) (hs : Sorted f x)
    (hv : f v < f (x (Fin.last n))) :
    (∀ i, f (insertVertex f x v i) ≤ f (x i)) ∧ ∃ i, f (insertVertex f x v i) < f (x i) := by
  have hp := g56_insertPos_le f x v
  have key := g56_key f x v hs
  have hlt : f v < f (x ⟨insertPos f x v, by omega⟩) := by
    rcases lt_or_eq_of_le hp with h | h
    · by_contra hc; push Not at hc; have := (key _ h).1 hc; omega
    · have : (⟨insertPos f x v, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [h])
      rw [this]; exact hv
  constructor
  · intro i
    rcases lt_trichotomy i.val (insertPos f x v) with h1 | h1 | h1
    · rw [g56_iv_lt _ _ _ _ h1]
    · rw [g56_iv_eq _ _ _ _ h1]
      have : i = ⟨insertPos f x v, by omega⟩ := Fin.ext h1
      rw [this]; exact hlt.le
    · rw [g56_iv_gt _ _ _ _ h1]; exact hs _ _ (by rw [Fin.le_def]; simp)
  · exact ⟨⟨insertPos f x v, by omega⟩, by rw [g56_iv_eq _ _ _ _ rfl]; exact hlt⟩

noncomputable def g56_augM {n : ℕ} (x : Fin (n + 1) → E n) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun i j => if h : (j : ℕ) < n then x i ⟨j, h⟩ else 1

lemma g56_det_edge {n : ℕ} (x : Fin (n + 1) → E n) : (edgeMatrix x).det = (g56_augM x).det := by
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of fun i j =>
    g56_augM x i j + (if i = Fin.last n then 0 else -1) * g56_augM x (Fin.last n) j
  have h1 : B.det = (g56_augM x).det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i = Fin.last n then 0 else -1)
      (Fin.last n) (by simp) (fun i j => rfl)
  rw [← h1, Matrix.det_succ_column B (Fin.last n)]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have hB : B (Fin.last n) (Fin.last n) = 1 := by simp [B, g56_augM]
    rw [hB, Fin.succAbove_last]
    have : (-1 : ℝ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
      rw [← two_mul, pow_mul]; simp
    rw [this, one_mul, one_mul, ← Matrix.det_transpose]
    congr 1
    ext r c
    simp [B, g56_augM, edgeMatrix]; ring
  · intro i _ hi
    have : B i (Fin.last n) = 0 := by simp [B, g56_augM, hi]
    rw [this]; simp
  · simp

lemma g56_abs_det_perm {n : ℕ} (x : Fin (n + 1) → E n) (π : Equiv.Perm (Fin (n + 1))) :
    |(edgeMatrix (x ∘ π)).det| = |(edgeMatrix x).det| := by
  rw [g56_det_edge, g56_det_edge]
  have : g56_augM (x ∘ π) = (g56_augM x).submatrix π id := by
    ext i j; simp [g56_augM]
  rw [this, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

lemma g56_edge_shrink {n : ℕ} (σ : ℝ) (x : Fin (n + 1) → E n) :
    edgeMatrix (shrinkPoints σ x) = σ • edgeMatrix x := by
  ext r c; simp [edgeMatrix, shrinkPoints]; ring

lemma g56_det_update {n : ℕ} [NeZero n] (x : Fin (n + 1) → E n) (τ : ℝ) :
    (edgeMatrix (Function.update x (Fin.last n) (trial x τ))).det = -τ * (edgeMatrix x).det := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let u : Fin n → ℝ := fun _ => -(1 + τ) / n
  let w : Fin n → ℝ := fun _ => 1
  have hM : edgeMatrix (Function.update x (Fin.last n) (trial x τ)) =
      edgeMatrix x * (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit w) := by
    rw [Matrix.mul_add, Matrix.mul_one]
    ext r c
    simp only [edgeMatrix, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      Function.update_of_ne (Fin.castSucc_ne_last _), Function.update_self, Matrix.replicateCol,
      Matrix.replicateRow, u, w, mul_one]
    simp only [trial, centroid, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
      Finset.sum_apply]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fintype.card_unit, Nat.cast_one, mul_one]
    field_simp
    ring
  rw [hM, Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, u, w, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

lemma g56_iv_comp {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) :
    ∃ π : Equiv.Perm (Fin (n + 1)), insertVertex f x v = Function.update x (Fin.last n) v ∘ π := by
  have hp := g56_insertPos_le f x v
  let g : Fin (n+1) → Fin (n+1) := fun i =>
    if i.val < insertPos f x v then i else if i.val = insertPos f x v then Fin.last n
    else ⟨i.val - 1, by omega⟩
  have hg : Function.Injective g := by
    intro a b hab
    simp only [g] at hab
    apply Fin.ext
    have := a.isLt; have := b.isLt
    split_ifs at hab <;> simp [Fin.ext_iff] at hab <;> omega
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), ?_⟩
  funext i
  show insertVertex f x v i = Function.update x (Fin.last n) v (g i)
  rcases lt_trichotomy i.val (insertPos f x v) with h | h | h
  · have : g i = i := by simp [g, h]
    rw [this, g56_iv_lt _ _ _ _ h, Function.update_of_ne]
    intro e; rw [e] at h; simp at h; omega
  · have : g i = Fin.last n := by simp [g, h]
    rw [this, g56_iv_eq _ _ _ _ h, Function.update_self]
  · have h1 : ¬ i.val < insertPos f x v := by omega
    have h2 : ¬ i.val = insertPos f x v := by omega
    have : g i = ⟨i.val - 1, by omega⟩ := by simp [g, h1, h2]
    rw [this, g56_iv_gt _ _ _ _ h, Function.update_of_ne]
    intro e; rw [Fin.ext_iff] at e; simp at e; have := i.isLt; omega

lemma g56_absdet_nonshrink {n : ℕ} [NeZero n] (f : E n → ℝ) (x : Fin (n + 1) → E n) (τ : ℝ) :
    |(edgeMatrix (insertVertex f x (trial x τ))).det| = |τ| * |(edgeMatrix x).det| := by
  obtain ⟨π, hπ⟩ := g56_iv_comp f x (trial x τ)
  rw [hπ, g56_abs_det_perm, g56_det_update, abs_mul, abs_neg]

lemma g56_absdet_shrink {n : ℕ} (f : E n → ℝ) (σ : ℝ) (hσ : 0 < σ) (x y : Fin (n + 1) → E n)
    (h : IsShrinkSuccessor f σ x y) :
    |(edgeMatrix y).det| = σ ^ n * |(edgeMatrix x).det| := by
  obtain ⟨⟨π, hπ⟩, _, _⟩ := h
  rw [hπ, g56_abs_det_perm, g56_edge_shrink, Matrix.det_smul, abs_mul, abs_pow, abs_of_pos hσ]
  simp

lemma g56_tau_ne {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (x : Fin (n + 1) → E n) (h : move f ρ χ γ x ≠ NelderMeadLD.Conv1D.Move.shrink) :
    tau ρ χ γ (move f ρ χ γ x) ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpar
  revert h
  cases move f ρ χ γ x <;> intro h <;> simp only [tau] <;> first | exact absurd rfl h | positivity | nlinarith

lemma g56_step_absdet {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ)
    (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ) (x y : Fin (n + 1) → E n)
    (hstep : IsNMStep f ρ χ γ σ x y) :
    (move f ρ χ γ x ≠ NelderMeadLD.Conv1D.Move.shrink →
      |(edgeMatrix y).det| = |tau ρ χ γ (move f ρ χ γ x)| * |(edgeMatrix x).det|) ∧
    (move f ρ χ γ x = NelderMeadLD.Conv1D.Move.shrink →
      |(edgeMatrix y).det| = σ ^ n * |(edgeMatrix x).det|) := by
  constructor
  · intro h; rw [hstep.2 h]; exact g56_absdet_nonshrink f x _
  · intro h; exact g56_absdet_shrink f σ hpar.2.2.2.2.2.1 x y (hstep.1 h)

lemma g56_run_nd {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ)
    (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ) (Δ : ℕ → Fin (n + 1) → E n)
    (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0)) : ∀ k, Nondegenerate (Δ k)
  | 0 => hnd
  | k + 1 => by
    have ih := g56_run_nd f ρ χ γ σ hpar Δ hrun hnd k
    unfold Nondegenerate at ih ⊢
    rw [← abs_ne_zero] at ih ⊢
    have hs := g56_step_absdet f ρ χ γ σ hpar _ _ (hrun.2 k)
    by_cases h : move f ρ χ γ (Δ k) = NelderMeadLD.Conv1D.Move.shrink
    · rw [hs.2 h]; exact mul_ne_zero (pow_ne_zero _ hpar.2.2.2.2.2.1.ne') ih
    · rw [hs.1 h]; exact mul_ne_zero (abs_ne_zero.mpr (g56_tau_ne f ρ χ γ σ hpar _ h)) ih

theorem lemma_3_1_core {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0)) :
    (∀ k, Nondegenerate (Δ k)) ∧
    (∀ k, ¬ IsShrinkAt f ρ χ γ Δ k →
      vol (Δ (k + 1)) = |tau ρ χ γ (move f ρ χ γ (Δ k))| * vol (Δ k)) ∧
    (∀ k, IsShrinkAt f ρ χ γ Δ k → vol (Δ (k + 1)) = σ ^ n * vol (Δ k)) := by
  refine ⟨g56_run_nd f ρ χ γ σ hpar Δ hrun hnd, ?_, ?_⟩
  · intro k h
    unfold vol; rw [(g56_step_absdet f ρ χ γ σ hpar _ _ (hrun.2 k)).1 h]; ring
  · intro k h
    unfold vol; rw [(g56_step_absdet f ρ χ γ σ hpar _ _ (hrun.2 k)).2 h]; ring

end NelderMeadLD.Dim2

open NelderMeadLD.Dim2


theorem solution {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0)) :
    (∀ k, Nondegenerate (Δ k)) ∧
    (∀ k, ¬ IsShrinkAt f ρ χ γ Δ k →
      vol (Δ (k + 1)) = |tau ρ χ γ (move f ρ χ γ (Δ k))| * vol (Δ k)) ∧
    (∀ k, IsShrinkAt f ρ χ γ Δ k → vol (Δ (k + 1)) = σ ^ n * vol (Δ k)) := by
  exact lemma_3_1_core f ρ χ γ σ hpar Δ hrun hnd
