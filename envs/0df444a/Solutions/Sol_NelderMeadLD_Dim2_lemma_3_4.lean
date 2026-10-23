-- Prove2me | solution 1 for NelderMeadLD.Dim2.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:46:20.936988+00:00
-- url     : https://prove2.me/submissions/5263ff9b-e8b8-4ee9-ba78-829d7e51eb9b

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

lemma g56_centroid_ne {n : ℕ} [NeZero n] (x : Fin (n + 1) → E n) (hnd : Nondegenerate x) :
    centroid x ≠ x (Fin.last n) := by
  intro h
  apply hnd
  have h1 := g56_det_update x 0
  have h2 : Function.update x (Fin.last n) (trial x 0) = x := by
    have : trial x 0 = x (Fin.last n) := by simp [trial, h]
    rw [this, Function.update_eq_self]
  rw [h2] at h1
  linarith

lemma g56_centroid_eq {n : ℕ} (x : Fin (n + 1) → E n) :
    centroid x = ∑ i : Fin n, (1 / (n : ℝ)) • x i.castSucc := by
  simp [centroid, Finset.smul_sum]

lemma g56_weights {n : ℕ} [NeZero n] : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp [Finset.sum_const, hn]

lemma g56_jensen {n : ℕ} [NeZero n] (f : E n → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (x : Fin (n + 1) → E n) :
    f (centroid x) ≤ ∑ i : Fin n, (1 / (n : ℝ)) * f (x i.castSucc) := by
  rw [g56_centroid_eq]
  have := hf.map_sum_le (t := Finset.univ) (w := fun _ => 1 / (n : ℝ)) (p := fun i => x i.castSucc)
    (fun i _ => by positivity) g56_weights (fun i _ => Set.mem_univ _)
  simpa using this

lemma g56_jensen_strict {n : ℕ} [NeZero n] (f : E n → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (x : Fin (n + 1) → E n) (h : ∃ i j : Fin n, x i.castSucc ≠ x j.castSucc) :
    f (centroid x) < ∑ i : Fin n, (1 / (n : ℝ)) * f (x i.castSucc) := by
  rw [g56_centroid_eq]
  obtain ⟨i, j, hij⟩ := h
  have := hf.map_sum_lt (t := Finset.univ) (w := fun _ => 1 / (n : ℝ)) (p := fun i => x i.castSucc)
    (fun i _ => by have : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
                   positivity) g56_weights (fun i _ => Set.mem_univ _)
    ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, hij⟩
  simpa using this

lemma g56_avg_le {n : ℕ} [NeZero n] (f : E n → ℝ) (x : Fin (n + 1) → E n) (hs : Sorted f x) :
    ∑ i : Fin n, (1 / (n : ℝ)) * f (x i.castSucc) ≤ f (x (nextWorst n)) := by
  calc ∑ i : Fin n, (1 / (n : ℝ)) * f (x i.castSucc)
      ≤ ∑ _i : Fin n, (1 / (n : ℝ)) * f (x (nextWorst n)) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply hs
        rw [Fin.le_def]; simp [nextWorst]; omega
    _ = f (x (nextWorst n)) := by rw [← Finset.sum_mul, g56_weights, one_mul]

lemma g56_noshrink_strict {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ)
    (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ) (hf : StrictConvexOn ℝ Set.univ f)
    (x : Fin (n + 1) → E n) (hs : Sorted f x) (hnd : Nondegenerate x) :
    move f ρ χ γ x ≠ NelderMeadLD.Conv1D.Move.shrink := by
  obtain ⟨hρ, hχ, hρχ, hγ0, hγ1, -, -⟩ := hpar
  have hc : f (centroid x) ≤ f (x (nextWorst n)) :=
    (g56_jensen f hf.convexOn x).trans (g56_avg_le f x hs)
  have hcL := g56_centroid_ne x hnd
  have h1n : f (x 0) ≤ f (x (nextWorst n)) := hs _ _ (Fin.zero_le _)
  have hnw : f (x (nextWorst n)) ≤ f (x (Fin.last n)) := hs _ _ (Fin.le_last _)
  have hout : f (trial x (ρ * γ)) ≤ (1 - γ) * f (centroid x) + γ * f (trial x ρ) := by
    have := hf.convexOn.2 (Set.mem_univ (centroid x)) (Set.mem_univ (trial x ρ))
      (by linarith : (0:ℝ) ≤ 1 - γ) hγ0.le (by ring)
    rw [show trial x (ρ * γ) = (1 - γ) • centroid x + γ • trial x ρ by simp only [trial]; module]
    simpa using this
  have hin : f (trial x (-γ)) < (1 - γ) * f (centroid x) + γ * f (x (Fin.last n)) := by
    have := hf.2 (Set.mem_univ (centroid x)) (Set.mem_univ (x (Fin.last n))) hcL
      (by linarith : (0:ℝ) < 1 - γ) hγ0 (by ring)
    rw [show trial x (-γ) = (1 - γ) • centroid x + γ • x (Fin.last n) by simp only [trial]; module]
    simpa using this
  intro hsh
  simp only [move] at hsh
  by_cases A : f (x 0) ≤ f (trial x ρ) ∧ f (trial x ρ) < f (x (nextWorst n))
  · rw [if_pos A] at hsh; exact absurd hsh (by decide)
  rw [if_neg A] at hsh
  by_cases B : f (trial x ρ) < f (x 0)
  · rw [if_pos B] at hsh; revert hsh; split_ifs <;> decide
  rw [if_neg B] at hsh
  have hfr : f (x (nextWorst n)) ≤ f (trial x ρ) := by
    by_contra h; push Not at B h; exact A ⟨B, h⟩
  by_cases C : f (trial x ρ) < f (x (Fin.last n))
  · rw [if_pos C] at hsh
    by_cases D : f (trial x (ρ * γ)) ≤ f (trial x ρ)
    · rw [if_pos D] at hsh; exact absurd hsh (by decide)
    · exact D (by nlinarith)
  · rw [if_neg C] at hsh
    by_cases D : f (trial x (-γ)) < f (x (Fin.last n))
    · rw [if_pos D] at hsh; exact absurd hsh (by decide)
    · exact D (by nlinarith)

theorem lemma_3_5_core {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hf : StrictConvexOn ℝ Set.univ f) :
    ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k := fun k =>
  g56_noshrink_strict f ρ χ γ σ hpar hf (Δ k) (g56_run_sorted f ρ χ γ σ Δ hrun k)
    (g56_run_nd f ρ χ γ σ hpar Δ hrun hnd k)

lemma g56_ns_step {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ) (Δ : ℕ → Fin (n + 1) → E n)
    (hrun : IsNMRun f ρ χ γ σ Δ) (k : ℕ) (h : ¬ IsShrinkAt f ρ χ γ Δ k) :
    (∀ i, f (Δ (k + 1) i) ≤ f (Δ k i)) ∧ ∃ i, f (Δ (k + 1) i) < f (Δ k i) := by
  have hs := g56_run_sorted f ρ χ γ σ Δ hrun k
  rw [(hrun.2 k).2 h]
  exact g56_nonshrink_values f _ _ hs (g56_accepted_lt f ρ χ γ _ hs h)

lemma g56_best_step {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ) (Δ : ℕ → Fin (n + 1) → E n)
    (hrun : IsNMRun f ρ χ γ σ Δ) (k : ℕ) : f (Δ (k + 1) 0) ≤ f (Δ k 0) := by
  by_cases h : IsShrinkAt f ρ χ γ Δ k
  · obtain ⟨⟨π, hπ⟩, hsort, _⟩ := (hrun.2 k).1 h
    have := hsort 0 (π.symm 0) (Fin.zero_le _)
    rw [hπ] at this ⊢
    simpa [shrinkPoints] using this
  · exact (g56_ns_step f ρ χ γ σ Δ hrun k h).1 0

lemma g56_bdd {n : ℕ} (f : E n → ℝ) (hbdd : BddBelow (Set.range f)) (g : ℕ → E n) :
    BddBelow (Set.range fun k => f (g k)) := by
  obtain ⟨m, hm⟩ := hbdd
  exact ⟨m, by rintro _ ⟨k, rfl⟩; exact hm ⟨_, rfl⟩⟩

lemma g56_fstar {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ) (Δ : ℕ → Fin (n + 1) → E n)
    (hrun : IsNMRun f ρ χ γ σ Δ) (hbdd : BddBelow (Set.range f)) (K₀ : ℕ)
    (hns : ∀ k ≥ K₀, ¬ IsShrinkAt f ρ χ γ Δ k) :
    ∃ fstar : Fin (n + 1) → ℝ,
        (∀ i, Tendsto (fun k => f (Δ k i)) atTop (𝓝 (fstar i))) ∧
        (∀ i, ∀ k ≥ K₀, fstar i ≤ f (Δ k i)) ∧
        Monotone fstar := by
  have hanti : ∀ i, Antitone (fun m => f (Δ (m + K₀) i)) := by
    intro i
    apply antitone_nat_of_succ_le
    intro m
    have := (g56_ns_step f ρ χ γ σ Δ hrun (m + K₀) (hns _ (by omega))).1 i
    rw [show m + 1 + K₀ = m + K₀ + 1 by ring]; exact this
  refine ⟨fun i => ⨅ m, f (Δ (m + K₀) i), ?_, ?_, ?_⟩
  · intro i
    have := tendsto_atTop_ciInf (hanti i) (g56_bdd f hbdd _)
    exact (Filter.tendsto_add_atTop_iff_nat K₀).mp this
  · intro i k hk
    have := ciInf_le (g56_bdd f hbdd (fun m => Δ (m + K₀) i)) (k - K₀)
    rwa [show k - K₀ + K₀ = k by omega] at this
  · intro i j hij
    exact ciInf_mono (g56_bdd f hbdd _) (fun m => g56_run_sorted f ρ χ γ σ Δ hrun _ i j hij)

lemma g56_diam_nonneg {n : ℕ} (x : Fin (n + 1) → E n) : 0 ≤ diam x := by
  unfold diam
  exact le_trans (by simp) (Finset.le_sup' (fun ij : Fin (n + 1) × Fin (n + 1) => ‖x ij.1 - x ij.2‖)
    (Finset.mem_univ ((0 : Fin (n+1)), (0 : Fin (n+1)))))

lemma g56_le_diam {n : ℕ} (x : Fin (n + 1) → E n) (a b : Fin (n + 1)) : ‖x a - x b‖ ≤ diam x := by
  unfold diam
  exact Finset.le_sup' (fun ij : Fin (n + 1) × Fin (n + 1) => ‖x ij.1 - x ij.2‖)
    (Finset.mem_univ (a, b))

lemma g56_shrink_diam {n : ℕ} (f : E n → ℝ) (σ : ℝ) (hσ : 0 < σ) (x y : Fin (n + 1) → E n)
    (h : IsShrinkSuccessor f σ x y) :
    diam y ≤ σ * diam x ∧ ‖y 0 - x 0‖ ≤ σ * diam x := by
  obtain ⟨⟨π, hπ⟩, _, _⟩ := h
  subst hπ
  constructor
  · unfold diam
    apply Finset.sup'_le
    intro ij _
    simp only [Function.comp, shrinkPoints]
    rw [show x 0 + σ • (x (π ij.1) - x 0) - (x 0 + σ • (x (π ij.2) - x 0)) =
      σ • (x (π ij.1) - x (π ij.2)) by module, norm_smul, Real.norm_of_nonneg hσ.le]
    exact mul_le_mul_of_nonneg_left (g56_le_diam x _ _) hσ.le
  · simp only [Function.comp, shrinkPoints]
    rw [show x 0 + σ • (x (π 0) - x 0) - x 0 = σ • (x (π 0) - x 0) by module, norm_smul,
      Real.norm_of_nonneg hσ.le]
    exact mul_le_mul_of_nonneg_left (g56_le_diam x _ _) hσ.le

theorem lemma_3_3_core {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ)
    (hbdd : BddBelow (Set.range f)) :
    (∃ L : ℝ, Tendsto (fun k => f (Δ k 0)) atTop (𝓝 L)) ∧
    (∀ k, ¬ IsShrinkAt f ρ χ γ Δ k →
      (∀ i, f (Δ (k + 1) i) ≤ f (Δ k i)) ∧ ∃ i, f (Δ (k + 1) i) < f (Δ k i)) ∧
    (∀ K₀ : ℕ, (∀ k ≥ K₀, ¬ IsShrinkAt f ρ χ γ Δ k) →
      ∃ fstar : Fin (n + 1) → ℝ,
        (∀ i, Tendsto (fun k => f (Δ k i)) atTop (𝓝 (fstar i))) ∧
        (∀ i, ∀ k ≥ K₀, fstar i ≤ f (Δ k i)) ∧
        Monotone fstar) ∧
    (∀ K₀ : ℕ, (∀ k ≥ K₀, IsShrinkAt f ρ χ γ Δ k) →
      ∃ p : E n, ∀ i, Tendsto (fun k => Δ k i) atTop (𝓝 p)) := by
  have hσ0 : 0 < σ := hpar.2.2.2.2.2.1
  have hσ1 : σ < 1 := hpar.2.2.2.2.2.2
  refine ⟨?_, g56_ns_step f ρ χ γ σ Δ hrun, g56_fstar f ρ χ γ σ Δ hrun hbdd, ?_⟩
  · exact ⟨_, tendsto_atTop_ciInf (antitone_nat_of_succ_le (g56_best_step f ρ χ γ σ Δ hrun))
      (g56_bdd f hbdd _)⟩
  · intro K₀ hsh
    set D := diam (Δ K₀)
    have hD : 0 ≤ D := g56_diam_nonneg _
    have hdiam : ∀ m, diam (Δ (m + K₀)) ≤ σ ^ m * D := by
      intro m
      induction m with
      | zero => simp [D]
      | succ m ih =>
        have := (g56_shrink_diam f σ hσ0 _ _ ((hrun.2 (m + K₀)).1 (hsh _ (by omega)))).1
        rw [show m + 1 + K₀ = m + K₀ + 1 by ring]
        calc _ ≤ σ * diam (Δ (m + K₀)) := this
          _ ≤ σ * (σ ^ m * D) := mul_le_mul_of_nonneg_left ih hσ0.le
          _ = σ ^ (m + 1) * D := by ring
    have hstep : ∀ m, dist (Δ (m + K₀) 0) (Δ (m + 1 + K₀) 0) ≤ D * σ ^ m := by
      intro m
      have := (g56_shrink_diam f σ hσ0 _ _ ((hrun.2 (m + K₀)).1 (hsh _ (by omega)))).2
      rw [dist_comm, dist_eq_norm, show m + 1 + K₀ = m + K₀ + 1 by ring]
      calc _ ≤ σ * diam (Δ (m + K₀)) := this
        _ ≤ 1 * (σ ^ m * D) := mul_le_mul hσ1.le (hdiam m) (g56_diam_nonneg _) zero_le_one
        _ = D * σ ^ m := by ring
    have hc := cauchySeq_of_le_geometric σ D hσ1 hstep
    obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨p, fun i => ?_⟩
    rw [← Filter.tendsto_add_atTop_iff_nat K₀]
    have h0 : Tendsto (fun m => Δ (m + K₀) i - Δ (m + K₀) 0) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun m => (g56_le_diam _ i 0).trans (hdiam m))
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hσ0.le hσ1).mul_const D
      simpa using this
    have := hp.add h0
    simp only [add_zero, add_sub_cancel] at this
    exact this

lemma g56_l34_pos {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ)
    (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k)
    (j : Fin n) (a b : ℝ)
    (ha : Tendsto (fun k => f (Δ k j.castSucc)) atTop (𝓝 a))
    (hb : Tendsto (fun k => f (Δ k j.succ)) atTop (𝓝 b)) (hab : a < b) :
    ∃ K : ℕ, ∀ k ≥ K, j.val < insertPos f (Δ k) (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k)))) := by
  have hanti : Antitone (fun k => f (Δ k j.succ)) :=
    antitone_nat_of_succ_le (fun k => (g56_ns_step f ρ χ γ σ Δ hrun k (hnoshrink k)).1 _)
  have hlow : ∀ k, b ≤ f (Δ k j.succ) := hanti.le_of_tendsto hb
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ha.eventually (Iio_mem_nhds hab))
  refine ⟨K, fun k hk => ?_⟩
  by_contra hp
  push Not at hp
  have hΔ := (hrun.2 k).2 (hnoshrink k)
  have h1 := hlow (k + 1)
  rw [hΔ, g56_iv_gt _ _ _ _ (by simp; omega)] at h1
  have h2 := hK k hk
  have : (⟨(j.succ : ℕ) - 1, by simp⟩ : Fin (n + 1)) = j.castSucc := Fin.ext (by simp)
  rw [this] at h1
  linarith

theorem lemma_3_4_core {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ)
    (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k)
    (j : Fin n) (a b : ℝ)
    (ha : Tendsto (fun k => f (Δ k j.castSucc)) atTop (𝓝 a))
    (hb : Tendsto (fun k => f (Δ k j.succ)) atTop (𝓝 b)) (hab : a < b) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ i : Fin (n + 1), i ≤ j.castSucc → Δ (k + 1) i = Δ k i := by
  obtain ⟨K, hK⟩ := g56_l34_pos f ρ χ γ σ Δ hrun hnoshrink j a b ha hb hab
  refine ⟨K, fun k hk i hi => ?_⟩
  rw [(hrun.2 k).2 (hnoshrink k)]
  apply g56_iv_lt
  have := hK k hk
  have : i.val ≤ j.val := hi
  omega

theorem corollary_3_1_core {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ)
    (hbdd : BddBelow (Set.range f)) (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k)
    (hinf : ∀ N : ℕ, ∃ k ≥ N, Δ (k + 1) 0 ≠ Δ k 0) :
    ∃ L : ℝ, ∀ i, Tendsto (fun k => f (Δ k i)) atTop (𝓝 L) := by
  obtain ⟨fstar, hlim, -, hmono⟩ := g56_fstar f ρ χ γ σ Δ hrun hbdd 0 (fun k _ => hnoshrink k)
  have hadj : ∀ j : Fin n, fstar j.castSucc = fstar j.succ := by
    intro j
    rcases lt_or_eq_of_le (hmono (Fin.castSucc_le_succ j)) with h | h
    · exfalso
      obtain ⟨K, hK⟩ := lemma_3_4_core f ρ χ γ σ Δ hrun hnoshrink j _ _ (hlim _) (hlim _) h
      obtain ⟨k, hk, hne⟩ := hinf K
      exact hne (hK k hk 0 (Fin.zero_le _))
    · exact h
  have hall : ∀ m (hm : m < n + 1), fstar ⟨m, hm⟩ = fstar 0 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have := hadj ⟨m, by omega⟩
      rw [← ih (by omega)]
      exact this.symm
  refine ⟨fstar 0, fun i => ?_⟩
  have := hall i.val i.isLt
  simp only [Fin.eta] at this
  rw [← this]; exact hlim i

end NelderMeadLD.Dim2

open NelderMeadLD.Dim2


theorem solution {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hbdd : BddBelow (Set.range f)) (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k)
    (j : Fin n) (a b : ℝ)
    (ha : Tendsto (fun k => f (Δ k j.castSucc)) atTop (𝓝 a))
    (hb : Tendsto (fun k => f (Δ k j.succ)) atTop (𝓝 b)) (hab : a < b) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ i : Fin (n + 1), i ≤ j.castSucc → Δ (k + 1) i = Δ k i := by
  exact lemma_3_4_core f ρ χ γ σ Δ hrun hnoshrink j a b ha hb hab
