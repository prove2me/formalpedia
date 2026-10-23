-- Prove2me | solution 1 for NelderMeadLD.Dim2.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:59:06.297624+00:00
-- url     : https://prove2.me/submissions/7c4e66ff-94fc-452d-a247-178e0abfeae9

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

lemma g56_contr {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (x : Fin (n + 1) → E n) (hs : Sorted f x)
    (hns : move f ρ χ γ x ≠ NelderMeadLD.Conv1D.Move.shrink)
    (hv : f (x (nextWorst n)) ≤ f (trial x (tau ρ χ γ (move f ρ χ γ x)))) :
    |tau ρ χ γ (move f ρ χ γ x)| ≤ max (ρ * γ) γ := by
  obtain ⟨hρ, hχ, hρχ, hγ0, hγ1, -, -⟩ := hpar
  have h1n : f (x 0) ≤ f (x (nextWorst n)) := hs _ _ (Fin.zero_le _)
  revert hns hv
  simp only [move]
  by_cases A : f (x 0) ≤ f (trial x ρ) ∧ f (trial x ρ) < f (x (nextWorst n))
  · rw [if_pos A]; intro _ hv; simp only [tau] at hv; linarith [A.2]
  rw [if_neg A]
  by_cases B : f (trial x ρ) < f (x 0)
  · rw [if_pos B]; split_ifs with C <;> intro _ hv <;> simp only [tau] at hv <;> linarith
  rw [if_neg B]
  split_ifs <;> intro hns hv <;> simp only [tau]
  all_goals first
    | exact absurd rfl hns
    | (rw [abs_of_pos (by positivity)]; exact le_max_left _ _)
    | (rw [abs_neg, abs_of_pos hγ0]; exact le_max_right _ _)

lemma g56_trial_sub {n : ℕ} (x : Fin (n + 1) → E n) (τ : ℝ) :
    trial x τ - centroid x = (-τ) • (x (Fin.last n) - centroid x) := by
  simp only [trial]; module

lemma g56_worst_conv {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (hργ : ρ * γ < 1) (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ)
    (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k) (K : ℕ)
    (hp : ∀ k ≥ K, insertPos f (Δ k) (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k)))) = n) :
    (∀ k ≥ K, ∀ i : Fin n, Δ k i.castSucc = Δ K i.castSucc) ∧
    Tendsto (fun k => Δ k (Fin.last n)) atTop (𝓝 (centroid (Δ K))) := by
  have hstep1 : ∀ k ≥ K, ∀ i : Fin n, Δ (k + 1) i.castSucc = Δ k i.castSucc := by
    intro k hk i
    rw [(hrun.2 k).2 (hnoshrink k)]
    apply g56_iv_lt; rw [hp k hk]; simp
  have hstep2 : ∀ k ≥ K, Δ (k + 1) (Fin.last n) =
      trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k))) := by
    intro k hk
    rw [(hrun.2 k).2 (hnoshrink k)]
    apply g56_iv_eq; rw [hp k hk]; simp
  have hfix : ∀ k ≥ K, ∀ i : Fin n, Δ k i.castSucc = Δ K i.castSucc := by
    intro k hk i
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [hstep1 k hk i, ih]
  refine ⟨hfix, ?_⟩
  set c := centroid (Δ K)
  have hcen : ∀ k ≥ K, centroid (Δ k) = c := by
    intro k hk; simp only [c, centroid]; congr 1
    exact Finset.sum_congr rfl (fun i _ => hfix k hk i)
  set q := max (ρ * γ) γ
  have hq0 : 0 ≤ q := le_max_of_le_right hpar.2.2.2.1.le
  have hq1 : q < 1 := max_lt hργ hpar.2.2.2.2.1
  have hcontr : ∀ k ≥ K, ‖Δ (k + 1) (Fin.last n) - c‖ ≤ q * ‖Δ k (Fin.last n) - c‖ := by
    intro k hk
    have hs := g56_run_sorted f ρ χ γ σ Δ hrun k
    have hv : f (Δ k (nextWorst n)) ≤ f (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k)))) := by
      have hn : n - 1 < n := by have := NeZero.ne n; omega
      have := (g56_key f (Δ k) _ hs (n - 1) hn).2 (by rw [hp k hk]; omega)
      simpa [nextWorst] using this
    have ht := g56_contr f ρ χ γ σ hpar _ hs (hnoshrink k) hv
    rw [hstep2 k hk, ← hcen k hk, g56_trial_sub, norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  have hgeo : ∀ m, ‖Δ (m + K) (Fin.last n) - c‖ ≤ q ^ m * ‖Δ K (Fin.last n) - c‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show m + 1 + K = m + K + 1 by ring]
      calc _ ≤ q * ‖Δ (m + K) (Fin.last n) - c‖ := hcontr _ (by omega)
        _ ≤ q * (q ^ m * ‖Δ K (Fin.last n) - c‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (m + 1) * ‖Δ K (Fin.last n) - c‖ := by ring
  rw [← Filter.tendsto_add_atTop_iff_nat K, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun m => norm_nonneg _) hgeo
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖Δ K (Fin.last n) - c‖
  simpa using this

lemma g56_nd_ne_last {n : ℕ} (y : Fin (n + 1) → E n) (hnd : Nondegenerate y) (i : Fin n) :
    y i.castSucc ≠ y (Fin.last n) := by
  intro h; apply hnd
  exact Matrix.det_eq_zero_of_column_eq_zero i (fun r => by simp [edgeMatrix, h])

lemma g56_nd_ne {n : ℕ} (y : Fin (n + 1) → E n) (hnd : Nondegenerate y) (i j : Fin n) (hij : i ≠ j) :
    y i.castSucc ≠ y j.castSucc := by
  intro h; apply hnd
  exact Matrix.det_zero_of_column_eq hij (fun r => by simp [edgeMatrix, h])

lemma g56_cont {n : ℕ} (f : E n → ℝ) (hf : StrictConvexOn ℝ Set.univ f) : Continuous f := by
  have := hf.convexOn.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

theorem lemma_3_6_core {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hf : StrictConvexOn ℝ Set.univ f) (hbdd : BddBelow (Set.range f)) (hργ : ρ * γ < 1) :
    (∃ L : ℝ, Tendsto (fun k => f (Δ k (nextWorst n))) atTop (𝓝 L) ∧
      Tendsto (fun k => f (Δ k (Fin.last n))) atTop (𝓝 L)) ∧
    (2 ≤ n → ∀ N : ℕ, ∃ k ≥ N, Δ (k + 1) (nextWorst n) ≠ Δ k (nextWorst n)) := by
  have hn0 := NeZero.ne n
  have hns := lemma_3_5_core f ρ χ γ σ hpar Δ hrun hnd hf
  have hcont := g56_cont f hf
  set j : Fin n := ⟨n - 1, by omega⟩ with hj
  have hjc : j.castSucc = nextWorst n := Fin.ext (by simp [j, nextWorst])
  have hjs : j.succ = Fin.last n := Fin.ext (by simp [j]; omega)
  constructor
  · obtain ⟨fstar, hlim, -, hmono⟩ := g56_fstar f ρ χ γ σ Δ hrun hbdd 0 (fun k _ => hns k)
    refine ⟨fstar (nextWorst n), hlim _, ?_⟩
    rcases lt_or_eq_of_le (hmono (Fin.le_last (nextWorst n))) with h | h
    · exfalso
      have ha := hlim (nextWorst n); rw [← hjc] at ha
      have hb := hlim (Fin.last n); rw [← hjs] at hb
      obtain ⟨K, hK⟩ := g56_l34_pos f ρ χ γ σ Δ hrun hns j _ _ ha hb (by rw [hjc, hjs]; exact h)
      have hp : ∀ k ≥ K, insertPos f (Δ k) (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k)))) = n := by
        intro k hk; have := hK k hk; have := g56_insertPos_le f (Δ k) (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k))))
        simp [j] at *; omega
      obtain ⟨hfix, hconv⟩ := g56_worst_conv f ρ χ γ σ hpar hργ Δ hrun hns K hp
      have h1 : fstar (Fin.last n) = f (centroid (Δ K)) :=
        tendsto_nhds_unique (hlim _) ((hcont.tendsto _).comp hconv)
      have h2 : fstar (nextWorst n) = f (Δ K (nextWorst n)) := by
        apply tendsto_nhds_unique (hlim _)
        apply tendsto_const_nhds.congr'
        rw [EventuallyEq, eventually_atTop]
        exact ⟨K, fun k hk => by rw [← hjc, hfix k hk j]⟩
      have h3 := (g56_jensen f hf.convexOn (Δ K)).trans
        (g56_avg_le f (Δ K) (g56_run_sorted f ρ χ γ σ Δ hrun K))
      linarith
    · rw [h]; exact hlim _
  · intro hn2 N
    by_contra hcon
    push Not at hcon
    have hp : ∀ k ≥ N, insertPos f (Δ k) (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k)))) = n := by
      intro k hk
      have hle := g56_insertPos_le f (Δ k) (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k))))
      by_contra hne
      have hlt : insertPos f (Δ k) (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k)))) < n := by omega
      have hnd' := g56_run_nd f ρ χ γ σ hpar Δ hrun hnd (k + 1)
      apply g56_nd_ne_last _ hnd' j
      rw [hjc, hcon k hk]
      rw [(hrun.2 k).2 (hns k), g56_iv_gt _ _ _ _ (by simp; omega)]
      congr 1
    obtain ⟨hfix, hconv⟩ := g56_worst_conv f ρ χ γ σ hpar hργ Δ hrun hns N hp
    have hlimc := (hcont.tendsto _).comp hconv
    have hge : f (Δ N (nextWorst n)) ≤ f (centroid (Δ N)) := by
      apply ge_of_tendsto hlimc
      rw [eventually_atTop]
      refine ⟨N, fun k hk => ?_⟩
      have := g56_run_sorted f ρ χ γ σ Δ hrun k (nextWorst n) (Fin.last n) (Fin.le_last _)
      simp only [Function.comp]
      rw [← hjc, ← hfix k hk j]; rw [hjc]; exact this
    have hdist : ∃ i j : Fin n, Δ N i.castSucc ≠ Δ N j.castSucc :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, g56_nd_ne _ (g56_run_nd f ρ χ γ σ hpar Δ hrun hnd N) _ _
        (by simp [Fin.ext_iff])⟩
    have h3 := (g56_jensen_strict f hf (Δ N) hdist).trans_le
      (g56_avg_le f (Δ N) (g56_run_sorted f ρ χ γ σ Δ hrun N))
    linarith

lemma g56_bdd_of_lev {n : ℕ} (f : E n → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) : BddBelow (Set.range f) := by
  have hcont := g56_cont f hf
  have hK : IsCompact {x | f x ≤ f 0} :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const) (hlev _)
  obtain ⟨m, hm⟩ := hK.bddBelow_image hcont.continuousOn
  refine ⟨min m (f 0), ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : f x ≤ f 0
  · exact (min_le_left _ _).trans (hm ⟨x, hx, rfl⟩)
  · push Not at hx; exact (min_le_right _ _).trans hx.le

lemma g56_refl_prop {n : ℕ} (f : E n → ℝ) (ρ χ γ : ℝ) (x : Fin (n + 1) → E n) (hs : Sorted f x)
    (h : move f ρ χ γ x = NelderMeadLD.Conv1D.Move.reflect) :
    f (trial x ρ) < f (x (nextWorst n)) := by
  have h1n : f (x 0) ≤ f (x (nextWorst n)) := hs _ _ (Fin.zero_le _)
  revert h; simp only [move]
  split_ifs <;> intro h <;> first | exact absurd h (by decide) | linarith | (rename_i hA; linarith [hA.2])

lemma g56_out_prop {n : ℕ} (f : E n → ℝ) (ρ χ γ : ℝ) (x : Fin (n + 1) → E n)
    (h : move f ρ χ γ x = NelderMeadLD.Conv1D.Move.outside) :
    f (trial x ρ) < f (x (Fin.last n)) := by
  revert h; simp only [move]
  split_ifs <;> intro h <;> first | exact absurd h (by decide) | assumption

lemma g56_exp_prop {n : ℕ} (f : E n → ℝ) (ρ χ γ : ℝ) (x : Fin (n + 1) → E n)
    (h : move f ρ χ γ x = NelderMeadLD.Conv1D.Move.expand) :
    f (trial x (tau ρ χ γ (move f ρ χ γ x))) < f (x 0) := by
  rw [h]; simp only [tau]
  revert h; simp only [move]
  split_ifs <;> intro h <;> first | exact absurd h (by decide) | linarith

lemma g56_step_info {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (Δ : ℕ → Fin (n + 1) → E n)
    (hrun : IsNMRun f ρ χ γ σ Δ) (k : ℕ) (hns : ¬ IsShrinkAt f ρ χ γ Δ k)
    (hc : Δ (k + 1) 0 = Δ k 0) :
    f (Δ k 0) ≤ f (trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k)))) ∧
    ∃ i : Fin (n + 1), 1 ≤ i.val ∧ Δ (k + 1) i = trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k))) := by
  have hs := g56_run_sorted f ρ χ γ σ Δ hrun k
  have hΔ := (hrun.2 k).2 hns
  set v := trial (Δ k) (tau ρ χ γ (move f ρ χ γ (Δ k)))
  have hp := g56_insertPos_le f (Δ k) v
  have key0 := g56_key f (Δ k) v hs 0 (Nat.pos_of_ne_zero (NeZero.ne n))
  have h0 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
  rw [h0] at key0
  have hle : f (Δ k 0) ≤ f v := by
    by_contra hlt
    have hp0 : 0 = insertPos f (Δ k) v := by
      by_contra hne; exact hlt (key0.2 (by omega))
    have := hc
    rw [hΔ, g56_iv_eq _ _ _ _ (by simpa using hp0)] at this
    rw [this] at hlt; exact hlt le_rfl
  refine ⟨hle, ⟨insertPos f (Δ k) v, by omega⟩, ?_, ?_⟩
  · simp only; have := key0.1 hle; omega
  · rw [hΔ, g56_iv_eq _ _ _ _ rfl]

lemma g56_centroid2 (x : Fin 3 → E 2) : centroid x = (1 / 2 : ℝ) • (x 0 + x 1) := by
  simp [centroid, Fin.sum_univ_two]

lemma g56_mid (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f) (p q : E 2) :
    f ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) ≤ (1 / 2) * f p + (1 / 2) * f q := by
  have := hf.convexOn.2 (Set.mem_univ p) (Set.mem_univ q) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simpa using this

lemma g56_mid_strict (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f) (p q : E 2) (hpq : p ≠ q) :
    f ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) < (1 / 2) * f p + (1 / 2) * f q := by
  have := hf.2 (Set.mem_univ p) (Set.mem_univ q) hpq (by norm_num : (0:ℝ) < 1 / 2)
    (by norm_num : (0:ℝ) < 1 / 2) (by norm_num)
  simpa using this

lemma g56_cen_ge (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f) (Y : Fin 3 → E 2) (L : ℝ)
    (hb : f (Y 0) ≤ L) (h1 : f (Y 1) ≤ L) (hc : L ≤ f (centroid Y)) : Y 1 = Y 0 := by
  by_contra hne
  have := g56_mid_strict f hf (Y 0) (Y 1) (Ne.symm hne)
  rw [g56_centroid2, smul_add] at hc
  linarith

lemma g56_static_out (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f) (Y : Fin 3 → E 2) (L : ℝ)
    (hb : f (Y 0) ≤ L) (h1 : f (Y 1) ≤ L) (hr : f (trial Y 1) ≤ L)
    (hv : L ≤ f (trial Y (1 * (1 / 2)))) : Y 1 = Y 0 ∧ Y 2 = Y 0 := by
  have hcle : f (centroid Y) ≤ L := by
    have := g56_mid f hf (Y 0) (Y 1)
    rw [g56_centroid2, smul_add]; linarith
  have hv' : trial Y (1 * (1 / 2)) = (1 / 2 : ℝ) • centroid Y + (1 / 2 : ℝ) • trial Y 1 := by
    simp only [trial]; module
  have hcr : centroid Y = trial Y 1 := by
    by_contra hne
    have := g56_mid_strict f hf _ _ hne
    rw [← hv'] at this; linarith
  have hvc : trial Y (1 * (1 / 2)) = centroid Y := by rw [hv', ← hcr]; module
  rw [hvc] at hv
  have h10 := g56_cen_ge f hf Y L hb h1 hv
  refine ⟨h10, ?_⟩
  have h2 : Y 2 = (2 : ℝ) • centroid Y - trial Y 1 := by
    simp only [trial, show (Fin.last 2 : Fin 3) = 2 from rfl]; module
  rw [← hcr, g56_centroid2, h10] at h2
  rw [h2]; module

lemma g56_static_in (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f) (Y : Fin 3 → E 2) (L : ℝ)
    (hb : f (Y 0) ≤ L) (h1 : f (Y 1) ≤ L) (h2 : f (Y 2) ≤ L)
    (hv : L ≤ f (trial Y (-(1 / 2)))) : Y 1 = Y 0 ∧ Y 2 = Y 0 := by
  have hcle : f (centroid Y) ≤ L := by
    have := g56_mid f hf (Y 0) (Y 1)
    rw [g56_centroid2, smul_add]; linarith
  have hv' : trial Y (-(1 / 2)) = (1 / 2 : ℝ) • centroid Y + (1 / 2 : ℝ) • Y 2 := by
    simp only [trial, show (Fin.last 2 : Fin 3) = 2 from rfl]; module
  have hcr : centroid Y = Y 2 := by
    by_contra hne
    have := g56_mid_strict f hf _ _ hne
    rw [← hv'] at this; linarith
  have hvc : trial Y (-(1 / 2)) = centroid Y := by rw [hv', ← hcr]; module
  rw [hvc] at hv
  have h10 := g56_cen_ge f hf Y L hb h1 hv
  refine ⟨h10, ?_⟩
  rw [← hcr, g56_centroid2, h10]; module

noncomputable def g56_R (x : Fin 3 → E 2) : Fin 3 → E 2 := ![x 0, trial x 1, x 1]

lemma g56_trial_cont {n : ℕ} (τ : ℝ) : Continuous (fun x : Fin (n + 1) → E n => trial x τ) := by
  unfold trial centroid; fun_prop

lemma g56_R_cont : Continuous g56_R := by
  apply continuous_pi; intro i; fin_cases i
  · exact continuous_apply 0
  · exact g56_trial_cont 1
  · exact continuous_apply 1

lemma g56_trial1 (x : Fin 3 → E 2) : trial x 1 = x 0 + x 1 - x 2 := by
  simp only [trial, g56_centroid2, show (Fin.last 2 : Fin 3) = 2 from rfl]; module

lemma g56_R_eq (x : Fin 3 → E 2) : g56_R x = ![x 0, x 0 + x 1 - x 2, x 1] := by
  simp [g56_R, g56_trial1]

lemma g56_R6 (x : Fin 3 → E 2) : g56_R^[6] x = x := by
  simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id, g56_R_eq]
  funext i; fin_cases i <;> simp <;> abel

lemma g56_R_back (m : ℕ) : ∀ x : Fin 3 → E 2, (g56_R^[m] x) 1 = x 0 → (g56_R^[m] x) 2 = x 0 →
    x 1 = x 0 ∧ x 2 = x 0 := by
  induction m with
  | zero => intro x h1 h2; exact ⟨h1, h2⟩
  | succ m ih =>
    intro x h1 h2
    rw [Function.iterate_succ_apply] at h1 h2
    have h0 : g56_R x 0 = x 0 := by simp [g56_R]
    obtain ⟨a, c⟩ := ih (g56_R x) (by rw [h1, h0]) (by rw [h2, h0])
    rw [g56_R_eq] at a c h0
    simp at a c
    refine ⟨c, ?_⟩
    rw [c] at a
    have : x 2 = x 0 + x 0 - (x 0 + x 0 - x 2) := by abel
    rw [this, a]; abel

theorem lemma_5_1_core (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (χ σ : ℝ)
    (hpar : NelderMeadLD.Conv1D.ParamsOK 1 χ (1 / 2) σ)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 χ (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0))
    (hconst : ∀ k, Δ k 0 = Δ 0 0) :
    ∀ i, Tendsto (fun k => Δ k i) atTop (𝓝 (Δ 0 0)) := by
  set b := Δ 0 0 with hb_def
  have hcont := g56_cont f hf
  have hbdd := g56_bdd_of_lev f hf hlev
  have hns := lemma_3_5_core f 1 χ (1/2) σ hpar Δ hrun hnd hf
  have hsorted := g56_run_sorted f 1 χ (1/2) σ Δ hrun
  obtain ⟨⟨L, hL1, hL2⟩, -⟩ := lemma_3_6_core f 1 χ (1/2) σ hpar Δ hrun hnd hf hbdd (by norm_num)
  have hnw : nextWorst 2 = 1 := rfl
  have hl2 : (Fin.last 2 : Fin 3) = 2 := rfl
  rw [hnw] at hL1; rw [hl2] at hL2
  have hanti : ∀ i, Antitone (fun k => f (Δ k i)) := fun i =>
    antitone_nat_of_succ_le (fun k => (g56_ns_step f 1 χ (1/2) σ Δ hrun k (hns k)).1 i)
  have hlow1 : ∀ m, L ≤ f (Δ m 1) := (hanti 1).le_of_tendsto hL1
  have hlow2 : ∀ m, L ≤ f (Δ m 2) := (hanti 2).le_of_tendsto hL2
  have hbL : f b ≤ L := by
    apply ge_of_tendsto' hL1; intro m; rw [← hconst m]; exact hsorted m 0 1 (by decide)
  have hc : ∀ k, Δ (k + 1) 0 = Δ k 0 := fun k => by rw [hconst, hconst k]
  have hv : ∀ k, L ≤ f (trial (Δ k) (tau 1 χ (1/2) (move f 1 χ (1/2) (Δ k)))) := by
    intro k
    obtain ⟨-, i, hi, hie⟩ := g56_step_info f 1 χ (1/2) σ Δ hrun k (hns k) (hc k)
    rw [← hie]
    fin_cases i
    · simp at hi
    · exact hlow1 _
    · exact hlow2 _
  have hnexp : ∀ k, move f 1 χ (1/2) (Δ k) ≠ NelderMeadLD.Conv1D.Move.expand := by
    intro k h
    have h1 := g56_exp_prop f 1 χ (1/2) (Δ k) h
    have h2 := (g56_step_info f 1 χ (1/2) σ Δ hrun k (hns k) (hc k)).1
    linarith
  have hrefl : ∀ k, move f 1 χ (1/2) (Δ k) = NelderMeadLD.Conv1D.Move.reflect →
      Δ (k + 1) = g56_R (Δ k) ∧ f (Δ (k + 1) 1) < f (Δ k 1) := by
    intro k h
    have hs := hsorted k
    have h1 := g56_refl_prop f 1 χ (1/2) (Δ k) hs h
    rw [hnw] at h1
    have h2 := (g56_step_info f 1 χ (1/2) σ Δ hrun k (hns k) (hc k)).1
    rw [h] at h2; simp only [tau] at h2
    have hΔ := (hrun.2 k).2 (hns k)
    rw [h] at hΔ; simp only [tau] at hΔ
    have key0 : f (Δ k 0) ≤ f (trial (Δ k) 1) ↔ 0 < insertPos f (Δ k) (trial (Δ k) 1) :=
      g56_key f (Δ k) (trial (Δ k) 1) hs 0 (by norm_num)
    have key1 : f (Δ k 1) ≤ f (trial (Δ k) 1) ↔ 1 < insertPos f (Δ k) (trial (Δ k) 1) :=
      g56_key f (Δ k) (trial (Δ k) 1) hs 1 (by norm_num)
    have hp : insertPos f (Δ k) (trial (Δ k) 1) = 1 := by
      have a := key0.1 h2
      have b' : ¬ (1 < insertPos f (Δ k) (trial (Δ k) 1)) := fun hh => by
        have := key1.2 hh; linarith
      omega
    have hR : Δ (k + 1) = g56_R (Δ k) := by
      rw [hΔ]; funext i; fin_cases i
      · exact g56_iv_lt _ _ _ _ (by simp [hp])
      · exact g56_iv_eq _ _ _ _ (by simp [hp])
      · rw [g56_iv_gt _ _ _ _ (by simp [hp])]; rfl
    refine ⟨hR, ?_⟩
    rw [hR]; simpa [g56_R] using h1
  have hcyc : ∀ k, ∃ d, d < 6 ∧ move f 1 χ (1/2) (Δ (k + d)) ≠ NelderMeadLD.Conv1D.Move.reflect := by
    intro k
    by_contra hcon
    push Not at hcon
    have hind : ∀ d ≤ 6, Δ (k + d) = g56_R^[d] (Δ k) ∧ (0 < d → f (Δ (k + d) 1) < f (Δ k 1)) := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        obtain ⟨r1, r2⟩ := hrefl (k + d) (hcon d (by omega))
        refine ⟨?_, fun _ => ?_⟩
        · rw [← add_assoc, r1, ih1, Function.iterate_succ_apply']
        · rw [← add_assoc]
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · subst h0; simpa using r2
          · exact r2.trans (ih2 h0)
    obtain ⟨e1, e2⟩ := hind 6 le_rfl
    rw [g56_R6] at e1
    have := e2 (by norm_num)
    rw [e1] at this; exact lt_irrefl _ this
  have hbd : ∀ k i, Δ k i ∈ {x | f x ≤ f (Δ 0 2)} := by
    intro k i
    show f (Δ k i) ≤ f (Δ 0 2)
    exact (hsorted k i 2 (Fin.le_last i)).trans (hanti 2 (Nat.zero_le k))
  have hlimY : ∀ (kk : ℕ → ℕ) (Y : Fin 3 → E 2), Tendsto kk atTop atTop →
      Tendsto (fun j => Δ (kk j)) atTop (𝓝 Y) → Y 0 = b ∧ f (Y 1) = L ∧ f (Y 2) = L := by
    intro kk Y hkk hY
    refine ⟨?_, ?_, ?_⟩
    · exact tendsto_nhds_unique (tendsto_pi_nhds.1 hY 0)
        (tendsto_const_nhds.congr (fun j => (hconst _).symm))
    · exact tendsto_nhds_unique ((hcont.tendsto _).comp (tendsto_pi_nhds.1 hY 1)) (hL1.comp hkk)
    · exact tendsto_nhds_unique ((hcont.tendsto _).comp (tendsto_pi_nhds.1 hY 2)) (hL2.comp hkk)
  have hA : ∀ (kk : ℕ → ℕ) (Y : Fin 3 → E 2), Tendsto kk atTop atTop →
      Tendsto (fun j => Δ (kk j)) atTop (𝓝 Y) →
      (∀ j, move f 1 χ (1/2) (Δ (kk j)) ≠ NelderMeadLD.Conv1D.Move.reflect) → Y 1 = b ∧ Y 2 = b := by
    intro kk Y hkk hY hnr
    by_cases hfr : ∃ᶠ j in atTop, move f 1 χ (1/2) (Δ (kk j)) = NelderMeadLD.Conv1D.Move.outside
    · obtain ⟨ψ, hψ, hψP⟩ := extraction_of_frequently_atTop hfr
      have hkk' : Tendsto (kk ∘ ψ) atTop atTop := hkk.comp hψ.tendsto_atTop
      have hY' : Tendsto (fun j => Δ ((kk ∘ ψ) j)) atTop (𝓝 Y) := hY.comp hψ.tendsto_atTop
      obtain ⟨hY0, hY1, hY2⟩ := hlimY _ Y hkk' hY'
      have hr : f (trial Y 1) ≤ L := by
        refine le_of_tendsto_of_tendsto' ((hcont.tendsto _).comp
          (((g56_trial_cont 1).tendsto Y).comp hY')) (hL2.comp hkk') (fun j => ?_)
        have := g56_out_prop f 1 χ (1/2) _ (hψP j)
        rw [hl2] at this; exact this.le
      have hvY : L ≤ f (trial Y (1 * (1 / 2))) := by
        refine ge_of_tendsto' ((hcont.tendsto _).comp
          (((g56_trial_cont _).tendsto Y).comp hY')) (fun j => ?_)
        have := hv (kk (ψ j))
        rw [hψP j] at this; simpa [tau] using this
      have := g56_static_out f hf Y L (hY0 ▸ hbL) hY1.le hr hvY
      rw [hY0] at this; exact this
    · have hin : ∀ᶠ j in atTop, move f 1 χ (1/2) (Δ (kk j)) = NelderMeadLD.Conv1D.Move.inside := by
        rw [not_frequently] at hfr
        filter_upwards [hfr] with j hj
        cases h : move f 1 χ (1/2) (Δ (kk j))
        · exact absurd h (hnr j)
        · exact absurd h (hnexp _)
        · exact absurd h hj
        · rfl
        · exact absurd h (hns _)
      obtain ⟨ψ, hψ, hψP⟩ := extraction_of_frequently_atTop hin.frequently
      have hkk' : Tendsto (kk ∘ ψ) atTop atTop := hkk.comp hψ.tendsto_atTop
      have hY' : Tendsto (fun j => Δ ((kk ∘ ψ) j)) atTop (𝓝 Y) := hY.comp hψ.tendsto_atTop
      obtain ⟨hY0, hY1, hY2⟩ := hlimY _ Y hkk' hY'
      have hvY : L ≤ f (trial Y (-(1 / 2))) := by
        refine ge_of_tendsto' ((hcont.tendsto _).comp
          (((g56_trial_cont _).tendsto Y).comp hY')) (fun j => ?_)
        have := hv (kk (ψ j))
        rw [hψP j] at this; simpa [tau] using this
      have := g56_static_in f hf Y L (hY0 ▸ hbL) hY1.le hY2.le hvY
      rw [hY0] at this; exact this
  have hA' : ∀ (kk : ℕ → ℕ) (Y : Fin 3 → E 2), StrictMono kk →
      Tendsto (fun j => Δ (kk j)) atTop (𝓝 Y) → Y = fun _ => b := by
    intro kk Y hkk hY
    classical
    let d : ℕ → ℕ := fun k => Nat.find (hcyc k)
    have hd1 : ∀ k, d k < 6 ∧ move f 1 χ (1/2) (Δ (k + d k)) ≠ NelderMeadLD.Conv1D.Move.reflect :=
      fun k => Nat.find_spec (hcyc k)
    have hd2 : ∀ k, ∀ i < d k, move f 1 χ (1/2) (Δ (k + i)) = NelderMeadLD.Conv1D.Move.reflect := by
      intro k i hi
      have := Nat.find_min (hcyc k) hi
      push Not at this
      exact this (by have := (hd1 k).1; omega)
    have hpig : ∃ d0, ∃ᶠ j in atTop, d (kk j) = d0 := by
      by_contra hcon
      push Not at hcon
      have : ∀ᶠ j in atTop, ∀ d0 ∈ Finset.range 6, ¬ d (kk j) = d0 :=
        (Filter.eventually_all_finset _).2 (fun d0 _ => hcon d0)
      obtain ⟨j, hj⟩ := this.exists
      exact hj (d (kk j)) (Finset.mem_range.2 (hd1 _).1) rfl
    obtain ⟨d0, hfreq⟩ := hpig
    obtain ⟨ψ, hψ, hψP⟩ := extraction_of_frequently_atTop hfreq
    have hkk' : Tendsto (kk ∘ ψ) atTop atTop := (hkk.comp hψ).tendsto_atTop
    have hY' : Tendsto (fun j => Δ ((kk ∘ ψ) j)) atTop (𝓝 Y) := hY.comp hψ.tendsto_atTop
    have hit : ∀ i ≤ d0, Tendsto (fun j => Δ ((kk ∘ ψ) j + i)) atTop (𝓝 (g56_R^[i] Y)) := by
      intro i
      induction i with
      | zero => intro _; simpa using hY'
      | succ i ih =>
        intro hi
        have heq : ∀ j, Δ ((kk ∘ ψ) j + (i + 1)) = g56_R (Δ ((kk ∘ ψ) j + i)) := by
          intro j
          have := (hrefl _ (hd2 ((kk ∘ ψ) j) i (by simp only [Function.comp]; rw [hψP j]; omega))).1
          rw [← add_assoc]; exact this
        simp only [heq, Function.iterate_succ_apply']
        exact (g56_R_cont.tendsto _).comp (ih (by omega))
    have hkk'' : Tendsto (fun j => (kk ∘ ψ) j + d0) atTop atTop :=
      tendsto_atTop_mono (fun j => Nat.le_add_right _ _) hkk'
    have hfin := hA (fun j => (kk ∘ ψ) j + d0) _ hkk'' (hit d0 le_rfl) (fun j => by
      have := (hd1 ((kk ∘ ψ) j)).2
      simp only [Function.comp] at this ⊢; rwa [hψP j] at this)
    have hY0 := (hlimY _ Y hkk' hY').1
    have hRb : ∀ m, (g56_R^[m] Y) 0 = Y 0 := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply']; simp [g56_R, ih]
    obtain ⟨e1, e2⟩ := g56_R_back d0 Y (by rw [hfin.1, hY0]) (by rw [hfin.2, hY0])
    funext i; fin_cases i
    · exact hY0
    · exact e1.trans hY0
    · exact e2.trans hY0
  have hmain : Tendsto Δ atTop (𝓝 (fun _ => b)) := by
    by_contra hnt
    rw [Metric.tendsto_atTop] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hN⟩ := hnt
    have hfr : ∃ᶠ k in atTop, ε ≤ dist (Δ k) (fun _ => b) := Filter.frequently_atTop.2 hN
    obtain ⟨φ1, hφ1, hφ1P⟩ := extraction_of_frequently_atTop hfr
    have hbdset : Bornology.IsBounded (Set.univ.pi (fun _ : Fin 3 => {x | f x ≤ f (Δ 0 2)})) :=
      Bornology.IsBounded.pi (fun _ => hlev _)
    obtain ⟨Y, -, φ2, hφ2, hY⟩ := tendsto_subseq_of_bounded hbdset
      (x := fun j => Δ (φ1 j)) (fun j => Set.mem_univ_pi.2 (fun i => hbd _ i))
    have hYb := hA' (φ1 ∘ φ2) Y (hφ1.comp hφ2) hY
    have hd : ε ≤ dist Y (fun _ => b) :=
      ge_of_tendsto (hY.dist tendsto_const_nhds) (Eventually.of_forall (fun j => hφ1P (φ2 j)))
    rw [hYb, dist_self] at hd
    linarith
  intro i
  exact tendsto_pi_nhds.1 hmain i

end NelderMeadLD.Dim2

open NelderMeadLD.Dim2


theorem solution (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (χ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK 1 χ (1 / 2) σ)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 χ (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0))
    (hconst : ∀ k, Δ k 0 = Δ 0 0) :
    ∀ i, Tendsto (fun k => Δ k i) atTop (𝓝 (Δ 0 0)) := by
  exact lemma_5_1_core f hf hlev χ σ hpar Δ hrun hnd hconst
