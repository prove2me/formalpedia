-- Prove2me | solution 1 for ModernConvex.Truss.strict_epigraph_cqr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:18:36.224684+00:00
-- url     : https://prove2.me/submissions/e6a6898d-5f73-4018-a7f0-d16996c7ac6d

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix ModernConvex.Truss

lemma g70mc1_range {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (f : Fin m → ℝ)
    (hf : ∀ w, A *ᵥ w = 0 → f ⬝ᵥ w = 0) : ∃ v, A *ᵥ v = f := by
  have hT : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  have hF : WithLp.toLp 2 f ∈ LinearMap.range (Matrix.toEuclideanLin A) := by
    rw [← Submodule.orthogonal_orthogonal (LinearMap.range (Matrix.toEuclideanLin A)),
      hT.orthogonal_range, Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have h1 : A *ᵥ WithLp.ofLp u = 0 := by
      have := congrArg WithLp.ofLp hu
      simpa using this
    simpa using hf _ h1
  obtain ⟨V, hV⟩ := hF
  refine ⟨WithLp.ofLp V, ?_⟩
  have := congrArg WithLp.ofLp hV
  simpa using this

lemma g70mc1_stiff_mulVec {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (v : Fin m → ℝ) :
    stiffness B t *ᵥ v = ∑ i, t i • (B i *ᵥ ((B i)ᵀ *ᵥ v)) := by
  simp [stiffness, sum_mulVec, smul_mulVec, mulVec_mulVec]

lemma g70mc1_dot_B {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (w : Fin m → ℝ) (y : Fin k → ℝ) :
    w ⬝ᵥ (B *ᵥ y) = (Bᵀ *ᵥ w) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma g70mc1_quad {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (w : Fin m → ℝ) :
    w ⬝ᵥ (stiffness B t *ᵥ w) = ∑ i, t i * (((B i)ᵀ *ᵥ w) ⬝ᵥ ((B i)ᵀ *ᵥ w)) := by
  rw [g70mc1_stiff_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, g70mc1_dot_B, smul_eq_mul]

lemma g70mc1_herm {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) :
    (stiffness B t).IsHermitian := by
  unfold IsHermitian stiffness
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_smul, conjTranspose_mul]
  simp [conjTranspose_eq_transpose_of_trivial]

lemma g70mc1_nn {k : ℕ} (x : Fin k → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem solution {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (τ : ℝ) :
    compliance B f t < (τ : EReal) ↔
      ∃ s : (i : Fin n) → Fin (k i) → ℝ,
        ∑ i, B i *ᵥ s i = f ∧
        (∀ i, t i = 0 → s i = 0) ∧
        ∑ i, (s i ⬝ᵥ s i) / (2 * t i) < τ := by
  constructor
  · intro hc
    unfold compliance at hc
    split_ifs at hc with h
    · have hv := h.choose_spec
      set v := h.choose
      rw [EReal.coe_lt_coe_iff] at hc
      refine ⟨fun i => t i • ((B i)ᵀ *ᵥ v), ?_, ?_, ?_⟩
      · rw [← hv, g70mc1_stiff_mulVec]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mulVec_smul]
      · intro i hi; simp [hi]
      · have e : ∑ i, ((t i • ((B i)ᵀ *ᵥ v)) ⬝ᵥ (t i • ((B i)ᵀ *ᵥ v))) / (2 * t i)
            = (1 / 2 : ℝ) * (f ⬝ᵥ v) := by
          rw [← hv, dotProduct_comm, g70mc1_quad, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
          rcases eq_or_ne (t i) 0 with h0 | h0
          · simp [h0]
          · field_simp
        exact lt_of_eq_of_lt e hc
    · simp at hc
  · rintro ⟨s, hs, hs0, hlt⟩
    set A := stiffness B t
    have hsol : ∃ v, A *ᵥ v = f := by
      apply g70mc1_range A (g70mc1_herm B t) f
      intro w hw
      have hq : ∑ i, t i * (((B i)ᵀ *ᵥ w) ⬝ᵥ ((B i)ᵀ *ᵥ w)) = 0 := by
        rw [← g70mc1_quad, hw, dotProduct_zero]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        mul_nonneg (ht i) (g70mc1_nn ((B i)ᵀ *ᵥ w)))).1 hq
      rw [← hs, dotProduct_comm, dotProduct_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [g70mc1_dot_B]
      rcases eq_or_ne (t i) 0 with h0 | h0
      · rw [hs0 i h0, dotProduct_zero]
      · have := hz i hi
        have hw0 : (B i)ᵀ *ᵥ w = 0 :=
          dotProduct_self_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0)
        rw [hw0, zero_dotProduct]
    unfold compliance
    rw [dif_pos hsol]
    have hv := hsol.choose_spec
    set v := hsol.choose
    rw [EReal.coe_lt_coe_iff]
    -- f ⬝ v = ∑ s_i ⬝ w_i and = ∑ t_i |w_i|²
    have h1 : f ⬝ᵥ v = ∑ i, s i ⬝ᵥ ((B i)ᵀ *ᵥ v) := by
      rw [← hs, sum_dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dotProduct_comm, g70mc1_dot_B, dotProduct_comm]
    have h2 : f ⬝ᵥ v = ∑ i, t i * (((B i)ᵀ *ᵥ v) ⬝ᵥ ((B i)ᵀ *ᵥ v)) := by
      rw [← hv, dotProduct_comm, g70mc1_quad]
    have h3 : ∀ i, s i ⬝ᵥ ((B i)ᵀ *ᵥ v) ≤
        (s i ⬝ᵥ s i) / (2 * t i) + t i * (((B i)ᵀ *ᵥ v) ⬝ᵥ ((B i)ᵀ *ᵥ v)) / 2 := by
      intro i
      set w := (B i)ᵀ *ᵥ v
      rcases eq_or_ne (t i) 0 with h0 | h0
      · simp [hs0 i h0, h0]
      · have htp : 0 < t i := lt_of_le_of_ne (ht i) (Ne.symm h0)
        have hsq := g70mc1_nn (s i - t i • w)
        simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
          smul_eq_mul] at hsq
        rw [dotProduct_comm w (s i)] at hsq
        rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
        nlinarith
    have h4 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← h2, ← h1] at h4
    linarith
