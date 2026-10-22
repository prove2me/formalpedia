-- Prove2me | solution 1 for ModernConvex.Truss.strict_epigraph_dual_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:24:45.83897+00:00
-- url     : https://prove2.me/submissions/77f04beb-6b51-498c-8218-f6b439ada725

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

theorem g70mc1_cqr {n m : ℕ} {k : Fin n → ℕ}
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

lemma g70mc1_ATl {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (f : Fin m → ℝ)
    (l : CQIIndex k → ℝ) :
    (cqiMatrix B t f)ᵀ *ᵥ l = (∑ i, B i *ᵥ (fun j => Real.sqrt 2 * Real.sqrt (t i) *
      l (Sum.inl (Sum.inl ⟨i, j⟩)))) + (l (Sum.inr ()) - l (Sum.inl (Sum.inr ()))) • f := by
  ext c
  simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type, Fintype.sum_sigma,
    cqiMatrix, stackedMatrix, of_apply, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Fintype.univ_unit, Finset.sum_singleton]
  have : ∀ i, ∑ j, Real.sqrt 2 * Real.sqrt (t i) * B i c j * l (Sum.inl (Sum.inl ⟨i, j⟩)) =
      ∑ j, B i c j * (Real.sqrt 2 * Real.sqrt (t i) * l (Sum.inl (Sum.inl ⟨i, j⟩))) := by
    intro i; refine Finset.sum_congr rfl fun j _ => ?_; ring
  simp only [this]
  ring

lemma g70mc1_bl {n : ℕ} (k : Fin n → ℕ) (τ : ℝ) (l : CQIIndex k → ℝ) :
    cqiRhs k τ ⬝ᵥ l = (-1 - τ) * l (Sum.inl (Sum.inr ())) + (-1 + τ) * l (Sum.inr ()) := by
  simp [dotProduct, Fintype.sum_sum_type, cqiRhs]

lemma g70mc1_lor {n : ℕ} (k : Fin n → ℕ) (l : CQIIndex k → ℝ) :
    l ∈ lorentzCone ((Σ i, Fin (k i)) ⊕ Unit) ↔
      Real.sqrt (∑ i, ∑ j, l (Sum.inl (Sum.inl ⟨i, j⟩)) ^ 2 + l (Sum.inl (Sum.inr ())) ^ 2)
        ≤ l (Sum.inr ()) := by
  simp [lorentzCone, Fintype.sum_sum_type, Fintype.sum_sigma]

theorem g70mc1_dual {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (τ : ℝ) :
    compliance B f t < (τ : EReal) ↔
      ∃ l : CQIIndex k → ℝ, (cqiMatrix B t f)ᵀ *ᵥ l = 0 ∧ 0 < cqiRhs k τ ⬝ᵥ l ∧
        l ∈ lorentzCone ((Σ i, Fin (k i)) ⊕ Unit) := by
  rw [g70mc1_cqr B t ht f τ]
  constructor
  · rintro ⟨s, hs, hs0, hlt⟩
    set σ := ∑ i, (s i ⬝ᵥ s i) / (2 * t i) with hσ
    have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun i _ =>
      div_nonneg (g70mc1_nn _) (mul_nonneg (by norm_num) (ht i))
    let l : CQIIndex k → ℝ := fun r => match r with
      | Sum.inl (Sum.inl q) => -s q.1 q.2 / (Real.sqrt 2 * Real.sqrt (t q.1))
      | Sum.inl (Sum.inr _) => (σ - 1) / 2
      | Sum.inr _ => (σ + 1) / 2
    have hcoef : ∀ i j, Real.sqrt 2 * Real.sqrt (t i) * l (Sum.inl (Sum.inl ⟨i, j⟩)) = -s i j := by
      intro i j
      simp only [l]
      rcases eq_or_ne (t i) 0 with h0 | h0
      · simp [hs0 i h0]
      · have : 0 < Real.sqrt 2 * Real.sqrt (t i) :=
          mul_pos (by positivity) (Real.sqrt_pos.2 (lt_of_le_of_ne (ht i) (Ne.symm h0)))
        rw [mul_div_assoc', mul_neg, neg_div, mul_div_cancel_left₀ _ this.ne']
    have hsq : ∀ i, ∑ j, l (Sum.inl (Sum.inl ⟨i, j⟩)) ^ 2 = (s i ⬝ᵥ s i) / (2 * t i) := by
      intro i
      simp only [l]
      rcases eq_or_ne (t i) 0 with h0 | h0
      · simp [hs0 i h0]
      · have htp : 0 < t i := lt_of_le_of_ne (ht i) (Ne.symm h0)
        rw [dotProduct, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt htp.le]
        ring
    refine ⟨l, ?_, ?_, ?_⟩
    · rw [g70mc1_ATl]
      simp only [hcoef]
      have : ∀ i, (B i *ᵥ fun j => -s i j) = -(B i *ᵥ s i) := by
        intro i; rw [← mulVec_neg]; rfl
      simp only [this, Finset.sum_neg_distrib, hs, l]
      ext c; simp; ring
    · rw [g70mc1_bl]; simp only [l]; nlinarith
    · rw [g70mc1_lor]
      simp only [hsq]
      rw [← hσ]
      simp only [l]
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
  · rintro ⟨l, hA, hb, hL⟩
    rw [g70mc1_bl] at hb
    rw [g70mc1_lor] at hL
    rw [g70mc1_ATl] at hA
    set lm := l (Sum.inl (Sum.inr ()))
    set lp := l (Sum.inr ())
    set Q := ∑ i, ∑ j, l (Sum.inl (Sum.inl ⟨i, j⟩)) ^ 2 with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hlp : 0 ≤ lp := le_trans (Real.sqrt_nonneg _) hL
    have hL2 : Q + lm ^ 2 ≤ lp ^ 2 := by
      rw [Real.sqrt_le_left hlp] at hL; exact hL
    set α := lp - lm with hα
    have hlm : lm ≤ lp := by
      by_contra h; push Not at h; nlinarith
    have hα0 : 0 < α := by
      by_contra h
      have e : lm = lp := by linarith
      rw [e] at hb; nlinarith
    let s : (i : Fin n) → Fin (k i) → ℝ :=
      fun i j => -(Real.sqrt 2 * Real.sqrt (t i) * l (Sum.inl (Sum.inl ⟨i, j⟩))) / α
    refine ⟨s, ?_, ?_, ?_⟩
    · have hsum : (∑ i, B i *ᵥ (fun j => Real.sqrt 2 * Real.sqrt (t i) *
          l (Sum.inl (Sum.inl ⟨i, j⟩)))) = -(α • f) := eq_neg_of_add_eq_zero_left hA
      have : ∀ i, B i *ᵥ s i = (-α⁻¹) • (B i *ᵥ (fun j => Real.sqrt 2 * Real.sqrt (t i) *
          l (Sum.inl (Sum.inl ⟨i, j⟩)))) := by
        intro i
        rw [← mulVec_smul]; congr 1; ext j; simp only [s, Pi.smul_apply, smul_eq_mul]; ring
      simp only [this]
      rw [← Finset.smul_sum, hsum, smul_neg, neg_smul, neg_neg, smul_smul,
        inv_mul_cancel₀ hα0.ne', one_smul]
    · intro i hi; ext j; simp [s, hi]
    · have hterm : ∀ i, (s i ⬝ᵥ s i) / (2 * t i) ≤
          (∑ j, l (Sum.inl (Sum.inl ⟨i, j⟩)) ^ 2) / α ^ 2 := by
        intro i
        rcases eq_or_ne (t i) 0 with h0 | h0
        · simp only [s, h0]; simp; positivity
        · have htp : 0 < t i := lt_of_le_of_ne (ht i) (Ne.symm h0)
          apply le_of_eq
          rw [dotProduct, Finset.sum_div, Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [s]
          rw [div_mul_div_comm, neg_mul_neg, mul_mul_mul_comm, ← sq, ← sq, mul_pow,
            Real.sq_sqrt (by norm_num), Real.sq_sqrt htp.le]
          field_simp
      have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
      rw [← Finset.sum_div] at h1
      have h2 : Q / α ^ 2 < τ := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      exact lt_of_le_of_lt h1 h2

theorem solution {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (τ : ℝ) :
    compliance B f t < (τ : EReal) ↔
      ∃ l : CQIIndex k → ℝ, (cqiMatrix B t f)ᵀ *ᵥ l = 0 ∧ 0 < cqiRhs k τ ⬝ᵥ l ∧
        l ∈ lorentzCone ((Σ i, Fin (k i)) ⊕ Unit) := by
  exact g70mc1_dual B t ht f τ

