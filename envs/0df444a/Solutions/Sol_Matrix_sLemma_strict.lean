-- Prove2me | solution 1 for Matrix.sLemma_strict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:48:49.880119+00:00
-- url     : https://prove2.me/submissions/624676fc-bc0f-44e8-a1dd-fff6a44d8a8a

import Mathlib

set_option autoImplicit false
open Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [Fintype G] [DecidableEq G] (u : G → F)

-- the support library of submission 3c55ced4-4944-4de2-ba43-8110d2682db1, lines 1155-1234, carved out verbatim

private lemma aux2_pair_real (ax bx ay by' ka kb s₁ s₂ : ℝ) (hx : 0 < bx) (hs₁ : s₁ < 0) (hs₂ : 0 < s₂)
    (hb₁ : bx + s₁ * kb + s₁ ^ 2 * by' = 0) (hb₂ : bx + s₂ * kb + s₂ ^ 2 * by' = 0)
    (ha₁ : 0 ≤ ax + s₁ * ka + s₁ ^ 2 * ay) (ha₂ : 0 ≤ ax + s₂ * ka + s₂ ^ 2 * ay) :
    0 ≤ ay * bx - ax * by' := by
  by_contra hC
  push Not at hC
  set C := ay * bx - ax * by'
  set γ := ka * bx - ax * kb
  -- h(s) = (a-part)·bx - ax·(b-part) = s γ + s² C
  have e₁ : (ax + s₁ * ka + s₁ ^ 2 * ay) * bx - ax * (bx + s₁ * kb + s₁ ^ 2 * by') =
      s₁ * (γ + s₁ * C) := by simp only [γ, C]; ring
  have e₂ : (ax + s₂ * ka + s₂ ^ 2 * ay) * bx - ax * (bx + s₂ * kb + s₂ ^ 2 * by') =
      s₂ * (γ + s₂ * C) := by simp only [γ, C]; ring
  rw [hb₁, mul_zero, sub_zero] at e₁
  rw [hb₂, mul_zero, sub_zero] at e₂
  have h₁ : 0 ≤ s₁ * (γ + s₁ * C) := e₁ ▸ mul_nonneg ha₁ hx.le
  have h₂ : 0 ≤ s₂ * (γ + s₂ * C) := e₂ ▸ mul_nonneg ha₂ hx.le
  have h₁' : γ + s₁ * C ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have h₂' : 0 ≤ γ + s₂ * C := by
    by_contra h; push Not at h; nlinarith
  nlinarith
private lemma aux2_roots (bx by' kb : ℝ) (hx : 0 < bx) (hy : by' < 0) :
    ∃ s₁ s₂ : ℝ, s₁ < 0 ∧ 0 < s₂ ∧ bx + s₁ * kb + s₁ ^ 2 * by' = 0 ∧
      bx + s₂ * kb + s₂ ^ 2 * by' = 0 := by
  have hD : 0 ≤ kb ^ 2 - 4 * bx * by' := by nlinarith
  set r := Real.sqrt (kb ^ 2 - 4 * bx * by') with hr_def
  have hr2 : r ^ 2 = kb ^ 2 - 4 * bx * by' := Real.sq_sqrt hD
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrk1 : kb < r := by nlinarith
  have hrk2 : -kb < r := by nlinarith
  have hy2 : (2 * by') ≠ 0 := by linarith
  have hy4 : (4 * by') ≠ 0 := by linarith
  refine ⟨(-kb + r) / (2 * by'), (-kb - r) / (2 * by'), ?_, ?_, ?_, ?_⟩
  · exact div_neg_of_pos_of_neg (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · set s := (-kb + r) / (2 * by')
    have hs : 2 * by' * s = -kb + r := by simp only [s]; field_simp; exact mul_div_cancel_left₀ _ (ne_of_lt hy)
    have : 4 * by' * (bx + s * kb + s ^ 2 * by') = 0 := by
      linear_combination (2 * by' * s + kb + r) * hs + hr2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy4
    · exact h
  · set s := (-kb - r) / (2 * by')
    have hs : 2 * by' * s = -kb - r := by simp only [s]; field_simp; exact mul_div_cancel_left₀ _ (ne_of_lt hy)
    have : 4 * by' * (bx + s * kb + s ^ 2 * by') = 0 := by
      linear_combination (2 * by' * s + kb - r) * hs + hr2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy4
    · exact h
private lemma aux2_core {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V → ℝ)
    (ha : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, a (x + s • y) = a x + s * k + s ^ 2 * a y)
    (hb : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, b (x + s • y) = b x + s * k + s ^ 2 * b y)
    (hslater : ∃ x₀, 0 < b x₀) (H : ∀ x, 0 ≤ b x → 0 ≤ a x) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ a x - τ * b x := by
  -- pair inequality
  have hpair : ∀ x y, 0 < b x → b y < 0 → 0 ≤ a y * b x - a x * b y := by
    intro x y hx hy
    obtain ⟨ka, hka⟩ := ha x y
    obtain ⟨kb, hkb⟩ := hb x y
    obtain ⟨s₁, s₂, hs₁, hs₂, h₁, h₂⟩ := aux2_roots (b x) (b y) kb hx hy
    refine aux2_pair_real (a x) (b x) (a y) (b y) ka kb s₁ s₂ hx hs₁ hs₂ h₁ h₂ ?_ ?_
    · rw [← hka]; exact H _ (by rw [hkb, h₁])
    · rw [← hka]; exact H _ (by rw [hkb, h₂])
  obtain ⟨x₀, hx₀⟩ := hslater
  let S : Set ℝ := {q | ∃ x, 0 < b x ∧ q = a x / b x}
  have hSne : S.Nonempty := ⟨_, x₀, hx₀, rfl⟩
  have hS0 : ∀ q ∈ S, 0 ≤ q := by
    rintro q ⟨x, hx, rfl⟩; exact div_nonneg (H x hx.le) hx.le
  have hSbdd : BddBelow S := ⟨0, hS0⟩
  refine ⟨sInf S, le_csInf hSne hS0, fun x => ?_⟩
  rcases lt_trichotomy (b x) 0 with hneg | hzero | hpos
  · have hle : a x / b x ≤ sInf S := by
      refine le_csInf hSne ?_
      rintro q ⟨z, hz, rfl⟩
      rw [div_le_iff_of_neg hneg, div_mul_eq_mul_div, div_le_iff₀ hz]
      linarith [hpair z x hz hneg]
    rw [div_le_iff_of_neg hneg] at hle
    linarith
  · rw [hzero, mul_zero, sub_zero]; exact H x hzero.ge
  · have hle : sInf S ≤ a x / b x := csInf_le hSbdd ⟨x, hpos, rfl⟩
    rw [le_div_iff₀ hpos] at hle
    linarith
private lemma aux2_dot_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
private lemma aux2_dot_self_pos {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (aux2_dot_self_nonneg v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))
private lemma aux2_isHermitian {n : Type*} {A : Matrix n n ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hA
private lemma aux2_normalize {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (c • v) ⬝ᵥ (c • v) = 1 := by
  have hpos := aux2_dot_self_pos hv
  have hs : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
  have hs2 : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹, inv_pos.2 hs, ?_⟩
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  linarith [hs2]
private lemma aux2_qexp {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x y : n → ℝ) (s : ℝ) :
    (x + s • y) ⬝ᵥ A *ᵥ (x + s • y) =
      x ⬝ᵥ A *ᵥ x + s * (x ⬝ᵥ A *ᵥ y + y ⬝ᵥ A *ᵥ x) + s ^ 2 * (y ⬝ᵥ A *ᵥ y) := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring
private lemma aux2_qf_smul {n : Type*} [Fintype n] (A : Matrix n n ℝ) (c : ℝ) (v : n → ℝ) :
    (c • v) ⬝ᵥ A *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
private lemma aux2_qf_sub_smul {n : Type*} [Fintype n] (A B : Matrix n n ℝ) (τ : ℝ) (x : n → ℝ) :
    x ⬝ᵥ (A - τ • B) *ᵥ x = x ⬝ᵥ A *ᵥ x - τ * (x ⬝ᵥ B *ᵥ x) := by
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
private def aux2_sph (n : Type*) [Fintype n] : Set (n → ℝ) := {v | v ⬝ᵥ v = 1}
private lemma aux2_sph_compact (n : Type*) [Fintype n] : IsCompact (aux2_sph n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun v hv => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : v i * v i ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
        (Finset.mem_univ i)
    have h2 : v ⬝ᵥ v = 1 := hv
    rw [Real.norm_eq_abs]
    nlinarith [abs_mul_abs_self (v i), abs_nonneg (v i)]
private lemma aux2_sph_ne {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ∈ aux2_sph n) : v ≠ 0 := by
  rintro rfl; simp [aux2_sph] at hv
private lemma aux2_symm_sub_smul {n : Type*} {A B : Matrix n n ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (τ : ℝ) : (A - τ • B).IsSymm := by
  unfold IsSymm at *
  rw [transpose_sub, transpose_smul, hA, hB]
theorem Matrix.sLemma {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (hslater : ∃ x₀, 0 < x₀ ⬝ᵥ B *ᵥ x₀) :
    (∀ x, 0 ≤ x ⬝ᵥ B *ᵥ x → 0 ≤ x ⬝ᵥ A *ᵥ x) ↔ ∃ τ : ℝ, 0 ≤ τ ∧ (A - τ • B).PosSemidef := by
  constructor
  · intro H
    obtain ⟨τ, hτ, h⟩ := aux2_core (fun x => x ⬝ᵥ A *ᵥ x) (fun x => x ⬝ᵥ B *ᵥ x)
      (fun x y => ⟨_, aux2_qexp A x y⟩) (fun x y => ⟨_, aux2_qexp B x y⟩) hslater H
    refine ⟨τ, hτ, PosSemidef.of_dotProduct_mulVec_nonneg
      (aux2_isHermitian (aux2_symm_sub_smul hA hB τ)) fun x => ?_⟩
    simpa [aux2_qf_sub_smul] using h x
  · rintro ⟨τ, hτ, h⟩ x hx
    have := h.dotProduct_mulVec_nonneg x
    simp only [star_trivial, aux2_qf_sub_smul] at this
    nlinarith

-- K6: strict S-lemma (Finsler–Yakubovich), no Slater needed
/-- Strict form (Finsler–Yakubovich). True without Slater (checked on paper, see STATEMENTS.md):
with a Slater point it follows from `sLemma` applied to `A - ε • 1`; without one, `-B` is PSD and
it is Finsler's lemma. -/

theorem solution {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) :
    (∀ x, x ≠ 0 → 0 ≤ x ⬝ᵥ B *ᵥ x → 0 < x ⬝ᵥ A *ᵥ x) ↔ ∃ τ : ℝ, 0 ≤ τ ∧ (A - τ • B).PosDef := by
  classical
  have hcA : Continuous fun x : n → ℝ => x ⬝ᵥ A *ᵥ x :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hcB : Continuous fun x : n → ℝ => x ⬝ᵥ B *ᵥ x :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  constructor
  · intro H
    by_cases hsl : ∃ x₀, 0 < x₀ ⬝ᵥ B *ᵥ x₀
    · -- Slater case: uniform ε on the compact set {‖x‖ = 1, b x ≥ 0}
      let K' : Set (n → ℝ) := aux2_sph n ∩ {x | 0 ≤ x ⬝ᵥ B *ᵥ x}
      have hK' : IsCompact K' :=
        (aux2_sph_compact n).inter_right (isClosed_le continuous_const hcB)
      obtain ⟨m, hm⟩ := hK'.elim_directed_cover
        (fun m : ℕ => {x : n → ℝ | 1 / ((m : ℝ) + 1) < x ⬝ᵥ A *ᵥ x})
        (fun m => isOpen_lt continuous_const hcA)
        (fun x hx => by
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (H x (aux2_sph_ne hx.1) hx.2)
          exact Set.mem_iUnion.2 ⟨m, hm⟩)
        (Monotone.directed_le fun i j hij x hx => by
          refine lt_of_le_of_lt ?_ (show 1 / ((i : ℝ) + 1) < _ from hx)
          gcongr)
      set ε : ℝ := 1 / ((m : ℝ) + 1) with hε
      have hε0 : 0 < ε := by positivity
      have hI : (A - ε • (1 : Matrix n n ℝ)).IsSymm := by
        unfold IsSymm at *; rw [transpose_sub, transpose_smul, transpose_one, hA]
      have hq : ∀ x, 0 ≤ x ⬝ᵥ B *ᵥ x → 0 ≤ x ⬝ᵥ (A - ε • (1 : Matrix n n ℝ)) *ᵥ x := by
        intro x hx
        rw [aux2_qf_sub_smul, one_mulVec]
        by_cases hx0 : x = 0
        · simp [hx0]
        obtain ⟨c, hc, hcx⟩ := aux2_normalize hx0
        have hmem : c • x ∈ K' := ⟨hcx, show 0 ≤ (c • x) ⬝ᵥ B *ᵥ (c • x) by rw [aux2_qf_smul]; positivity⟩
        have h1 := hm hmem
        simp only [Set.mem_ofPred_eq, aux2_qf_smul] at h1
        simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at hcx
        nlinarith
      obtain ⟨τ, hτ, hpsd⟩ := (Matrix.sLemma hI hB hsl).1 hq
      refine ⟨τ, hτ, PosDef.of_dotProduct_mulVec_pos
        (aux2_isHermitian (aux2_symm_sub_smul hA hB τ)) fun x hx => ?_⟩
      have h1 := hpsd.dotProduct_mulVec_nonneg x
      have h2 := aux2_dot_self_pos hx
      simp only [star_trivial, aux2_qf_sub_smul, one_mulVec] at h1 ⊢
      nlinarith
    · -- no Slater: b ≤ 0 everywhere, Finsler by a directed compact cover
      push Not at hsl
      obtain ⟨k, hk⟩ := (aux2_sph_compact n).elim_directed_cover
        (fun k : ℕ => {x : n → ℝ | 0 < x ⬝ᵥ A *ᵥ x - (k : ℝ) * (x ⬝ᵥ B *ᵥ x)})
        (fun k => isOpen_lt continuous_const (hcA.sub (continuous_const.mul hcB)))
        (fun x hx => by
          rcases (hsl x).lt_or_eq with hlt | heq
          · obtain ⟨k, hk⟩ := exists_nat_gt ((-(x ⬝ᵥ A *ᵥ x)) / (-(x ⬝ᵥ B *ᵥ x)))
            refine Set.mem_iUnion.2 ⟨k, ?_⟩
            have hnb : 0 < -(x ⬝ᵥ B *ᵥ x) := by linarith
            rw [div_lt_iff₀ hnb] at hk
            simp only [Set.mem_ofPred_eq]
            linarith
          · refine Set.mem_iUnion.2 ⟨0, ?_⟩
            simp only [Set.mem_ofPred_eq, Nat.cast_zero, zero_mul, sub_zero]
            exact H x (aux2_sph_ne hx) heq.ge)
        (Monotone.directed_le fun i j hij x hx => by
          have hx' : 0 < x ⬝ᵥ A *ᵥ x - (i : ℝ) * (x ⬝ᵥ B *ᵥ x) := hx
          show 0 < x ⬝ᵥ A *ᵥ x - (j : ℝ) * (x ⬝ᵥ B *ᵥ x)
          have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
          nlinarith [hsl x])
      refine ⟨k, by positivity, PosDef.of_dotProduct_mulVec_pos
        (aux2_isHermitian (aux2_symm_sub_smul hA hB _)) fun x hx => ?_⟩
      obtain ⟨c, hc, hcx⟩ := aux2_normalize hx
      have h1 := hk hcx
      simp only [Set.mem_ofPred_eq, aux2_qf_smul] at h1
      simp only [star_trivial, aux2_qf_sub_smul]
      have hc2 : 0 < c ^ 2 := by positivity
      nlinarith
  · rintro ⟨τ, hτ, h⟩ x hx0 hx
    have := h.dotProduct_mulVec_pos hx0
    simp only [star_trivial, aux2_qf_sub_smul] at this
    nlinarith
