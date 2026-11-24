-- Prove2me | solution 1 for KSPolySign.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T13:47:48.731192+00:00
-- url     : https://prove2.me/submissions/2e5e71a5-96cc-421d-9f6a-d979460d1ea3

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
open Matrix
open scoped ComplexOrder

namespace KSPolySign.L31
open KSPolySign

theorem exists_vecMulVec_of_rank_le_one {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (h : C.rank ≤ 1) :
    ∃ a b : Fin n → ℂ, C = vecMulVec a b := by
  classical
  have h' : Module.finrank ℂ (LinearMap.range C.mulVecLin) ≤ 1 := h
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h'
  have hcol : ∀ j : Fin n, ∃ c : ℂ, c • (v : Fin n → ℂ) = C *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨c, hc⟩ := hv ⟨C *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  choose c hc using hcol
  refine ⟨v, c, ?_⟩
  ext i j
  have := congrFun (hc j) i
  simp [mulVec_single] at this
  simp [vecMulVec_apply, ← this, mul_comm]

theorem sandwich_of_rank_le_one {n : ℕ} (C D : Matrix (Fin n) (Fin n) ℂ) (h : C.rank ≤ 1) :
    C * D * C = (C * D).trace • C := by
  obtain ⟨a, b, rfl⟩ := exists_vecMulVec_of_rank_le_one C h
  ext i j
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, trace, diag, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

section L2
open scoped Matrix.Norms.L2Operator

theorem opNorm_eq_l2 {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    AgnosticTNS.opNorm M = ‖M‖ := by
  rw [Matrix.cstar_norm_def, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  unfold AgnosticTNS.opNorm
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq]; exact Real.sqrt_le_one.mpr hx
    · rw [EuclideanSpace.norm_eq]; simp
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.ofLp, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq] at hx
      simpa using (Real.sqrt_le_one (x := ∑ i, ‖x i‖ ^ 2)).mp hx
    · rw [EuclideanSpace.norm_eq]; simp

theorem herm_norm_mul_self {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ‖A * A‖ = ‖A‖ * ‖A‖ := by
  have := l2_opNorm_conjTranspose_mul_self A
  rwa [hA.eq] at this

theorem norm_entry_le {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ‖S j j‖ ≤ ‖S‖ := by
  rw [Matrix.cstar_norm_def]
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  have h1 : S j j = inner ℂ e (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) S e) := by
    simp [e, EuclideanSpace.inner_single_left, mulVec_single]
  rw [h1]
  calc ‖inner ℂ e (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) S e)‖
      ≤ ‖e‖ * ‖toEuclideanCLM (n := Fin n) (𝕜 := ℂ) S e‖ := norm_inner_le_norm _ _
    _ ≤ ‖e‖ * (‖toEuclideanCLM (n := Fin n) (𝕜 := ℂ) S‖ * ‖e‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [he]; ring

theorem trace_re_le {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) : S.trace.re ≤ n * ‖S‖ := by
  rw [trace, Complex.re_sum]
  calc ∑ j, (S.diag j).re ≤ ∑ _j : Fin n, ‖S‖ :=
        Finset.sum_le_sum fun j _ => (Complex.re_le_norm _).trans (norm_entry_le S j)
    _ = n * ‖S‖ := by simp

/-- PSD rank ≤ 1: norm equals trace. -/
theorem psd_rank_one_norm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hr : A.rank ≤ 1) : ‖A‖ = A.trace.re := by
  have hAA : A * A = A.trace • A := by simpa using sandwich_of_rank_le_one A 1 hr
  have h0 := hA.trace_nonneg
  have htr : A.trace = (A.trace.re : ℂ) := by
    rw [Complex.nonneg_iff] at h0; apply Complex.ext <;> simp [h0.2.symm]
  have hn := herm_norm_mul_self hA.isHermitian
  rw [hAA, norm_smul, htr, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Complex.nonneg_iff.mp h0).1] at hn
  by_cases hz : ‖A‖ = 0
  · have : A = 0 := norm_eq_zero.mp hz
    subst this; simp
  · have := mul_right_cancel₀ hz hn
    exact this.symm

theorem herm_rank_one {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hr : A.rank = 1) :
    A.trace.re ≠ 0 ∧ A.trace = (A.trace.re : ℂ) ∧ A * A = ((A.trace.re : ℝ) : ℂ) • A := by
  have hAA : A * A = A.trace • A := by simpa using sandwich_of_rank_le_one A 1 hr.le
  have hreal : A.trace = (A.trace.re : ℂ) := by
    have h := trace_conjTranspose A
    rw [hA.eq] at h
    apply Complex.ext
    · simp
    · have := congrArg Complex.im h
      simp at this; simp; linarith
  refine ⟨?_, hreal, by rw [← hreal]; exact hAA⟩
  intro h0
  have : A * A = 0 := by rw [hAA, hreal, h0]; simp
  have hA0 : A = 0 := by
    have h2 : Aᴴ * A = 0 := by rw [hA.eq]; exact this
    exact conjTranspose_mul_self_eq_zero.mp h2
  rw [hA0, rank_zero] at hr
  exact zero_ne_one hr

theorem lemma_3_1 (m n : ℕ) (hm : 1 ≤ m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i, (A i).IsHermitian ∧ (A i).rank = 1) :
    let L : ℝ := ∑ i, |(A i).trace.re|
    let ε : Fin m → ℝ := fun i => if 0 < (A i).trace.re then 1 else -1
    let Abar : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((ε i / L : ℝ) : ℂ) • A i
    let ζ : ℝ := AgnosticTNS.opNorm (∑ i, Abar i * Abar i)
    ((∀ i, (Abar i).PosSemidef ∧ (Abar i).rank = 1) ∧ (∑ i, (Abar i).trace) = 1 ∧
        1 / ((m : ℝ) * n) ≤ ζ ∧ ζ ≤ 1 ∧ ∀ i, AgnosticTNS.opNorm (Abar i) ≤ Real.sqrt ζ) ∧
      (∀ τ : Fin m → ℝ, (∀ i, τ i = 1 ∨ τ i = -1) →
          AgnosticTNS.opNorm (∑ i, ((ε i * τ i : ℝ) : ℂ) • A i) =
            L * AgnosticTNS.opNorm (∑ i, ((τ i : ℝ) : ℂ) • Abar i)) ∧
      AgnosticTNS.opNorm (∑ i, A i * A i) = L ^ 2 * ζ := by
  intro L ε Abar ζ
  simp only [opNorm_eq_l2] at *
  set t : Fin m → ℝ := fun i => (A i).trace.re with ht_def
  have hR := fun i => herm_rank_one (hA i).1 (hA i).2
  have ht0 : ∀ i, t i ≠ 0 := fun i => (hR i).1
  have hεt : ∀ i, ε i * t i = |t i| := by
    intro i
    simp only [ε, ht_def]
    split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) (ht0 i)), neg_one_mul]
  have hε2 : ∀ i, ε i * ε i = 1 := by
    intro i; simp only [ε]; split_ifs <;> norm_num
  have hLpos : 0 < L := by
    have : 0 < |t ⟨0, hm⟩| := abs_pos.mpr (ht0 _)
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => |t i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ _))
  -- tbar
  set tb : Fin m → ℝ := fun i => |t i| / L with htb_def
  have htb_nonneg : ∀ i, 0 ≤ tb i := fun i => div_nonneg (abs_nonneg _) hLpos.le
  have htb_sum : ∑ i, tb i = 1 := by
    simp only [htb_def, ← Finset.sum_div]; exact div_self hLpos.ne'
  have htrAbar : ∀ i, (Abar i).trace = ((tb i : ℝ) : ℂ) := by
    intro i
    simp only [Abar, trace_smul, smul_eq_mul]
    rw [(hR i).2.1]
    push_cast
    rw [htb_def]; simp only
    rw [← hεt i]; push_cast; ring
  have hAbarPSD : ∀ i, (Abar i).PosSemidef := by
    intro i
    have hAi : A i = (((1 / t i : ℝ)) : ℂ) • (A i * A i) := by
      rw [(hR i).2.2, smul_smul]
      push_cast
      rw [div_mul_cancel₀ _ (by exact_mod_cast ht0 i)]
      simp
    have heq : Abar i = (((1 / (L * |t i|)) : ℝ) : ℂ) • ((A i)ᴴ * A i) := by
      simp only [Abar]
      rw [(hA i).1.eq]
      conv_lhs => rw [hAi]
      rw [smul_smul]
      congr 1
      have hε0 : ε i ≠ 0 := by intro h; have := hε2 i; rw [h] at this; simp at this
      have key : ε i / L * (1 / t i) = 1 / (L * |t i|) := by
        rw [← hεt i]
        field_simp
        linear_combination (t i)⁻¹ * hε2 i
      exact_mod_cast key
    rw [heq]
    apply (posSemidef_conjTranspose_mul_self _).smul
    have : (0:ℝ) ≤ 1 / (L * |t i|) := by positivity
    exact_mod_cast this
  have hεL0 : ∀ i, (((ε i / L : ℝ)) : ℂ) ≠ 0 := by
    intro i
    have : ε i ≠ 0 := by intro h; have := hε2 i; rw [h] at this; simp at this
    exact_mod_cast div_ne_zero this hLpos.ne'
  have hAbarRank : ∀ i, (Abar i).rank = 1 := by
    intro i
    simp only [Abar]
    rw [rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (hεL0 i))]
    exact (hA i).2
  have hnormAbar : ∀ i, ‖Abar i‖ = tb i := by
    intro i
    rw [psd_rank_one_norm (hAbarPSD i) (hAbarRank i).le, htrAbar i]; simp
  have hsqAbar : ∀ i, Abar i * Abar i = ((tb i : ℝ) : ℂ) • Abar i := by
    intro i
    have := sandwich_of_rank_le_one (Abar i) 1 (hAbarRank i).le
    simp only [Matrix.mul_one] at this
    rw [this, htrAbar i]
  have hζ : ζ = ‖∑ i, Abar i * Abar i‖ := opNorm_eq_l2 _
  have hS : ∑ i, Abar i * Abar i = ∑ i, ((tb i : ℝ) : ℂ) • Abar i :=
    Finset.sum_congr rfl fun i _ => hsqAbar i
  have htb_le : ∀ i, tb i ≤ 1 := fun i => htb_sum ▸
    Finset.single_le_sum (f := tb) (fun j _ => htb_nonneg j) (Finset.mem_univ i)
  have hζle : ‖∑ i, Abar i * Abar i‖ ≤ 1 := by
    rw [hS]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖((tb i : ℝ) : ℂ) • Abar i‖ = ∑ i, tb i * tb i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, hnormAbar i, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (htb_nonneg i)]
      _ ≤ ∑ i, tb i * 1 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (htb_le i) (htb_nonneg i)
      _ = 1 := by simp [htb_sum]
  have htrS : (∑ i, Abar i * Abar i).trace.re = ∑ i, tb i ^ 2 := by
    rw [hS, trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [trace_smul, htrAbar i, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have hlow : 1 ≤ (m : ℝ) * n * ‖∑ i, Abar i * Abar i‖ := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := tb)
    rw [htb_sum, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := trace_re_le (∑ i, Abar i * Abar i)
    rw [htrS] at h2
    have hm0 : (0:ℝ) ≤ m := by positivity
    calc (1:ℝ) = 1 ^ 2 := by norm_num
      _ ≤ m * ∑ i, tb i ^ 2 := h1
      _ ≤ m * (n * ‖∑ i, Abar i * Abar i‖) := mul_le_mul_of_nonneg_left h2 hm0
      _ = _ := by ring
  have hmn : (0:ℝ) < (m : ℝ) * n := by
    rcases (show (0:ℝ) ≤ m * n by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h] at hlow; simp at hlow; linarith
  refine ⟨⟨fun i => ⟨hAbarPSD i, hAbarRank i⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [htrAbar]; exact_mod_cast htb_sum
  · rw [hζ, div_le_iff₀ hmn]; linarith
  · rw [hζ]; exact hζle
  · intro i
    rw [hnormAbar i, hζ]
    apply Real.le_sqrt_of_sq_le
    rw [sq, ← hnormAbar i, ← herm_norm_mul_self (hAbarPSD i).isHermitian]
    have hnn : ∀ j, (Abar j * Abar j).PosSemidef := by
      intro j
      have := posSemidef_conjTranspose_mul_self (Abar j)
      rwa [(hAbarPSD j).isHermitian.eq] at this
    open scoped MatrixOrder in
    exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (hnn i).nonneg
      (Finset.single_le_sum (f := fun j => Abar j * Abar j) (fun j _ => (hnn j).nonneg)
        (Finset.mem_univ i))
  · intro τ _
    have : ∑ i, ((ε i * τ i : ℝ) : ℂ) • A i = (L : ℂ) • ∑ i, ((τ i : ℝ) : ℂ) • Abar i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Abar, smul_smul]
      congr 1
      have hL : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
      push_cast
      field_simp
    rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
  · rw [hζ]
    have : ∑ i, A i * A i = ((L ^ 2 : ℝ) : ℂ) • ∑ i, Abar i * Abar i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Abar, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hL : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
      have h1 : (ε i : ℂ) * ε i = 1 := by exact_mod_cast hε2 i
      have : ((L ^ 2 : ℝ) : ℂ) * ((((ε i / L : ℝ)) : ℂ) * (((ε i / L : ℝ)) : ℂ)) = 1 := by
        push_cast
        field_simp
        linear_combination h1
      rw [this, one_smul]
    rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end L2

end KSPolySign.L31

open Matrix
open scoped ComplexOrder
open KSPolySign

theorem solution (m n : ℕ) (hm : 1 ≤ m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i, (A i).IsHermitian ∧ (A i).rank = 1) :
    let L : ℝ := ∑ i, |(A i).trace.re|
    let ε : Fin m → ℝ := fun i => if 0 < (A i).trace.re then 1 else -1
    let Abar : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((ε i / L : ℝ) : ℂ) • A i
    let ζ : ℝ := AgnosticTNS.opNorm (∑ i, Abar i * Abar i)
    ((∀ i, (Abar i).PosSemidef ∧ (Abar i).rank = 1) ∧ (∑ i, (Abar i).trace) = 1 ∧
        1 / ((m : ℝ) * n) ≤ ζ ∧ ζ ≤ 1 ∧ ∀ i, AgnosticTNS.opNorm (Abar i) ≤ Real.sqrt ζ) ∧
      (∀ τ : Fin m → ℝ, (∀ i, τ i = 1 ∨ τ i = -1) →
          AgnosticTNS.opNorm (∑ i, ((ε i * τ i : ℝ) : ℂ) • A i) =
            L * AgnosticTNS.opNorm (∑ i, ((τ i : ℝ) : ℂ) • Abar i)) ∧
      AgnosticTNS.opNorm (∑ i, A i * A i) = L ^ 2 * ζ := by
  apply KSPolySign.L31.lemma_3_1 <;> assumption
