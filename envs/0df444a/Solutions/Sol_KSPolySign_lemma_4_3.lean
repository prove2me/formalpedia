-- Prove2me | solution 1 for KSPolySign.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T13:53:33.098254+00:00
-- url     : https://prove2.me/submissions/f20aaccf-eb75-44cb-b657-e4a917b443d8

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
open Matrix
open scoped ComplexOrder

namespace KSPolySign.L43
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

theorem opNorm_le_frob {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    AgnosticTNS.opNorm M ≤ Real.sqrt (∑ j, ∑ l, ‖M j l‖ ^ 2) := by
  unfold AgnosticTNS.opNorm
  apply csSup_le
  · exact ⟨_, ⟨0, by simp, rfl⟩⟩
  rintro r ⟨x, hx, rfl⟩
  simp only [Set.mem_setOf_eq] at hx
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  have h1 : ‖(M *ᵥ x) j‖ ≤ ∑ l, ‖M j l‖ * ‖x l‖ := by
    simp only [mulVec, dotProduct]
    refine (norm_sum_le _ _).trans ?_
    simp [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖M j l‖) (fun l => ‖x l‖)
  have h3 : 0 ≤ ∑ l, ‖M j l‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  calc ‖(M *ᵥ x) j‖ ^ 2 ≤ (∑ l, ‖M j l‖ * ‖x l‖) ^ 2 := by
        gcongr
    _ ≤ (∑ l, ‖M j l‖ ^ 2) * ∑ l, ‖x l‖ ^ 2 := h2
    _ ≤ (∑ l, ‖M j l‖ ^ 2) * 1 := by gcongr
    _ = ∑ l, ‖M j l‖ ^ 2 := mul_one _

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


theorem lemma_4_3 (m n : ℕ) (hm : 1 ≤ m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i, (A i).IsHermitian ∧ (A i).rank = 1) :
    let ε : Fin m → ℝ := fun i => if 0 < (A i).trace.re then 1 else -1
    let B : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((ε i : ℝ) : ℂ) • A i
    ∀ aStar : ℝ, (∀ i j, (B i j j).re ≤ aStar) → (∃ i j, (B i j j).re = aStar) →
    ∀ Daux : ℝ, aStar ≤ Daux → Daux < 2 * aStar →
    let Abar : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((1 / Daux : ℝ) : ℂ) • B i
    let ζ0 : ℝ := AgnosticTNS.opNorm (∑ i, Abar i * Abar i)
    let ξ : ℝ := 1 / 10 ^ 8
    let δ : ℝ := ξ / ((m : ℝ) * n)
    ∀ Atil : Fin m → Matrix (Fin n) (Fin n) ℂ, (∀ i, Real.sqrt (∑ j, ∑ l, ‖(Atil i - Abar i) j l‖ ^ 2) ≤ δ) →
      let ζt : ℝ := AgnosticTNS.opNorm (∑ i, Atil i * Atil i)
      let Cstar : ℝ := 3.4813833
      (|ζt - ζ0| ≤ 3 * ξ ∧ Real.sqrt ζt ≤ (1 + 6 * ξ) * Real.sqrt ζ0) ∧
        ∀ τ : Fin m → ℝ, (∀ i, τ i = 1 ∨ τ i = -1) →
          AgnosticTNS.opNorm (∑ i, ((τ i : ℝ) : ℂ) • Atil i) ≤ Cstar * Real.sqrt ζt →
          AgnosticTNS.opNorm (∑ i, ((ε i * τ i : ℝ) : ℂ) • A i) <
            3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i)) := by
  intro ε B aStar haS1 haS2 Daux hD1 hD2 Abar ζ0 ξ δ Atil hAtil ζt Cstar
  have hζ0 : ζ0 = ‖∑ i, Abar i * Abar i‖ := opNorm_eq_l2 _
  have hζt : ζt = ‖∑ i, Atil i * Atil i‖ := opNorm_eq_l2 _
  simp only [opNorm_eq_l2]
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
  have hε0 : ∀ i, ε i ≠ 0 := by
    intro i h; have := hε2 i; rw [h] at this; simp at this
  -- B PSD
  have hBPSD : ∀ i, (B i).PosSemidef := by
    intro i
    have hAi : A i = (((1 / t i : ℝ)) : ℂ) • (A i * A i) := by
      rw [(hR i).2.2, smul_smul]
      push_cast
      rw [div_mul_cancel₀ _ (by exact_mod_cast ht0 i)]
      simp
    have heq : B i = (((1 / |t i|) : ℝ) : ℂ) • ((A i)ᴴ * A i) := by
      simp only [B]
      rw [(hA i).1.eq]
      conv_lhs => rw [hAi]
      rw [smul_smul]
      congr 1
      have key : ε i * (1 / t i) = 1 / |t i| := by
        have := hε0 i
        have := ht0 i
        rw [← hεt i]
        field_simp
        linear_combination hε2 i
      exact_mod_cast key
    rw [heq]
    apply (posSemidef_conjTranspose_mul_self _).smul
    have : (0:ℝ) ≤ 1 / |t i| := by positivity
    exact_mod_cast this
  have hBrank : ∀ i, (B i).rank = 1 := by
    intro i
    simp only [B]
    rw [rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero
      (by exact_mod_cast hε0 i))]
    exact (hA i).2
  have hBtr : ∀ i, (B i).trace.re = |t i| := by
    intro i
    simp only [B, trace_smul, smul_eq_mul]
    rw [(hR i).2.1]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    exact hεt i
  -- aStar > 0
  let i0 : Fin m := ⟨0, hm⟩
  have hpos_entry : ∃ j, 0 < (B i0 j j).re := by
    have h := hBtr i0
    have hp : 0 < |t i0| := abs_pos.mpr (ht0 i0)
    rw [← h, trace, Complex.re_sum] at hp
    by_contra hcon
    push_neg at hcon
    have : ∑ j, ((B i0).diag j).re ≤ 0 := Finset.sum_nonpos fun j _ => hcon j
    linarith
  obtain ⟨j0, hj0⟩ := hpos_entry
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact j0.elim0
    · exact h
  have haS : 0 < aStar := lt_of_lt_of_le hj0 (haS1 i0 j0)
  have hDpos : 0 < Daux := lt_of_lt_of_le haS hD1
  -- Abar
  have hAbarPSD : ∀ i, (Abar i).PosSemidef := by
    intro i
    apply (hBPSD i).smul
    have : (0:ℝ) ≤ 1 / Daux := by positivity
    exact_mod_cast this
  have hAbarRank : ∀ i, (Abar i).rank = 1 := by
    intro i
    simp only [Abar]
    rw [rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero
      (by exact_mod_cast (one_div_pos.mpr hDpos).ne'))]
    exact hBrank i
  have hAbar_norm : ∀ i, ‖Abar i‖ ≤ n := by
    intro i
    rw [psd_rank_one_norm (hAbarPSD i) (hAbarRank i).le]
    simp only [Abar, trace_smul, smul_eq_mul]
    rw [Complex.re_ofReal_mul]
    have : (B i).trace.re ≤ n * aStar := by
      rw [trace, Complex.re_sum]
      calc ∑ j, ((B i).diag j).re ≤ ∑ _j : Fin n, aStar :=
            Finset.sum_le_sum fun j _ => haS1 i j
        _ = n * aStar := by simp
    calc 1 / Daux * (B i).trace.re ≤ 1 / Daux * (n * aStar) := by gcongr
      _ ≤ 1 / Daux * (n * Daux) := by gcongr
      _ = n := by field_simp
  -- errors
  set E : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => Atil i - Abar i with hE_def
  have hE : ∀ i, ‖E i‖ ≤ δ := fun i => by
    rw [← opNorm_eq_l2]; exact (opNorm_le_frob _).trans (hAtil i)
  have hAtil_eq : ∀ i, Atil i = Abar i + E i := fun i => by simp [hE_def]
  have hξ : ξ = 1 / 10 ^ 8 := rfl
  have hδ : δ = ξ / ((m : ℝ) * n) := rfl
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hδ0 : 0 ≤ δ := by rw [hδ, hξ]; positivity
  have hsq_diff : ∀ i, ‖Atil i * Atil i - Abar i * Abar i‖ ≤ 2 * n * δ + δ ^ 2 := by
    intro i
    have : Atil i * Atil i - Abar i * Abar i = Abar i * E i + E i * Abar i + E i * E i := by
      rw [hAtil_eq i]; noncomm_ring
    rw [this]
    have h1 := norm_mul_le (Abar i) (E i)
    have h2 := norm_mul_le (E i) (Abar i)
    have h3 := norm_mul_le (E i) (E i)
    have := norm_add₃_le (a := Abar i * E i) (b := E i * Abar i) (c := E i * E i)
    have hEn := norm_nonneg (E i)
    have hAn := norm_nonneg (Abar i)
    nlinarith [hE i, hAbar_norm i, mul_le_mul (hAbar_norm i) (hE i) hEn (by positivity),
      mul_le_mul (hE i) (hE i) hEn hδ0]
  have hdiff : ‖∑ i, Atil i * Atil i - ∑ i, Abar i * Abar i‖ ≤ 3 * ξ := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖Atil i * Atil i - Abar i * Abar i‖ ≤ ∑ _i : Fin m, (2 * n * δ + δ ^ 2) :=
          Finset.sum_le_sum fun i _ => hsq_diff i
      _ = m * (2 * n * δ + δ ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 3 * ξ := by
          rw [hδ, hξ]
          have hm0 : (0:ℝ) < m := by linarith
          have hn0 : (0:ℝ) < n := by linarith
          field_simp
          nlinarith [mul_le_mul hmR hnR (by norm_num) (by linarith),
            mul_pos hm0 hn0, mul_pos (mul_pos hm0 hn0) hn0]
  -- ζ0 > 1/4
  obtain ⟨i1, j1, hij⟩ := haS2
  have hnn : ∀ j, (Abar j * Abar j).PosSemidef := by
    intro j
    have := posSemidef_conjTranspose_mul_self (Abar j)
    rwa [(hAbarPSD j).isHermitian.eq] at this
  have hAbar1 : 1 / 2 < ‖Abar i1‖ := by
    refine lt_of_lt_of_le ?_ (norm_entry_le (Abar i1) j1)
    refine lt_of_lt_of_le ?_ (Complex.re_le_norm _)
    have : (Abar i1 j1 j1).re = 1 / Daux * aStar := by
      simp only [Abar, Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]; rw [hij]
    rw [this, div_mul_eq_mul_div, one_mul, lt_div_iff₀ hDpos]
    linarith
  have hζ0low : 1 / 4 < ζ0 := by
    rw [hζ0]
    have hmono : ‖Abar i1 * Abar i1‖ ≤ ‖∑ i, Abar i * Abar i‖ := by
      open scoped MatrixOrder in
      exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (hnn i1).nonneg
        (Finset.single_le_sum (f := fun j => Abar j * Abar j) (fun j _ => (hnn j).nonneg)
          (Finset.mem_univ i1))
    rw [herm_norm_mul_self (hAbarPSD i1).isHermitian] at hmono
    nlinarith [hAbar1]
  have hζ_diff : |ζt - ζ0| ≤ 3 * ξ := by
    rw [hζt, hζ0]; exact (abs_norm_sub_norm_le _ _).trans hdiff
  have hξ0 : 0 < ξ := by rw [hξ]; norm_num
  have hξ1 : ξ ≤ 1 / 10 ^ 8 := le_of_eq hξ
  have hsqrt : Real.sqrt ζt ≤ (1 + 6 * ξ) * Real.sqrt ζ0 := by
    have hz0 : 0 ≤ ζ0 := by linarith
    have : ζt ≤ ((1 + 6 * ξ) * Real.sqrt ζ0) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hz0]
      have := (abs_le.mp hζ_diff).2
      nlinarith [mul_pos hξ0 (sub_pos.mpr hζ0low), sq_nonneg ξ, mul_nonneg (sq_nonneg ξ) hz0]
    calc Real.sqrt ζt ≤ Real.sqrt (((1 + 6 * ξ) * Real.sqrt ζ0) ^ 2) := Real.sqrt_le_sqrt this
      _ = (1 + 6 * ξ) * Real.sqrt ζ0 := Real.sqrt_sq (by positivity)
  refine ⟨⟨hζ_diff, hsqrt⟩, ?_⟩
  intro τ hτ hbound
  have hτn : ∀ i, ‖((τ i : ℝ) : ℂ)‖ = 1 := by
    intro i; rcases hτ i with h | h <;> simp [h]
  have hsumE : ‖∑ i, ((τ i : ℝ) : ℂ) • E i‖ ≤ ξ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖((τ i : ℝ) : ℂ) • E i‖ ≤ ∑ _i : Fin m, δ :=
          Finset.sum_le_sum fun i _ => by rw [norm_smul, hτn i, one_mul]; exact hE i
      _ = m * δ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ξ := by
          rw [hδ]
          have hm0 : (0:ℝ) < m := by linarith
          have hn0 : (0:ℝ) < n := by linarith
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hnR (le_of_lt (mul_pos hm0 hξ0))]
  have hsplit : ∑ i, ((τ i : ℝ) : ℂ) • Abar i =
      ∑ i, ((τ i : ℝ) : ℂ) • Atil i - ∑ i, ((τ i : ℝ) : ℂ) • E i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hAtil_eq i, smul_add]; abel
  have hζ0sqrt : 1 / 2 < Real.sqrt ζ0 := by
    rw [show (1:ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hζ0low
  have hkey : ‖∑ i, ((τ i : ℝ) : ℂ) • Abar i‖ < 3.4814 * Real.sqrt ζ0 := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans_lt ?_
    have hC : Cstar = 3.4813833 := rfl
    have h1 : Cstar * Real.sqrt ζt ≤ Cstar * ((1 + 6 * ξ) * Real.sqrt ζ0) :=
      mul_le_mul_of_nonneg_left hsqrt (by rw [hC]; norm_num)
    have hs0 := Real.sqrt_nonneg ζ0
    rw [hC] at h1 hbound
    rw [hξ] at h1 hsumE
    nlinarith
  have hDsum : ∑ i, ((ε i * τ i : ℝ) : ℂ) • A i = (Daux : ℂ) • ∑ i, ((τ i : ℝ) : ℂ) • Abar i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Abar, B, smul_smul]
    congr 1
    have hD : (Daux : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
    push_cast
    field_simp
  have hDsq : ∑ i, A i * A i = ((Daux ^ 2 : ℝ) : ℂ) • ∑ i, Abar i * Abar i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Abar, B, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hD : (Daux : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have h1 : (ε i : ℂ) * ε i = 1 := by exact_mod_cast hε2 i
    have : ((Daux ^ 2 : ℝ) : ℂ) * ((((1 / Daux : ℝ)) : ℂ) * (ε i : ℂ) * ((((1 / Daux : ℝ)) : ℂ) *
        (ε i : ℂ))) = 1 := by
      push_cast
      field_simp
      linear_combination h1
    rw [this, one_smul]
  rw [hDsum, hDsq, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hDpos, abs_of_nonneg (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_sq hDpos.le, ← hζ0]
  have := mul_lt_mul_of_pos_left hkey hDpos
  linarith

end L2

end KSPolySign.L43

open Matrix
open scoped ComplexOrder
open KSPolySign

theorem solution (m n : ℕ) (hm : 1 ≤ m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i, (A i).IsHermitian ∧ (A i).rank = 1) :
    let ε : Fin m → ℝ := fun i => if 0 < (A i).trace.re then 1 else -1
    let B : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((ε i : ℝ) : ℂ) • A i
    ∀ aStar : ℝ, (∀ i j, (B i j j).re ≤ aStar) → (∃ i j, (B i j j).re = aStar) →
    ∀ Daux : ℝ, aStar ≤ Daux → Daux < 2 * aStar →
    let Abar : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((1 / Daux : ℝ) : ℂ) • B i
    let ζ0 : ℝ := AgnosticTNS.opNorm (∑ i, Abar i * Abar i)
    let ξ : ℝ := 1 / 10 ^ 8
    let δ : ℝ := ξ / ((m : ℝ) * n)
    ∀ Atil : Fin m → Matrix (Fin n) (Fin n) ℂ, (∀ i, Real.sqrt (∑ j, ∑ l, ‖(Atil i - Abar i) j l‖ ^ 2) ≤ δ) →
      let ζt : ℝ := AgnosticTNS.opNorm (∑ i, Atil i * Atil i)
      let Cstar : ℝ := 3.4813833
      (|ζt - ζ0| ≤ 3 * ξ ∧ Real.sqrt ζt ≤ (1 + 6 * ξ) * Real.sqrt ζ0) ∧
        ∀ τ : Fin m → ℝ, (∀ i, τ i = 1 ∨ τ i = -1) →
          AgnosticTNS.opNorm (∑ i, ((τ i : ℝ) : ℂ) • Atil i) ≤ Cstar * Real.sqrt ζt →
          AgnosticTNS.opNorm (∑ i, ((ε i * τ i : ℝ) : ℂ) • A i) <
            3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i)) := by
  apply KSPolySign.L43.lemma_4_3 <;> assumption
