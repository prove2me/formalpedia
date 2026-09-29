-- Prove2me | solution 1 for LogRegretOCO.ONS.elliptical_potential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:38:29.200865+00:00
-- url     : https://prove2.me/submissions/f7fbe9e0-00fd-4c2a-ab94-821a3e2f9be5

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic

open Matrix
open LogRegretOCO.ONS

private theorem rk1 {n : ℕ} (z v : Fin n → ℝ) :
    (1 - Matrix.vecMulVec z v).det = 1 - v ⬝ᵥ z := by
  have h : (1 + Matrix.vecMulVec (-z) v).det = 1 + v ⬝ᵥ (-z) := by
    rw [Matrix.vecMulVec_eq (Fin 1)]
    exact Matrix.det_one_add_replicateCol_mul_replicateRow (-z) v
  have hneg : Matrix.vecMulVec (-z) v = -Matrix.vecMulVec z v := by
    ext i j; simp [Matrix.vecMulVec_apply]
  rw [hneg, ← sub_eq_add_neg] at h
  rw [h, dotProduct_neg]
  ring

/-- The matrix determinant lemma, in the rank-one downdate form used below. -/
private theorem det_downdate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (w : Fin n → ℝ) :
    (A - Matrix.vecMulVec w w).det = A.det * (1 - w ⬝ᵥ (A⁻¹ *ᵥ w)) := by
  have h1 : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (v z : Fin n → ℝ),
      B * Matrix.vecMulVec v z = Matrix.vecMulVec (B *ᵥ v) z := by
    intro B v z
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : A *ᵥ (A⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  have hz : A * Matrix.vecMulVec (A⁻¹ *ᵥ w) w = Matrix.vecMulVec w w := by
    rw [h1, h2]
  have hfac : A - Matrix.vecMulVec w w = A * (1 - Matrix.vecMulVec (A⁻¹ *ᵥ w) w) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hz]
  rw [hfac, Matrix.det_mul, rk1]

private noncomputable def VV {n : ℕ} (ε : ℝ) (u : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ τ ∈ Finset.Icc 1 t, Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ))
    + ε • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Lemma 11 of Hazan–Agarwal–Kale: the elliptical potential bound. -/
private theorem ep_core {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (r ε : ℝ) (T : ℕ)
    (hr : 0 < r) (hε : 0 < ε) (hu : ∀ t ∈ Finset.Icc 1 T, ‖u t‖ ≤ r) :
    ∑ t ∈ Finset.Icc 1 T,
        (WithLp.ofLp (u t) ⬝ᵥ ((VV ε u t)⁻¹ *ᵥ WithLp.ofLp (u t)))
      ≤ n * Real.log (r ^ 2 * T / ε + 1) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  -- positive definiteness of every `V t`
  have hpsd : ∀ v : Fin n → ℝ, (Matrix.vecMulVec v v).PosSemidef := fun v => by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  have hsumpsd : ∀ t : ℕ, (∑ τ ∈ Finset.Icc 1 t,
      Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ))).PosSemidef :=
    fun t => Matrix.posSemidef_sum _ (fun i _ => hpsd _)
  have hunfold : ∀ t : ℕ, VV ε u t = (∑ τ ∈ Finset.Icc 1 t,
      Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ))) + ε • 1 := fun t => rfl
  have hPD : ∀ t : ℕ, (VV ε u t).PosDef := by
    intro t
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · rw [hunfold t]
      exact Matrix.IsHermitian.add (hsumpsd t).1 (by simp [Matrix.IsHermitian])
    · intro x hx
      have h1 : (0:ℝ) ≤ star x ⬝ᵥ ((∑ τ ∈ Finset.Icc 1 t,
          Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ))) *ᵥ x) :=
        (hsumpsd t).dotProduct_mulVec_nonneg x
      have h2 : (0:ℝ) < star x ⬝ᵥ ((ε • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
        have hxx : (0:ℝ) < star x ⬝ᵥ x := by
          simp only [star_trivial]
          rcases Function.ne_iff.mp hx with ⟨i, hi⟩
          exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
            ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
        positivity
      rw [hunfold t, Matrix.add_mulVec, dotProduct_add]
      linarith
  have hdet : ∀ t : ℕ, 0 < (VV ε u t).det := fun t => (hPD t).det_pos
  have hunit : ∀ t : ℕ, IsUnit (VV ε u t).det := fun t =>
    isUnit_iff_ne_zero.mpr (hdet t).ne'
  -- the recursion `V (t+1) = V t + u_{t+1} u_{t+1}ᵀ`
  have hrec : ∀ t : ℕ, VV ε u (t + 1) = VV ε u t
      + Matrix.vecMulVec (WithLp.ofLp (u (t + 1))) (WithLp.ofLp (u (t + 1))) := by
    intro t
    rw [hunfold, hunfold, Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1)]
    abel
  -- the one-step potential inequality
  set L : ℕ → ℝ := fun t => Real.log ((VV ε u t).det) with hL
  have hstep : ∀ s : ℕ,
      (WithLp.ofLp (u (s + 1)) ⬝ᵥ ((VV ε u (s + 1))⁻¹ *ᵥ WithLp.ofLp (u (s + 1))))
        ≤ L (s + 1) - L s := by
    intro s
    set w : Fin n → ℝ := WithLp.ofLp (u (s + 1)) with hw
    set A : Matrix (Fin n) (Fin n) ℝ := VV ε u (s + 1) with hA
    set b : ℝ := w ⬝ᵥ (A⁻¹ *ᵥ w) with hb
    have hVs : VV ε u s = A - Matrix.vecMulVec w w := by
      rw [hA, hrec s, ← hw]
      abel
    have hdl : (VV ε u s).det = A.det * (1 - b) := by
      rw [hVs, hb]
      exact det_downdate A (hA ▸ hunit (s + 1)) w
    -- `hdl : (VV ε u s).det = A.det * (1 - b)`
    have hAne : A.det ≠ 0 := by rw [hA]; exact (hdet (s + 1)).ne'
    have hkey : b = 1 - (VV ε u s).det / A.det := by
      rw [hdl]
      field_simp
      ring
    have hx : 0 < A.det / (VV ε u s).det := by
      have := hdet (s + 1); have := hdet s; rw [← hA] at *; positivity
    have hlog : 1 - ((VV ε u s).det / A.det) ≤ Real.log (A.det / (VV ε u s).det) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
      rw [Real.log_inv, inv_div] at h
      linarith
    have hLdiff : Real.log (A.det / (VV ε u s).det) = L (s + 1) - L s := by
      rw [hL]
      simp only
      rw [Real.log_div (hdet (s + 1)).ne' (hdet s).ne']
    rw [hkey, ← hLdiff]
    exact hlog
  -- telescoping
  have hsum : ∀ N : ℕ, ∑ t ∈ Finset.Icc 1 N,
      (WithLp.ofLp (u t) ⬝ᵥ ((VV ε u t)⁻¹ *ᵥ WithLp.ofLp (u t))) ≤ L N - L 0 := by
    intro N
    induction N with
    | zero => simp
    | succ s ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ s + 1)]
      have := hstep s
      linarith
  refine le_trans (hsum T) ?_
  -- the base value `L 0 = n log ε`
  have hV0 : VV ε u 0 = ε • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hunfold]; simp
  have hL0 : L 0 = n * Real.log ε := by
    rw [hL]
    simp only [hV0, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [Real.log_pow]
  -- the trace bound
  have htr : (VV ε u T).trace = n * ε + ∑ t ∈ Finset.Icc 1 T, ‖u t‖ ^ 2 := by
    rw [hunfold, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Matrix.trace_sum]
    have : ∀ t : ℕ, (Matrix.vecMulVec (WithLp.ofLp (u t)) (WithLp.ofLp (u t))).trace
        = ‖u t‖ ^ 2 := by
      intro t
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.vecMulVec_apply]
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
      ring
    rw [Finset.sum_congr rfl fun t _ => this t]
    simp [Fintype.card_fin]
    ring
  have hnormsq : ∑ t ∈ Finset.Icc 1 T, ‖u t‖ ^ 2 ≤ T * r ^ 2 := by
    calc ∑ t ∈ Finset.Icc 1 T, ‖u t‖ ^ 2
        ≤ ∑ _t ∈ Finset.Icc 1 T, r ^ 2 := by
          refine Finset.sum_le_sum fun t ht => ?_
          have h0 := norm_nonneg (u t)
          have h1 := hu t ht
          nlinarith
      _ = T * r ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc]
          simp
  -- eigenvalues of `V T`
  have hPDT := hPD T
  have hherm : (VV ε u T).IsHermitian := hPDT.1
  have hev : ∀ i, 0 < hherm.eigenvalues i := fun i => hPDT.eigenvalues_pos i
  have htrev : (VV ε u T).trace = ∑ i, hherm.eigenvalues i := by
    have h := hherm.trace_eq_sum_eigenvalues
    simpa using h
  have hdetev : (VV ε u T).det = ∏ i, hherm.eigenvalues i := by
    have h := hherm.det_eq_prod_eigenvalues
    simpa using h
  have htrpos : (0:ℝ) < (VV ε u T).trace := by
    rw [htr]
    have : (0:ℝ) ≤ ∑ t ∈ Finset.Icc 1 T, ‖u t‖ ^ 2 :=
      Finset.sum_nonneg fun t _ => by positivity
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hMpos : 0 < ((VV ε u T).trace) / n := by
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    exact div_pos htrpos hnR
  set M : ℝ := ((VV ε u T).trace) / n with hM
  have hLT : L T ≤ n * Real.log M := by
    rw [hL]
    simp only
    rw [hdetev, Real.log_prod (fun i _ => (hev i).ne')]
    have hb : ∀ i : Fin n, Real.log (hherm.eigenvalues i)
        ≤ (hherm.eigenvalues i / M - 1) + Real.log M := by
      intro i
      have h := Real.log_le_sub_one_of_pos (div_pos (hev i) hMpos)
      rw [Real.log_div (hev i).ne' hMpos.ne'] at h
      linarith
    refine le_trans (Finset.sum_le_sum fun i _ => hb i) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_sub_distrib, Finset.sum_const,
      ← Finset.sum_div, ← htrev]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    rw [hM]
    field_simp
    linarith
  have hMle : M ≤ ε + T * r ^ 2 := by
    rw [hM, htr]
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hnR0 : (0:ℝ) < n := by linarith
    rw [div_le_iff₀ hnR0]
    have h1 : (0:ℝ) ≤ T * r ^ 2 := by positivity
    nlinarith [hnormsq]
  have hfin : n * Real.log M - n * Real.log ε ≤ n * Real.log (r ^ 2 * T / ε + 1) := by
    have hnR : (0:ℝ) ≤ n := by positivity
    have harg : M / ε ≤ r ^ 2 * T / ε + 1 := by
      rw [div_le_iff₀ hε]
      have : (r ^ 2 * T / ε + 1) * ε = r ^ 2 * T + ε := by field_simp
      rw [this]
      nlinarith [hMle]
    have h1 : Real.log M - Real.log ε = Real.log (M / ε) := (Real.log_div hMpos.ne' hε.ne').symm
    have h2 : Real.log (M / ε) ≤ Real.log (r ^ 2 * T / ε + 1) :=
      Real.log_le_log (div_pos hMpos hε) harg
    have : n * Real.log M - n * Real.log ε = n * (Real.log M - Real.log ε) := by ring
    rw [this, h1]
    exact mul_le_mul_of_nonneg_left h2 hnR
  rw [hL0]
  linarith

theorem solution {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (T : ℕ) (hu : ∀ t ∈ Finset.Icc 1 T, ‖u t‖ ≤ r) :
    ∑ t ∈ Finset.Icc 1 T, quadForm (regGram ε u t)⁻¹ (u t) ≤
      n * Real.log (r ^ 2 * T / ε + 1) := by
  have h : ∀ t : ℕ, quadForm (regGram ε u t)⁻¹ (u t)
      = WithLp.ofLp (u t) ⬝ᵥ ((VV ε u t)⁻¹ *ᵥ WithLp.ofLp (u t)) := by
    intro t
    rfl
  rw [Finset.sum_congr rfl fun t _ => h t]
  exact ep_core u r ε T hr hε hu
