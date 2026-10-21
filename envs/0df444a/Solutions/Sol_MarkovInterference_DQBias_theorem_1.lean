-- Prove2me | solution 1 for MarkovInterference.DQBias.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:23:26.073816+00:00
-- url     : https://prove2.me/submissions/34e3a396-b217-4a62-b17a-220b9793bd23

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain
import Definitions.Def_MarkovInterference_DQBias_MDP

open MarkovInterference.DQBias

namespace DQBiasCounterexample

/-- sign of the action: `+1` for action `1`, `-1` for action `0`. -/
def sg (a : Fin 2) : ℝ := if a = 1 then 1 else -1
/-- sign of the target state: `+1` for state `0`, `-1` for state `1`. -/
def tg (j : Fin 2) : ℝ := if j = 0 then 1 else -1

/-- Transition matrices: every row of `P a` equals `(1/2 + sg a * e, 1/2 - sg a * e)`. -/
noncomputable def Pm (e : ℝ) (a : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ j => 1 / 2 + e * sg a * tg j

/-- State-only rewards `f 0 = 2`, `f 1 = 1`. -/
def f (s : Fin 2) : ℝ := if s = 0 then 2 else 1

lemma sg_sq (a : Fin 2) : sg a * sg a = 1 := by
  unfold sg; split_ifs <;> norm_num

lemma stoch (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 4) (a : Fin 2) : IsStochastic (Pm e a) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold Pm sg tg
    split_ifs <;> nlinarith
  · simp [Pm, Fin.sum_univ_two, tg] <;> ring_nf

noncomputable def mdp (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 4) : MDP (Fin 2) where
  P := Pm e
  r := fun s _ => f s
  stoch := stoch e he he'

/-- The half-randomized matrix: all entries `1/2`. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => (1 / 2 : ℝ)

lemma H_apply (i j : Fin 2) : H i j = 1 / 2 := rfl

lemma Phalf_eq (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 4) :
    (mdp e he he').Phalf = H := by
  ext i j
  simp [MDP.Phalf, mdp, Pm, sg, H_apply]
  ring

lemma half_mul_half : H * H = H := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, H_apply]

lemma half_pow (k : ℕ) : H ^ (k + 1) = H := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, half_mul_half]

lemma mulVec_ge_one {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : IsStochastic P) (v : Fin 2 → ℝ)
    (hv : ∀ i, 1 ≤ v i) (i : Fin 2) : 1 ≤ P.mulVec v i := by
  simp only [Matrix.mulVec, dotProduct]
  calc (1 : ℝ) = ∑ j, P i j * 1 := by simp [hP.2 i]
    _ ≤ ∑ j, P i j * v j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hP.1 i j)

lemma tsum_zero (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 4) (s : Fin 2) (a : Fin 2) :
    ∑' t : ℕ, ((mdp e he he').P a * (mdp e he he').Phalf ^ t).mulVec (mdp e he he').rHalf s
      = 0 := by
  set M := mdp e he he'
  have hPh : IsStochastic M.Phalf := by
    rw [Phalf_eq]
    refine ⟨fun _ _ => by simp [H_apply], fun _ => ?_⟩
    simp [Fin.sum_univ_two, H_apply]
  have hr : ∀ i, 1 ≤ M.rHalf i := by
    intro i; simp only [MDP.rHalf, M, mdp, f]; split_ifs <;> norm_num
  have hpow : ∀ t : ℕ, ∀ i, 1 ≤ (M.Phalf ^ t).mulVec M.rHalf i := by
    intro t
    induction t with
    | zero => simpa using hr
    | succ t ih =>
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact mulVec_ge_one hPh _ ih i
  have hge : ∀ t : ℕ, 1 ≤ (M.P a * M.Phalf ^ t).mulVec M.rHalf s := by
    intro t
    rw [← Matrix.mulVec_mulVec]
    exact mulVec_ge_one (M.stoch a) _ (hpow t) s
  apply tsum_eq_zero_of_not_summable
  intro hs
  have ht := hs.tendsto_atTop_zero
  have := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  obtain ⟨t, ht⟩ := this
  linarith [hge t]

end DQBiasCounterexample

open DQBiasCounterexample in
theorem solution : ¬ (∃ q : Polynomial ℝ, ∀ {S : Type} [Fintype S] [DecidableEq S] (M : MDP S)
      (rhoHalf rho0 rho1 : S → ℝ) (C lam δ : ℝ),
      IsPrimitive (M.P 0) → IsPrimitive (M.P 1) →
      IsStationaryDist M.Phalf rhoHalf →
      IsStationaryDist (M.P 0) rho0 → IsStationaryDist (M.P 1) rho1 →
      0 < lam → lam < 1 →
      (∀ (k : ℕ) (s : S), tvDist ((M.Phalf ^ k) s) rhoHalf ≤ C * lam ^ k) →
      (∀ s : S, tvDist (M.P 1 s) (M.P 0 s) ≤ δ) →
      |M.ate rho0 rho1 - M.dqMean rhoHalf| ≤
        q.eval (Real.log C) * (1 / (1 - lam)) ^ 2 * M.rmax * δ ^ 2) := by
  rintro ⟨q, hq⟩
  set q0 := q.eval 0 with hq0
  set e : ℝ := 1 / (32 * (|q0| + 1)) with he_def
  have habs := abs_nonneg q0
  have he : 0 < e := by rw [he_def]; positivity
  have he' : e ≤ 1 / 4 := by
    rw [he_def, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hkey : 32 * |q0| * e < 1 := by
    rw [he_def]; rw [mul_one_div, div_lt_one (by positivity)]; linarith
  set M := mdp e he.le he'
  let rhoH : Fin 2 → ℝ := fun _ => 1 / 2
  let rho0 : Fin 2 → ℝ := fun j => 1 / 2 - e * tg j
  let rho1 : Fin 2 → ℝ := fun j => 1 / 2 + e * tg j
  have hP0 : M.P 0 = fun _ j => 1 / 2 - e * tg j := by
    ext i j; simp [M, mdp, Pm, sg]; ring
  have hP1 : M.P 1 = fun _ j => 1 / 2 + e * tg j := by
    ext i j; simp [M, mdp, Pm, sg]
  have tgb : ∀ j, (tg j = 1 ∨ tg j = -1) := by intro j; unfold tg; split_ifs <;> simp
  have hprim0 : IsPrimitive (M.P 0) := ⟨1, fun i j => by
    rw [pow_one, hP0]; rcases tgb j with h | h <;> simp only [h] <;> linarith⟩
  have hprim1 : IsPrimitive (M.P 1) := ⟨1, fun i j => by
    rw [pow_one, hP1]; rcases tgb j with h | h <;> simp only [h] <;> linarith⟩
  have hstH : IsStationaryDist M.Phalf rhoH := by
    refine ⟨fun _ => by norm_num, by simp [rhoH, Fin.sum_univ_two], ?_⟩
    rw [Phalf_eq]; ext j; simp [rhoH, Matrix.vecMul, dotProduct, Fin.sum_univ_two, H_apply]
  have hst0 : IsStationaryDist (M.P 0) rho0 := by
    refine ⟨fun j => ?_, ?_, ?_⟩
    · rcases tgb j with h | h <;> simp only [rho0, h] <;> linarith
    · simp [rho0, Fin.sum_univ_two, tg] <;> ring_nf
    · rw [hP0]; ext j; simp [rho0, Matrix.vecMul, dotProduct, Fin.sum_univ_two, tg] <;> ring_nf
  have hst1 : IsStationaryDist (M.P 1) rho1 := by
    refine ⟨fun j => ?_, ?_, ?_⟩
    · rcases tgb j with h | h <;> simp only [rho1, h] <;> linarith
    · simp [rho1, Fin.sum_univ_two, tg] <;> ring_nf
    · rw [hP1]; ext j; simp [rho1, Matrix.vecMul, dotProduct, Fin.sum_univ_two, tg] <;> ring_nf
  have hmix : ∀ (k : ℕ) (s : Fin 2), tvDist ((M.Phalf ^ k) s) rhoH ≤ 1 * (1 / 2) ^ k := by
    intro k s
    rcases k with _ | k
    · fin_cases s <;> simp [tvDist, rhoH, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num
    · rw [Phalf_eq, half_pow]
      simp [tvDist, rhoH, H_apply]
  have htv : ∀ s : Fin 2, tvDist (M.P 1 s) (M.P 0 s) ≤ 2 * e := by
    intro s
    rw [hP0, hP1]
    simp only [tvDist, Fin.sum_univ_two, tg]
    simp
    ring_nf
    rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < e * 2)]; linarith
  have h := hq M rhoH rho0 rho1 1 (1 / 2) (2 * e) hprim0 hprim1 hstH hst0 hst1
    (by norm_num) (by norm_num) hmix htv
  -- the DQ mean vanishes
  have hdq : M.dqMean rhoH = 0 := by
    have hT : ∀ s a, ∑' t : ℕ, (M.P a * M.Phalf ^ t).mulVec M.rHalf s = 0 :=
      fun s a => tsum_zero e he.le he' s a
    simp only [MDP.dqMean, MDP.Q, hT]
    simp [M, mdp]
  have hate : M.ate rho0 rho1 = 2 * e := by
    simp only [MDP.ate, MDP.rvec, M, mdp, rho0, rho1, dotProduct, Fin.sum_univ_two, f, tg]
    simp; ring
  have hrmax0 : 0 ≤ M.rmax := Real.iSup_nonneg fun s => Real.iSup_nonneg fun a => abs_nonneg _
  have hrmax2 : M.rmax ≤ 2 :=
    ciSup_le fun s => ciSup_le fun a => by
      simp only [M, mdp, f]; split_ifs <;> norm_num
  rw [hdq, hate, sub_zero, abs_of_pos (by linarith), Real.log_one, ← hq0] at h
  norm_num at h
  -- h : 2 * e ≤ q0 * 4 * rmax * (2 * e) ^ 2
  have h1 : q0 * 4 * M.rmax * (2 * e) ^ 2 ≤ |q0| * 4 * M.rmax * (2 * e) ^ 2 := by
    have := le_abs_self q0
    have : 0 ≤ 4 * M.rmax * (2 * e) ^ 2 := by positivity
    nlinarith
  have h2 : |q0| * 4 * M.rmax * (2 * e) ^ 2 ≤ |q0| * 4 * 2 * (2 * e) ^ 2 := by
    have : 0 ≤ |q0| * 4 * (2 * e) ^ 2 := by positivity
    nlinarith
  have h3 : |q0| * 4 * 2 * (2 * e) ^ 2 = (32 * |q0| * e) * e := by ring
  have h4 : (32 * |q0| * e) * e < e := by nlinarith
  linarith
