-- Prove2me | solution 1 for MarkovInterference.DQBias.dq_first_order
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:27:07.339991+00:00
-- url     : https://prove2.me/submissions/5c8317c4-1674-496f-9b40-6d45500937ed

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

lemma onesRho_half : onesRho (fun _ : Fin 2 => (1 / 2 : ℝ)) = H := by
  ext i j; simp [onesRho, Matrix.vecMulVec_apply, H_apply]

lemma groupInv_half : groupInv H (fun _ : Fin 2 => (1 / 2 : ℝ)) = 1 - H := by
  rw [groupInv, onesRho_half]; simp

lemma G_f : (groupInv H (fun _ : Fin 2 => (1 / 2 : ℝ))).mulVec f = fun s => f s - 3 / 2 := by
  rw [groupInv_half]; ext s
  fin_cases s <;> simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, H_apply, f] <;>
    norm_num

end DQBiasCounterexample

open DQBiasCounterexample in
theorem solution : ¬ (∀ {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S) (rho : S → ℝ)
    (hp : IsPrimitive M.Phalf) (hrho : IsStationaryDist M.Phalf rho),
    M.dqMean rho = rho ⬝ᵥ
      (M.rvec 1 - M.rvec 0 +
        (M.P 1 - M.P 0).mulVec ((groupInv M.Phalf rho).mulVec M.rHalf)) ∧
    ∀ (A : Matrix S S ℝ) (δ : ℝ),
      M.P 0 = M.Phalf - δ • A → M.P 1 = M.Phalf + δ • A →
      M.dqMean rho = rho ⬝ᵥ M.rvec 1 - rho ⬝ᵥ M.rvec 0 +
        δ * (Matrix.vecMul rho (A * groupInv M.Phalf rho) ⬝ᵥ
          (M.rvec 1 + M.rvec 0))) := by
  intro hall
  have he : (0 : ℝ) ≤ 1 / 4 := by norm_num
  set M := mdp (1 / 4) he le_rfl
  let rhoH : Fin 2 → ℝ := fun _ => 1 / 2
  have hPh := Phalf_eq (1 / 4) he le_rfl
  have hprim : IsPrimitive M.Phalf := ⟨1, fun i j => by rw [pow_one, hPh, H_apply]; norm_num⟩
  have hstH : IsStationaryDist M.Phalf rhoH := by
    refine ⟨fun _ => by norm_num, by simp [rhoH, Fin.sum_univ_two], ?_⟩
    rw [hPh]; ext j; simp [rhoH, Matrix.vecMul, dotProduct, Fin.sum_univ_two, H_apply]
  have h := (hall M rhoH hprim hstH).1
  have hT : ∀ s a, ∑' t : ℕ, (M.P a * M.Phalf ^ t).mulVec M.rHalf s = 0 :=
    fun s a => tsum_zero (1 / 4) he le_rfl s a
  have hdq : M.dqMean rhoH = 0 := by
    simp only [MDP.dqMean, MDP.Q, hT]
    simp [M, mdp]
  have hrH : M.rHalf = f := by
    ext s; simp [MDP.rHalf, M, mdp]
  rw [hdq, hPh, hrH, G_f] at h
  simp [M, mdp, rhoH, MDP.rvec, Pm, sg, tg, f, dotProduct, Matrix.mulVec, Fin.sum_univ_two] at h
  norm_num at h
