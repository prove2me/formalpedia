-- Prove2me | solution 1 for GlobalInexactNewton.Backtracking.inb_isMRRun
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T19:15:26.015659+00:00
-- url     : https://prove2.me/submissions/155aa497-c951-4e0b-9ac0-358bc0001f39

import Init
import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method

open Filter Topology
open GlobalInexactNewton.Backtracking
namespace NewtonTrials

theorem levels (ηbar θmin θmax : ℝ) (hη : ηbar ∈ Set.Ico (0:ℝ) 1)
    (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1) (θ : ℕ → ℝ) (n : ℕ)
    (hmem : ∀ j < n, θ j ∈ Set.Icc θmin θmax) :
    ηbar ≤ trialLevel ηbar θ n ∧ trialLevel ηbar θ n < 1 := by
  induction n with
  | zero => exact ⟨le_rfl,hη.2⟩
  | succ n ih =>
    obtain ⟨hl,hu⟩ := ih (fun j hj => hmem j (Nat.lt_succ_of_lt hj))
    have ht := hmem n (Nat.lt_succ_self n)
    have hp := mul_le_mul_of_nonneg_right (ht.2.trans hθ.2.2.le) (sub_nonneg.mpr hu.le)
    have hpos := mul_pos (hθ.1.trans_le ht.1) (sub_pos.mpr hu)
    simp only [trialLevel]
    constructor <;> nlinarith

theorem gap_bound (ηbar θmin θmax : ℝ) (hη : ηbar ∈ Set.Ico (0:ℝ) 1)
    (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1) (θ : ℕ → ℝ)
    (hmem : ∀ j, θ j ∈ Set.Icc θmin θmax) (n : ℕ) :
    0 ≤ 1-trialLevel ηbar θ n ∧ 1-trialLevel ηbar θ n ≤ θmax^n*(1-ηbar) := by
  have hl := levels ηbar θmin θmax hη hθ θ n (fun j _ => hmem j)
  refine ⟨by linarith,?_⟩
  induction n with
  | zero => simp [trialLevel]
  | succ n ih =>
    have hn := levels ηbar θmin θmax hη hθ θ n (fun j _ => hmem j)
    have ht := hmem n
    have hx : 0 < θmax := lt_trans hθ.1 hθ.2.1
    have hm := mul_le_mul_of_nonneg_left (ih hn) hx.le
    have hb := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hn.2.le)
    simp only [trialLevel,pow_succ]
    nlinarith

theorem gap_tendsto (ηbar θmin θmax : ℝ) (hη : ηbar ∈ Set.Ico (0:ℝ) 1)
    (hθ : 0 < θmin ∧ θmin < θmax ∧ θmax < 1) (θ : ℕ → ℝ)
    (hmem : ∀ j, θ j ∈ Set.Icc θmin θmax) :
    Tendsto (fun n => 1-trialLevel ηbar θ n) atTop (𝓝 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (le_of_lt (lt_trans hθ.1 hθ.2.1)) hθ.2.2).mul_const (1-ηbar)
  apply squeeze_zero (fun n => (gap_bound ηbar θmin θmax hη hθ θ hmem n).1)
    (fun n => (gap_bound ηbar θmin θmax hη hθ θ hmem n).2)
  simpa using hp

#print axioms gap_tendsto
end NewtonTrials

open Filter Topology
open GlobalInexactNewton.Backtracking
namespace NewtonScaling
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scaled_condition (F : E → E) (x s : E) (ηbar η : ℝ)
    (hbar : ηbar < 1) (hη : η ∈ Set.Icc ηbar 1)
    (hi : InexactNewtonCond F x s ηbar) :
    InexactNewtonCond F x (((1-η)/(1-ηbar))•s) η := by
  let a := (1-η)/(1-ηbar)
  have hd : 0 < 1-ηbar := sub_pos.mpr hbar
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hη.2) hd.le
  have hau : a ≤ 1 := (div_le_one hd).mpr (by linarith [hη.1])
  have he : a*(1-ηbar) = 1-η := div_mul_cancel₀ _ (ne_of_gt hd)
  have hv : F x+fderiv ℝ F x (a•s) = (1-a)•F x+a•(F x+fderiv ℝ F x s) := by
    rw [map_smul]
    module
  unfold InexactNewtonCond at hi ⊢
  change ‖F x+fderiv ℝ F x (a•s)‖ ≤ η*‖F x‖
  rw [hv]
  have hn := norm_add_le ((1-a)•F x) (a•(F x+fderiv ℝ F x s))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg (sub_nonneg.mpr hau)] at hn
  have hm := mul_le_mul_of_nonneg_left hi ha
  have heN := congrArg (fun r : ℝ => r*‖F x‖) he
  nlinarith

theorem steps (s : E) (ηbar : ℝ) (hbar : ηbar < 1) (θ : ℕ → ℝ) (n : ℕ) :
    trialStep s θ n = ((1-trialLevel ηbar θ n)/(1-ηbar))•s := by
  induction n with
  | zero => simp [trialStep,trialLevel,ne_of_gt (sub_pos.mpr hbar)]
  | succ n ih =>
    rw [trialStep,ih,smul_smul,trialLevel]
    congr 1
    ring
end NewtonScaling

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ) (sbar : ℕ → E)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (hrun : IsINBRun F ηmax t θmin θmax x ηbar sbar θ m) :
    IsMRRun F ηmax t θmin θmax x ηbar (fun k η => ((1 - η) / (1 - ηbar k)) • sbar k) θ m ∧
      ∀ k j, trialStep (sbar k) (θ k) j =
        ((1 - trialLevel (ηbar k) (θ k) j) / (1 - ηbar k)) • sbar k := by
  have hb : ∀ k, ηbar k < 1 := fun k => (hrun.ηbar_mem k).2.trans_lt hrun.ηmax_mem.2
  have hs : ∀ k j, trialStep (sbar k) (θ k) j =
      ((1-trialLevel (ηbar k) (θ k) j)/(1-ηbar k))•sbar k :=
    fun k j => NewtonScaling.steps (sbar k) (ηbar k) (hb k) (θ k) j
  refine ⟨?_,hs⟩
  refine ⟨hrun.ηmax_mem,hrun.t_mem,hrun.θ_bounds,hrun.ηbar_mem,?_,hrun.θ_mem,?_,?_,?_⟩
  · intro k η hη
    exact NewtonScaling.scaled_condition F (x k) (sbar k) (ηbar k) η (hb k) hη (hrun.initial k)
  · intro k j hj
    rw [← hs k j]
    exact hrun.rejected k j hj
  · intro k
    rw [← hs k (m k)]
    exact hrun.accepted k
  · intro k
    rw [← hs k (m k)]
    exact hrun.step k

#print axioms solution
