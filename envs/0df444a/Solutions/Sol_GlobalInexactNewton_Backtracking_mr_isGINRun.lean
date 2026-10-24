-- Prove2me | solution 1 for GlobalInexactNewton.Backtracking.mr_isGINRun
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T19:15:22.764263+00:00
-- url     : https://prove2.me/submissions/cbbeec63-7a98-476e-ac0d-298c388a1bf4

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

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ) (σ : ℕ → ℝ → E)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (hrun : IsMRRun F ηmax t θmin θmax x ηbar σ θ m) :
    IsGINRun F t x (fun k => trialLevel (ηbar k) (θ k) (m k)) := by
  have hl : ∀ k, ηbar k ≤ trialLevel (ηbar k) (θ k) (m k) ∧
      trialLevel (ηbar k) (θ k) (m k) < 1 := by
    intro k
    exact NewtonTrials.levels (ηbar k) θmin θmax
      ⟨(hrun.ηbar_mem k).1,lt_of_le_of_lt (hrun.ηbar_mem k).2 hrun.ηmax_mem.2⟩
      hrun.θ_bounds (θ k) (m k) (hrun.θ_mem k)
  refine ⟨hrun.t_mem,?_,?_,?_⟩
  · intro k
    exact ⟨(hrun.ηbar_mem k).1.trans (hl k).1,(hl k).2⟩
  · intro k
    rw [hrun.step k,add_sub_cancel_left]
    exact hrun.curve k _ ⟨(hl k).1,(hl k).2.le⟩
  · intro k
    rw [hrun.step k,add_sub_cancel_left]
    exact hrun.accepted k

#print axioms solution
