-- Prove2me | solution 1 for MarkovEntanglement.decomposition_error_atv_sup_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T01:29:39.8252+00:00
-- url     : https://prove2.me/submissions/6308fdcb-f93b-432f-a05e-5c46ee1e6c38

import Mathlib
import Definitions.Def_markov_entanglement_multi_atv

open scoped BigOperators
open MarkovEntanglement

namespace MEatv

variable {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Grouping a sum over joint successors by the coordinate of agent `i`. -/
theorem fiber (P : Matrix (Joint S) (Joint S) ℝ) (i : Fin N) (q : Joint S) (g : S i → ℝ) :
    ∑ q' : Joint S, P q q' * g (q' i) = ∑ t : S i, marginalN i P q t * g t := by
  simp only [marginalN, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ => ?_
  simp

/-- The Bellman residual of the candidate decomposition. -/
theorem residual (P : Matrix (Joint S) (Joint S) ℝ) (γ : ℝ) (r : ∀ i, S i → ℝ)
    (Q : Joint S → ℝ) (Pl : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    (hQi : ∀ i, IsBellmanQ (Pl i) (r i) γ (Qi i)) (q : Joint S) :
    Q q - ∑ i, Qi i (q i)
      = γ * (∑ q' : Joint S, P q q' * (Q q' - ∑ i, Qi i (q' i)))
        + γ * ∑ i, ∑ t : S i, (marginalN i P q t - Pl i (q i) t) * Qi i t := by
  have hsplit : ∑ q' : Joint S, P q q' * (Q q' - ∑ i, Qi i (q' i))
      = (∑ q' : Joint S, P q q' * Q q') - ∑ i, ∑ t : S i, marginalN i P q t * Qi i t := by
    have h1 : ∀ q' : Joint S, P q q' * (Q q' - ∑ i, Qi i (q' i))
        = P q q' * Q q' - ∑ i, P q q' * Qi i (q' i) := by
      intro q'; rw [mul_sub, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun q' (_ : q' ∈ Finset.univ) => h1 q'),
      Finset.sum_sub_distrib, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => fiber P i q (Qi i)
  have h2 : ∀ i : Fin N, ∑ t : S i, (marginalN i P q t - Pl i (q i) t) * Qi i t
      = (∑ t : S i, marginalN i P q t * Qi i t) - ∑ t : S i, Pl i (q i) t * Qi i t := by
    intro i; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun t _ => by ring
  rw [hsplit, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h2 i),
    Finset.sum_sub_distrib]
  have hq := hQ q
  have hqi : ∀ i, Qi i (q i) = r i (q i) + γ * ∑ t : S i, Pl i (q i) t * Qi i t :=
    fun i => hQi i (q i)
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hqi i), Finset.sum_add_distrib,
    ← Finset.mul_sum, hq]
  ring

/-- A row of a transition matrix averages: `|∑ⱼ Pᵢⱼ vⱼ| ≤ max |v|`. -/
theorem row_avg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (hA : IsTransitionMatrix A)
    (v : ι → ℝ) (B : ℝ) (hv : ∀ j, |v j| ≤ B) (s : ι) : |∑ j, A s j * v j| ≤ B := by
  calc |∑ j, A s j * v j| ≤ ∑ j, |A s j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, A s j * |v j| := by
        exact Finset.sum_congr rfl fun j _ => by
          rw [abs_mul, abs_of_nonneg (hA.1 s j)]
    _ ≤ ∑ j, A s j * B := Finset.sum_le_sum fun j _ => by
        exact mul_le_mul_of_nonneg_left (hv j) (hA.1 s j)
    _ = B := by rw [← Finset.sum_mul, hA.2 s, one_mul]

/-- The local value function is bounded by `rmax / (1 - γ)`. -/
theorem Qi_bound {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : IsTransitionMatrix A) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : ι → ℝ) (rm : ℝ) (hρ : ∀ s, |ρ s| ≤ rm) (V : ι → ℝ) (hV : IsBellmanQ A ρ γ V) :
    ∀ s, |V s| ≤ rm / (1 - γ) := by
  classical
  have hune : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  obtain ⟨s0, -, hs0⟩ := Finset.exists_mem_eq_sup' hune (fun s => |V s|)
  have hle : ∀ s, |V s| ≤ |V s0| := by
    intro s
    rw [← hs0]
    exact Finset.le_sup' (fun s => |V s|) (Finset.mem_univ s)
  have h1 : |V s0| = |ρ s0 + γ * ∑ j, A s0 j * V j| := by rw [hV s0]
  have h2 : |∑ j, A s0 j * V j| ≤ |V s0| := row_avg A hA V _ hle s0
  have h3 : |ρ s0 + γ * ∑ j, A s0 j * V j| ≤ |ρ s0| + |γ * ∑ j, A s0 j * V j| :=
    abs_add_le _ _
  have h4 : |γ * ∑ j, A s0 j * V j| = γ * |∑ j, A s0 j * V j| := by
    rw [abs_mul, abs_of_nonneg hγ]
  have h5 := mul_le_mul_of_nonneg_left h2 hγ
  have hstep : |V s0| ≤ rm + γ * |V s0| := by linarith [hρ s0]
  have hMle : |V s0| ≤ rm / (1 - γ) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  exact fun s => le_trans (hle s) hMle

end MEatv

open MEatv

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |r i s| ≤ rmax i)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, agentTVDistN i P (Pl i) = agentEntanglementWith i (agentTVDistN i) P)
    (hQi : ∀ i, IsBellmanQ (Pl i) (r i) γ (Qi i)) (p : Joint S) :
    |Q p - ∑ i, Qi i (p i)|
      ≤ 4 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ) ^ 2 := by
  classical
  have hg : (0:ℝ) < 1 - γ := by linarith
  -- every joint state realises at most the supremal agent-wise TV distance
  have hsupbd : ∀ (i : Fin N) (q : Joint S),
      (1/2) * ∑ t : S i, |marginalN i P q t - Pl i (q i) t|
        ≤ agentEntanglementWith i (agentTVDistN i) P := by
    intro i q
    rw [← hopt i]
    show (1/2) * ∑ t : S i, |marginalN i P q t - Pl i (q i) t|
      ≤ ⨆ q' : Joint S, (1 / 2) * ∑ t : S i, |marginalN i P q' t - Pl i (q' i) t|
    exact le_ciSup (f := fun q' : Joint S =>
      (1 / 2) * ∑ t : S i, |marginalN i P q' t - Pl i (q' i) t|)
      (Finite.bddAbove_range _) q
  have hEnn : ∀ i, 0 ≤ agentEntanglementWith i (agentTVDistN i) P := by
    intro i
    refine le_trans ?_ (hsupbd i p)
    positivity
  have hrm : ∀ i, 0 ≤ rmax i := fun i => le_trans (abs_nonneg _) (hr i (p i))
  have hMi : ∀ (i : Fin N) (s : S i), |Qi i s| ≤ rmax i / (1 - γ) := by
    intro i
    haveI : Nonempty (S i) := ⟨p i⟩
    exact Qi_bound (Pl i) (hPl i) γ hγ hγ1 (r i) (rmax i) (hr i) (Qi i) (hQi i)
  -- the per-agent Bellman residual
  have hres : ∀ (i : Fin N) (q : Joint S),
      |∑ t : S i, (marginalN i P q t - Pl i (q i) t) * Qi i t|
        ≤ 2 * agentEntanglementWith i (agentTVDistN i) P * (rmax i / (1 - γ)) := by
    intro i q
    have hnn : (0:ℝ) ≤ rmax i / (1 - γ) := div_nonneg (hrm i) (le_of_lt hg)
    have hstep : ∑ t : S i, |marginalN i P q t - Pl i (q i) t|
        ≤ 2 * agentEntanglementWith i (agentTVDistN i) P := by
      have := hsupbd i q; linarith
    calc |∑ t : S i, (marginalN i P q t - Pl i (q i) t) * Qi i t|
        ≤ ∑ t : S i, |(marginalN i P q t - Pl i (q i) t) * Qi i t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t : S i, |marginalN i P q t - Pl i (q i) t| * |Qi i t| :=
          Finset.sum_congr rfl fun t _ => abs_mul _ _
      _ ≤ ∑ t : S i, |marginalN i P q t - Pl i (q i) t| * (rmax i / (1 - γ)) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hMi i t) (abs_nonneg _)
      _ = (∑ t : S i, |marginalN i P q t - Pl i (q i) t|) * (rmax i / (1 - γ)) := by
          rw [Finset.sum_mul]
      _ ≤ 2 * agentEntanglementWith i (agentTVDistN i) P * (rmax i / (1 - γ)) :=
          mul_le_mul_of_nonneg_right hstep hnn
  -- take the maximum of the decomposition error
  have hune : (Finset.univ : Finset (Joint S)).Nonempty := ⟨p, Finset.mem_univ p⟩
  obtain ⟨q0, -, hq0⟩ := Finset.exists_mem_eq_sup' hune (fun q => |Q q - ∑ i, Qi i (q i)|)
  have hle : ∀ q : Joint S, |Q q - ∑ i, Qi i (q i)| ≤ |Q q0 - ∑ i, Qi i (q0 i)| := by
    intro q; rw [← hq0]
    exact Finset.le_sup' (fun q => |Q q - ∑ i, Qi i (q i)|) (Finset.mem_univ q)
  have hrow : |∑ q' : Joint S, P q0 q' * (Q q' - ∑ i, Qi i (q' i))|
      ≤ |Q q0 - ∑ i, Qi i (q0 i)| :=
    row_avg P hP (fun q => Q q - ∑ i, Qi i (q i)) _ hle q0
  have habs : |∑ i : Fin N, ∑ t : S i, (marginalN i P q0 t - Pl i (q0 i) t) * Qi i t|
      ≤ ∑ i : Fin N, 2 * agentEntanglementWith i (agentTVDistN i) P * (rmax i / (1 - γ)) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => hres i q0)
  have hsum : ∑ i : Fin N, 2 * agentEntanglementWith i (agentTVDistN i) P * (rmax i / (1 - γ))
      = 2 * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hid := residual P γ r Q Pl Qi hQ hQi q0
  have e0 : |Q q0 - ∑ i, Qi i (q0 i)|
      = |γ * (∑ q' : Joint S, P q0 q' * (Q q' - ∑ i, Qi i (q' i)))
        + γ * ∑ i : Fin N, ∑ t : S i, (marginalN i P q0 t - Pl i (q0 i) t) * Qi i t| := by
    rw [hid]
  have hb := abs_add_le (γ * (∑ q' : Joint S, P q0 q' * (Q q' - ∑ i, Qi i (q' i))))
      (γ * ∑ i : Fin N, ∑ t : S i, (marginalN i P q0 t - Pl i (q0 i) t) * Qi i t)
  have hA1 : |γ * (∑ q' : Joint S, P q0 q' * (Q q' - ∑ i, Qi i (q' i)))|
      = γ * |∑ q' : Joint S, P q0 q' * (Q q' - ∑ i, Qi i (q' i))| := by
    rw [abs_mul, abs_of_nonneg hγ]
  have hA2 : |γ * ∑ i : Fin N, ∑ t : S i, (marginalN i P q0 t - Pl i (q0 i) t) * Qi i t|
      = γ * |∑ i : Fin N, ∑ t : S i, (marginalN i P q0 t - Pl i (q0 i) t) * Qi i t| := by
    rw [abs_mul, abs_of_nonneg hγ]
  have hs1 := mul_le_mul_of_nonneg_left hrow hγ
  have hs2 := mul_le_mul_of_nonneg_left habs hγ
  rw [hsum] at hs2
  have hmain : |Q q0 - ∑ i, Qi i (q0 i)|
      ≤ γ * |Q q0 - ∑ i, Qi i (q0 i)|
        + γ * (2 * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ)) := by
    linarith [e0, hb, hA1, hA2, hs1, hs2]
  have hSnn : 0 ≤ ∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hEnn i) (hrm i)
  have hfin : |Q q0 - ∑ i, Qi i (q0 i)|
      ≤ 4 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ) ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (1 - γ) ^ 2)]
    have h1 : (1 - γ) * |Q q0 - ∑ i, Qi i (q0 i)|
        ≤ γ * (2 * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ)) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hg)
    have h3 : (1 - γ) * (γ * (2 * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i)
        / (1 - γ))) = 2 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) := by
      field_simp
    rw [h3] at h2
    nlinarith [mul_nonneg hγ hSnn]
  exact le_trans (hle p) hfin
