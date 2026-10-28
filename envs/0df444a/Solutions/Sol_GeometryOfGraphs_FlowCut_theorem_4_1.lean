-- Prove2me | solution 1 for GeometryOfGraphs.FlowCut.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:27:18.873389+00:00
-- url     : https://prove2.me/submissions/c88e25db-dfa5-40a9-9e5e-fc8ae86d9fc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow
import Theorems.Thm_GeometryOfGraphs_FlowCut_lp_duality
import Theorems.Thm_GeometryOfGraphs_FlowCut_corollary_3_4_claim_2
import Theorems.Thm_GeometryOfGraphs_FlowCut_l1_coordinate_min
import Theorems.Thm_GeometryOfGraphs_FlowCut_variational_zero_one

set_option autoImplicit false

open GeometryOfGraphs.FlowCut

private lemma sum_b_eq {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) (f : V → ℝ) :
    (∑ i, ∑ j, ((1 / 2 : ℝ) * ∑ μ,
        ((if i = N.s μ ∧ j = N.t μ then N.D μ else 0) +
         (if i = N.t μ ∧ j = N.s μ then N.D μ else 0))) * |f i - f j|) =
      ∑ μ, N.D μ * |f (N.s μ) - f (N.t μ)| := by
  have hpair : ∀ (u v : V) (c : ℝ),
      (∑ i, ∑ j, (if i = u ∧ j = v then c else 0) * |f i - f j|) = c * |f u - f v| := by
    intro u v c
    have h1 : ∀ i, (∑ j, (if i = u ∧ j = v then c else 0) * |f i - f j|) =
        if i = u then c * |f u - f v| else 0 := by
      intro i
      by_cases hi : i = u
      · subst hi
        simp
      · simp [hi]
    simp_rw [h1]
    simp
  have hstep : ∀ i j,
      ((1 / 2 : ℝ) * ∑ μ,
        ((if i = N.s μ ∧ j = N.t μ then N.D μ else 0) +
         (if i = N.t μ ∧ j = N.s μ then N.D μ else 0))) * |f i - f j| =
      ∑ μ, (1 / 2 : ℝ) *
        ((if i = N.s μ ∧ j = N.t μ then N.D μ else 0) * |f i - f j| +
         (if i = N.t μ ∧ j = N.s μ then N.D μ else 0) * |f i - f j|) := by
    intro i j
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  simp_rw [hstep]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp_rw [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hpair (N.s μ) (N.t μ) (N.D μ), hpair (N.t μ) (N.s μ) (N.D μ),
      abs_sub_comm (f (N.t μ)) (f (N.s μ))]
  ring

private lemma sum_b_indicator_eq_Dem {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (S : Finset V) :
    (∑ μ, N.D μ * |(if N.s μ ∈ S then (1 : ℝ) else 0) - (if N.t μ ∈ S then 1 else 0)|) =
      N.Dem S := by
  unfold Network.Dem
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun μ _ => ?_
  by_cases hs : N.s μ ∈ S <;> by_cases ht : N.t μ ∈ S <;> simp [hs, ht]

private lemma sum_a_indicator_eq_Cap {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (S : Finset V) :
    (∑ i, ∑ j, ((1 / 2 : ℝ) * N.C i j) *
      |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) = N.Cap S := by
  have hsplit : ∀ (g : V → ℝ), (∑ v : V, g v) = (∑ v ∈ S, g v) + (∑ v ∈ Sᶜ, g v) := by
    intro g
    exact (Finset.sum_add_sum_compl S g).symm
  rw [hsplit]
  have hS : (∑ i ∈ S, ∑ j : V, ((1 / 2 : ℝ) * N.C i j) *
      |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) =
      (1 / 2 : ℝ) * N.Cap S := by
    unfold Network.Cap
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hsplit]
    have h1 : (∑ j ∈ S, ((1 / 2 : ℝ) * N.C i j) *
        |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp [hi, hj]
    have h2 : (∑ j ∈ Sᶜ, ((1 / 2 : ℝ) * N.C i j) *
        |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) =
        (1 / 2 : ℝ) * ∑ j ∈ Sᶜ, N.C i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ∉ S := Finset.mem_compl.mp hj
      simp [hi, hj']
    rw [h1, h2, zero_add]
  have hSc : (∑ i ∈ Sᶜ, ∑ j : V, ((1 / 2 : ℝ) * N.C i j) *
      |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) =
      (1 / 2 : ℝ) * N.Cap S := by
    have hSc1 : (∑ i ∈ Sᶜ, ∑ j : V, ((1 / 2 : ℝ) * N.C i j) *
        |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) =
        ∑ i ∈ Sᶜ, (1 / 2 : ℝ) * ∑ j ∈ S, N.C i j := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ∉ S := Finset.mem_compl.mp hi
      rw [hsplit]
      have h1 : (∑ j ∈ S, ((1 / 2 : ℝ) * N.C i j) *
          |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) =
          (1 / 2 : ℝ) * ∑ j ∈ S, N.C i j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [hi', hj]
      have h2 : (∑ j ∈ Sᶜ, ((1 / 2 : ℝ) * N.C i j) *
          |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj' : j ∉ S := Finset.mem_compl.mp hj
        simp [hi', hj']
      rw [h1, h2, add_zero]
    rw [hSc1, ← Finset.mul_sum, Finset.sum_comm]
    unfold Network.Cap
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => N.C_symm i j
  rw [hS, hSc]
  ring

theorem solution :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (N : Network V),
        (∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) →
        ∃ S : Finset V, 0 < N.Dem S ∧
          N.Cap S ≤ C₀ * Real.log (max (N.k : ℝ) 2) * N.maxflow * N.Dem S := by
  obtain ⟨C₁, hC₁_pos, hclaim2⟩ := corollary_3_4_claim_2
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro V _ _ N hN
  obtain ⟨d, hd, hd_pos, hd_eq⟩ := (lp_duality N hN).2
  obtain ⟨m, φ, hφ_le, hφ_ge⟩ := hclaim2 V d hd N.k N.s N.t
  let K : ℝ := C₁ * Real.log (max (N.k : ℝ) 2)
  have hlog_pos : 0 < Real.log (max (N.k : ℝ) 2) :=
    Real.log_pos (by linarith [le_max_right (N.k : ℝ) 2])
  have hK_pos : 0 < K := mul_pos hC₁_pos hlog_pos
  have hsum_d_le : (∑ μ, N.D μ * d (N.s μ) (N.t μ)) ≤
      K * ∑ μ, N.D μ * ∑ r, |φ (N.s μ) r - φ (N.t μ) r| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hφ_ge μ) (N.D_nonneg μ)
    linarith
  have hφ_pos : 0 < ∑ μ, N.D μ * ∑ r, |φ (N.s μ) r - φ (N.t μ) r| := by
    by_contra hle
    have hle' : K * ∑ μ, N.D μ * ∑ r, |φ (N.s μ) r - φ (N.t μ) r| ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hK_pos) (not_lt.mp hle)
    linarith
  have hcap_d_nonneg : 0 ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, N.C i j * d i j := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
    exact mul_nonneg (N.C_nonneg i j) (hd.2.1 i j)
  have hmaxflow_nonneg : 0 ≤ N.maxflow := by
    by_contra hlt
    have hneg : N.maxflow * ∑ μ, N.D μ * d (N.s μ) (N.t μ) < 0 :=
      mul_neg_of_neg_of_pos (not_le.mp hlt) hd_pos
    linarith
  have hφ_cap_le : (1 / 2 : ℝ) * ∑ i, ∑ j, N.C i j * ∑ r, |φ i r - φ j r| ≤
      (1 / 2 : ℝ) * ∑ i, ∑ j, N.C i j * d i j := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left (hφ_le i j) (N.C_nonneg i j)
  obtain ⟨r, hr_pos, hr_le⟩ := l1_coordinate_min N φ hφ_pos
  have hr_bound : (1 / 2 : ℝ) * ∑ i, ∑ j, N.C i j * |φ i r - φ j r| ≤
      K * N.maxflow * ∑ μ, N.D μ * |φ (N.s μ) r - φ (N.t μ) r| := by
    have hstep1 : ((1 / 2 : ℝ) * ∑ i, ∑ j, N.C i j * ∑ r', |φ i r' - φ j r'|) ≤
        K * N.maxflow * ∑ μ, N.D μ * ∑ r', |φ (N.s μ) r' - φ (N.t μ) r'| := by
      have h2 := mul_le_mul_of_nonneg_left hsum_d_le hmaxflow_nonneg
      linarith
    have hstep2 : ((1 / 2 : ℝ) * ∑ i, ∑ j, N.C i j * |φ i r - φ j r|) *
        (∑ μ, N.D μ * ∑ r', |φ (N.s μ) r' - φ (N.t μ) r'|) ≤
        (K * N.maxflow * ∑ μ, N.D μ * |φ (N.s μ) r - φ (N.t μ) r|) *
        (∑ μ, N.D μ * ∑ r', |φ (N.s μ) r' - φ (N.t μ) r'|) := by
      have h3 := mul_le_mul_of_nonneg_right hstep1 (le_of_lt hr_pos)
      linarith
    exact le_of_mul_le_mul_right hstep2 hφ_pos
  let a : V → V → ℝ := fun i j => (1 / 2 : ℝ) * N.C i j
  let b : V → V → ℝ := fun i j => (1 / 2 : ℝ) * ∑ μ,
    ((if i = N.s μ ∧ j = N.t μ then N.D μ else 0) +
     (if i = N.t μ ∧ j = N.s μ then N.D μ else 0))
  have hb_nonneg : ∀ i j, 0 ≤ b i j := by
    intro i j
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun μ _ => ?_)
    have hD := N.D_nonneg μ
    split_ifs <;> linarith
  have ha_symm : ∀ i j, a i j = a j i := fun i j => by dsimp [a]; rw [N.C_symm i j]
  have hb_symm : ∀ i j, b i j = b j i := by
    intro i j
    dsimp [b]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h1 : (j = N.s μ ∧ i = N.t μ) ↔ (i = N.t μ ∧ j = N.s μ) := and_comm
    have h2 : (j = N.t μ ∧ i = N.s μ) ↔ (i = N.s μ ∧ j = N.t μ) := and_comm
    rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl, add_comm]
  have hz_pos : 0 < ∑ i, ∑ j, b i j * |φ i r - φ j r| := by
    rw [sum_b_eq N (fun i => φ i r)]
    exact hr_pos
  obtain ⟨S, hS_pos, hS_le⟩ :=
    variational_zero_one a b hb_nonneg ha_symm hb_symm (fun i => φ i r) hz_pos
  rw [sum_b_eq N (fun i => if i ∈ S then (1 : ℝ) else 0), sum_b_indicator_eq_Dem N S] at hS_pos hS_le
  rw [sum_b_eq N (fun i => φ i r), sum_a_indicator_eq_Cap N S] at hS_le
  have ha_z_eq : (∑ i, ∑ j, a i j * |φ i r - φ j r|) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, N.C i j * |φ i r - φ j r| := by
    dsimp [a]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [ha_z_eq] at hS_le
  refine ⟨S, hS_pos, ?_⟩
  have hmul_le : N.Cap S * (∑ μ, N.D μ * |φ (N.s μ) r - φ (N.t μ) r|) ≤
      (K * N.maxflow * N.Dem S) * (∑ μ, N.D μ * |φ (N.s μ) r - φ (N.t μ) r|) := by
    have h4 := mul_le_mul_of_nonneg_right hr_bound (le_of_lt hS_pos)
    linarith
  exact le_of_mul_le_mul_right hmul_le hr_pos
