-- Prove2me | solution 1 for MaxPressure.StrictLeontief.extreme_maximizer_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:31:55.672997+00:00
-- url     : https://prove2.me/submissions/8bca046b-1511-4bcc-868e-dcbe092405bc

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network



namespace MaxPressure.StrictLeontief

theorem pressure_lin {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) (s t : ℝ) (x y : Fin J → ℝ) :
    pressure N (s • x + t • y) z = s * pressure N x z + t * pressure N y z := by
  simp [pressure, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]

theorem pressure_cont {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) :
    Continuous (fun a : Fin J → ℝ => pressure N a z) := by
  unfold pressure
  have : (fun a : Fin J → ℝ => dotProduct z (Matrix.mulVec (R N) a)) =
      fun a => ∑ i, z i * ∑ j, R N i j * a j := by
    funext a; simp [dotProduct, Matrix.mulVec]
  rw [this]
  fun_prop

theorem cont_sum {J K : ℕ} (c : Fin J → ℝ) :
    Continuous (fun a : Fin J → ℝ => ∑ j, c j * a j) :=
  continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)

theorem allocSet_closed {I J K : ℕ} (N : Network I J K) : IsClosed (allocSet N) := by
  unfold allocSet
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
    ((isClosed_iInter fun k => ?_).inter (isClosed_iInter fun k => ?_))
  · exact isClosed_le (cont_sum (K := K) (fun j => N.A k j)) continuous_const
  · by_cases hk : N.inputProc k
    · simp only [hk, true_implies, Set.iInter_true]
      exact isClosed_eq (cont_sum (K := K) (fun j => N.A k j)) continuous_const
    · simp [hk]

theorem allocSet_bdd {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    ∀ a ∈ allocSet N, ∀ j, a j ≤ 1 := by
  intro a ha j
  obtain ⟨h01, -, -, -, hAk, -⟩ := hN
  obtain ⟨k, hk⟩ := hAk j
  have h1 := ha.2.1 k
  have : N.A k j * a j ≤ ∑ j, N.A k j * a j :=
    Finset.single_le_sum (f := fun j => N.A k j * a j)
      (fun j _ => mul_nonneg (by rcases h01 k j with h | h <;> rw [h] <;> norm_num) (ha.1 j))
      (Finset.mem_univ j)
  rw [hk] at this
  linarith

theorem allocSet_compact {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    IsCompact (allocSet N) := by
  apply Metric.isCompact_of_isClosed_isBounded (allocSet_closed N)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, fun a ha => ?_⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (ha.1 j)]
  exact allocSet_bdd N hN a ha j

theorem emv_core {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (at' : Fin J → ℝ) (hat : at' ∈ allocSet N)
    (hmax : ∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N at' z)
    (hvan : ∀ j ∈ J0 N z, at' j = 0) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0 := by
  set F : Set (Fin J → ℝ) := {a | a ∈ allocSet N ∧ pressure N a z = pressure N at' z ∧
      ∀ j ∈ J0 N z, a j = 0} with hF
  have hFne : F.Nonempty := ⟨at', hat, rfl, hvan⟩
  have hFcl : IsClosed F := by
    have h1 : IsClosed {a : Fin J → ℝ | pressure N a z = pressure N at' z} :=
      isClosed_eq (pressure_cont N z) continuous_const
    have h2 : IsClosed {a : Fin J → ℝ | ∀ j ∈ J0 N z, a j = 0} := by
      simp only [Set.setOf_forall]
      exact isClosed_biInter fun j _ => isClosed_eq (continuous_apply j) continuous_const
    have : F = allocSet N ∩ ({a | pressure N a z = pressure N at' z} ∩ {a | ∀ j ∈ J0 N z, a j = 0}) := by
      ext a; simp only [hF, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [this]
    exact (allocSet_closed N).inter (h1.inter h2)
  have hFc : IsCompact F := (allocSet_compact N hN).of_isClosed_subset hFcl (fun a ha => ha.1)
  have hext : IsExtreme ℝ (allocSet N) F := by
    refine ⟨fun a ha => ha.1, ?_⟩
    intro x₁ hx₁ x₂ hx₂ x hx hseg
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hseg
    obtain ⟨hxA, hxp, hxv⟩ := hx
    have hp := pressure_lin N z s t x₁ x₂
    have h1 := hmax x₁ hx₁
    have h2 := hmax x₂ hx₂
    rw [hxp] at hp
    have hM : s * pressure N at' z + t * pressure N at' z = pressure N at' z := by
      rw [← add_mul, hst, one_mul]
    have e1 : pressure N x₁ z = pressure N at' z := by
      refine le_antisymm h1 ?_
      by_contra hlt
      push_neg at hlt
      nlinarith [mul_pos hs (sub_pos.2 hlt), mul_nonneg ht.le (sub_nonneg.2 h2)]
    refine ⟨hx₁, e1, ?_⟩
    intro j hj
    have := hxv j hj
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have a1 := hx₁.1 j
    have a2 := hx₂.1 j
    refine le_antisymm ?_ a1
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_pos hs hlt, mul_nonneg ht.le a2]
  obtain ⟨a, ha⟩ := hFc.extremePoints_nonempty hFne
  have haE : a ∈ extremeAllocs N := hext.extremePoints_subset_extremePoints ha
  obtain ⟨⟨haA, hap, hav⟩, -⟩ := ha
  refine ⟨a, haE, fun a' ha' => ?_, hav⟩
  rw [hap]; exact hmax a' ha'

end MaxPressure.StrictLeontief

open MaxPressure.StrictLeontief


theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (at' : Fin J → ℝ) (hat : at' ∈ allocSet N)
    (hmax : ∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N at' z)
    (hvan : ∀ j ∈ J0 N z, at' j = 0) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0 := by
  exact emv_core N hN hSL z hz at' hat hmax hvan
