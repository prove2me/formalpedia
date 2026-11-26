-- Prove2me | solution 1 for Kyprianou.Ch04.affineStepLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:29:11.802389+00:00
-- url     : https://prove2.me/submissions/ca0b293e-fd15-4825-a57f-c88dbc9ac749

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A positive-time left limit of a finite affine-step path uses strict time indicators. -/
theorem solution {ι : Type} (U : NNReal → ℝ) (S : Finset ι) (r a : ι → ℝ)
    (c d : ℝ) (t T : NNReal) (ht : 0 < t) (hT : t ≤ T)
    (hU : ∀ u ≤ T, U u = c + d * (u : ℝ) +
      ∑ i ∈ S, if r i ≤ (u : ℝ) then a i else 0)
    (l : ℝ) (hl : Tendsto U (𝓝[<] t) (𝓝 l)) :
    l = c + d * (t : ℝ) + ∑ i ∈ S, if r i < (t : ℝ) then a i else 0 := by
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hcell (i : ι) : ∀ᶠ u : NNReal in 𝓝[<] t,
      (if r i ≤ (u : ℝ) then a i else 0) =
        (if r i < (t : ℝ) then a i else 0) := by
    by_cases hi : r i < (t : ℝ)
    · have h : ∀ᶠ u : NNReal in 𝓝 t, r i < (u : ℝ) :=
        (NNReal.continuous_coe.tendsto t).eventually (Ioi_mem_nhds hi)
      filter_upwards [nhdsWithin_le_nhds h] with u hu
      simp [hi, hu.le]
    · filter_upwards [self_mem_nhdsWithin (a := t) (s := Iio t)] with u hu
      have hu' : (u : ℝ) < (t : ℝ) := by exact_mod_cast hu
      have hnot : ¬ r i ≤ (u : ℝ) := not_le_of_gt (hu'.trans_le (le_of_not_gt hi))
      simp [hi,hnot]
  have hsum : ∀ᶠ u : NNReal in 𝓝[<] t, ∀ i ∈ S,
      (if r i ≤ (u : ℝ) then a i else 0) =
        (if r i < (t : ℝ) then a i else 0) :=
    (Filter.eventually_all_finset S).2 (fun i _ => hcell i)
  let F : NNReal → ℝ := fun u => c + d * (u : ℝ) +
    ∑ i ∈ S, if r i < (t : ℝ) then a i else 0
  have he : U =ᶠ[𝓝[<] t] F := by
    filter_upwards [self_mem_nhdsWithin (a := t) (s := Iio t), hsum] with u hu h
    rw [hU u (hu.le.trans hT)]
    dsimp [F]
    rw [Finset.sum_congr rfl h]
  have hc : Continuous F := by dsimp [F]; fun_prop
  exact tendsto_nhds_unique hl ((hc.tendsto t).mono_left nhdsWithin_le_nhds |>.congr' he.symm)
