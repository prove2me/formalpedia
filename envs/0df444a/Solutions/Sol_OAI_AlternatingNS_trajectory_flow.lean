-- Prove2me | solution 1 for OAI.AlternatingNS.trajectory_flow
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T02:13:15.935491+00:00
-- url     : https://prove2.me/submissions/f03fbbcd-dd71-4b1d-b2b2-8ebc0b83d3bf

import Mathlib
import Definitions.Def_NavierStokesAlternating
set_option autoImplicit false
open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory OAI OAI.AlternatingNS

namespace AN_T

lemma fderiv_apply_eq (U : Velocity) (t : ℝ) (x v : Space) :
    fderiv ℝ (U t) x v = ∑ i, v i • dx i U t x := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
  simp [map_sum, map_smul, dx, e]

lemma contDiff_slice (U : Velocity) (hU : Smooth U) (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (U t) := by
  have h1 : ContDiff ℝ ∞ (fun x : Space => (t, x)) := by fun_prop
  have h2 := hU.comp h1.contDiffOn (s := Set.univ) (fun x _ => by simp [ht])
  rw [contDiffOn_univ] at h2
  exact h2

lemma bound (U : Velocity) (hr : Rapid U) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x, ‖U t x‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := hr 0 0 0
  refine ⟨C, hC, fun t ht x => ?_⟩
  have := h t ht x
  simpa [mixed, spatial] using this

lemma bound_dx (U : Velocity) (hr : Rapid U) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x, ‖dx i U t x‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := hr 0 0 (Pi.single i 1)
  refine ⟨C, hC, fun t ht x => ?_⟩
  have h' := h t ht x
  have e1 : mixed 0 (Pi.single i 1) U t x = dx i U t x := by
    fin_cases i <;> simp [mixed, spatial]
  rw [e1] at h'
  simpa using h'

lemma lipschitz (U : Velocity) (hU : Smooth U) (hr : Rapid U) :
    ∃ K : NNReal, ∀ t, 0 ≤ t → LipschitzWith K (U t) := by
  choose C hC0 hC using bound_dx U hr
  have hS : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC0 i)
  refine ⟨Real.toNNReal (∑ i, C i), fun t ht => ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact (contDiff_slice U hU t ht).differentiable (by simp)
  · intro x
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hS, coe_nnnorm]
    apply ContinuousLinearMap.opNorm_le_bound _ hS
    intro v
    rw [fderiv_apply_eq, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    have h1 : ‖v i‖ ≤ ‖v‖ := PiLp.norm_apply_le v i
    calc ‖v i‖ * ‖dx i U t x‖ ≤ ‖v‖ * C i :=
          mul_le_mul h1 (hC i t ht x) (norm_nonneg _) (norm_nonneg _)
      _ = C i * ‖v‖ := mul_comm _ _

lemma cont_time (U : Velocity) (hU : Smooth U) (x : Space) :
    ContinuousOn (fun t => U t x) (Set.Ici 0) := by
  have h1 : ContinuousOn (Function.uncurry U) (Set.Ici 0 ×ˢ Set.univ) := hU.continuousOn
  have h2 : Continuous (fun t : ℝ => (t, x)) := by fun_prop
  exact h1.comp h2.continuousOn (fun t ht => by simpa using ht)


lemma exists_sol (U : Velocity) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, 0 ≤ t → ∀ x, ‖U t x‖ ≤ C)
    (K : NNReal) (hK : ∀ t, 0 ≤ t → LipschitzWith K (U t))
    (hc : ∀ x, ContinuousOn (fun t => U t x) (Set.Ici 0)) (a : Space) (T : ℝ) (hT : 0 ≤ T) :
    ∃ α : ℝ → Space, α 0 = a ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt α (U t (α t)) (Set.Icc 0 T) t := by
  have hPL : IsPicardLindelof U (tmin := 0) (tmax := T) ⟨0, ⟨le_rfl, hT⟩⟩ a
      (Real.toNNReal (C * T)) 0 (Real.toNNReal C) K :=
    { lipschitzOnWith := fun t ht => (hK t ht.1).lipschitzOnWith
      continuousOn := fun x _ => (hc x).mono Set.Icc_subset_Ici_self
      norm_le := fun t ht x _ => by rw [Real.coe_toNNReal _ hC0]; exact hC t ht.1 x
      mul_max_le := by
        rw [Real.coe_toNNReal _ hC0, Real.coe_toNNReal _ (mul_nonneg hC0 hT)]
        simp [hT] }
  obtain ⟨α, h0, h⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, h⟩

lemma uniq (U : Velocity) (K : NNReal) (hK : ∀ t, 0 ≤ t → LipschitzWith K (U t))
    {f g : ℝ → Space} {b : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 b))
    (hf' : ∀ t ∈ Set.Ico 0 b, HasDerivWithinAt f (U t (f t)) (Set.Ici t) t)
    (hg : ContinuousOn g (Set.Icc 0 b))
    (hg' : ∀ t ∈ Set.Ico 0 b, HasDerivWithinAt g (U t (g t)) (Set.Ici t) t)
    (h0 : f 0 = g 0) : Set.EqOn f g (Set.Icc 0 b) :=
  ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hK t ht.1).lipschitzOnWith) hf hf' (fun _ _ => trivial) hg hg'
    (fun _ _ => trivial) h0

/-- A trajectory (within `Ici 0`) satisfies the hypotheses of `uniq` on any `[0, b]`. -/
lemma traj_cont (U : Velocity) (a : Space) (γ : ℝ → Space) (h : IsTrajectory U a γ) (b : ℝ) :
    ContinuousOn γ (Set.Icc 0 b) := fun t ht =>
  ((h.2 t ht.1).continuousWithinAt).mono Set.Icc_subset_Ici_self

lemma traj_deriv (U : Velocity) (a : Space) (γ : ℝ → Space) (h : IsTrajectory U a γ) (b : ℝ) :
    ∀ t ∈ Set.Ico 0 b, HasDerivWithinAt γ (U t (γ t)) (Set.Ici t) t := fun t ht =>
  (h.2 t ht.1).mono (Set.Ici_subset_Ici.2 ht.1)

/-- A local solution on `[0, T]` satisfies the hypotheses of `uniq` on `[0, b]` for `b ≤ T`. -/
lemma loc_cont (U : Velocity) (α : ℝ → Space) (T : ℝ)
    (h : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt α (U t (α t)) (Set.Icc 0 T) t) (b : ℝ) (hb : b ≤ T) :
    ContinuousOn α (Set.Icc 0 b) := fun t ht =>
  ((h t ⟨ht.1, ht.2.trans hb⟩).continuousWithinAt).mono (Set.Icc_subset_Icc_right hb)

lemma loc_deriv (U : Velocity) (α : ℝ → Space) (T : ℝ)
    (h : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt α (U t (α t)) (Set.Icc 0 T) t) (b : ℝ) (hb : b ≤ T) :
    ∀ t ∈ Set.Ico 0 b, HasDerivWithinAt α (U t (α t)) (Set.Ici t) t := by
  intro t ht
  have htT : t < T := lt_of_lt_of_le ht.2 hb
  refine (h t ⟨ht.1, htT.le⟩).mono_of_mem_nhdsWithin ?_
  exact Filter.mem_of_superset (Icc_mem_nhdsGE htT) (Set.Icc_subset_Icc_left ht.1)

end AN_T

theorem solution (U : Velocity) (hU : Smooth U) (hr : Rapid U) :
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory U a (X a)) ∧
      (∀ a γ, IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) := by
  obtain ⟨C, hC0, hC⟩ := AN_T.bound U hr
  obtain ⟨K, hK⟩ := AN_T.lipschitz U hU hr
  have hc := AN_T.cont_time U hU
  choose α hα0 hα using fun (a : Space) (n : ℕ) =>
    AN_T.exists_sol U C hC0 hC K hK hc a (n : ℝ) (Nat.cast_nonneg n)
  -- consistency of the local solutions
  have agree : ∀ (a : Space) (m n : ℕ) (s : ℝ), 0 ≤ s → s ≤ m → s ≤ n →
      α a m s = α a n s := by
    intro a m n s hs hm hn
    have := AN_T.uniq U K hK (b := min (m : ℝ) n)
      (AN_T.loc_cont U _ _ (hα a m) _ (min_le_left _ _))
      (AN_T.loc_deriv U _ _ (hα a m) _ (min_le_left _ _))
      (AN_T.loc_cont U _ _ (hα a n) _ (min_le_right _ _))
      (AN_T.loc_deriv U _ _ (hα a n) _ (min_le_right _ _))
      ((hα0 a m).trans (hα0 a n).symm)
    exact this ⟨hs, le_min hm hn⟩
  set N : ℝ → ℕ := fun t => ⌈t⌉₊ + 1 with hN
  have hNt : ∀ t : ℝ, t < (N t : ℝ) := fun t => by
    simp only [hN, Nat.cast_add, Nat.cast_one]
    linarith [Nat.le_ceil t]
  refine ⟨fun a t => α a (N t) t, fun a => ⟨hα0 a _, fun t ht => ?_⟩, ?_⟩
  · have hEq : ∀ s ∈ Set.Icc (0 : ℝ) (N t), α a (N s) s = α a (N t) s := fun s hs =>
      agree a _ _ s hs.1 (hNt s).le hs.2
    have h1 := (hα a (N t) t ⟨ht, (hNt t).le⟩).congr (f₁ := fun s => α a (N s) s) hEq rfl
    refine h1.mono_of_mem_nhdsWithin ?_
    have hI : Set.Icc (0 : ℝ) (N t) = Set.Ici (0 : ℝ) ∩ Set.Iic ((N t : ℕ) : ℝ) := Set.Ici_inter_Iic.symm
    rw [hI]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (hNt t))
  · intro a γ hγ t ht
    have := AN_T.uniq U K hK (b := (N t : ℝ))
      (AN_T.traj_cont U a γ hγ _) (AN_T.traj_deriv U a γ hγ _)
      (AN_T.loc_cont U _ _ (hα a (N t)) _ le_rfl)
      (AN_T.loc_deriv U _ _ (hα a (N t)) _ le_rfl)
      (hγ.1.trans (hα0 a _).symm)
    exact this ⟨ht, (hNt t).le⟩
