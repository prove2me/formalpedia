-- Prove2me | solution 1 for HighDimStat.SparseLinear.restricted_nullspace_iff_basis_pursuit_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:56:40.714247+00:00
-- url     : https://prove2.me/submissions/695159ff-93c5-4318-9f58-fd259b700d35

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_HasSupport
import Definitions.Def_HighDimStat_SparseLinear_RestrictedNullspaceProperty
import Definitions.Def_HighDimStat_SparseLinear_IsBasisPursuitSolution



namespace HighDimStat.SparseLinear

lemma rn_l1_cont {d : ℕ} : Continuous (fun β : Fin d → ℝ => l1Norm β) := by
  unfold l1Norm
  exact continuous_finset_sum _ fun j _ => (continuous_apply j).abs

lemma rn_exists {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (θ : Fin d → ℝ) :
    ∃ θhat, IsBasisPursuitSolution X (X.mulVec θ) θhat := by
  set c := l1Norm θ with hc
  set K : Set (Fin d → ℝ) := {β | X.mulVec β = X.mulVec θ} ∩ {β | l1Norm β ≤ c} with hK
  have hmv : Continuous (fun β : Fin d → ℝ => X.mulVec β) :=
    (Matrix.mulVecLin X).continuous_of_finiteDimensional
  have hclosed : IsClosed K :=
    (isClosed_eq hmv continuous_const).inter (isClosed_le rn_l1_cont continuous_const)
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hbdd : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨c, fun β hβ => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hc0]
    intro j
    rw [Real.norm_eq_abs]
    exact (Finset.single_le_sum (f := fun j => |β j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)).trans hβ.2
  have hcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : K.Nonempty := ⟨θ, rfl, show l1Norm θ ≤ c from le_rfl⟩
  obtain ⟨θhat, hθK, hmin⟩ := hcpt.exists_isMinOn hne rn_l1_cont.continuousOn
  refine ⟨θhat, hθK.1, fun β hβ => ?_⟩
  by_cases hβc : l1Norm β ≤ c
  · exact hmin ⟨hβ, hβc⟩
  · exact hθK.2.trans (le_of_lt (not_le.mp hβc))

lemma rn_split {d : ℕ} (S : Finset (Fin d)) (v : Fin d → ℝ) :
    l1Norm v = ∑ j ∈ S, |v j| + ∑ j ∈ Sᶜ, |v j| := by
  unfold l1Norm
  exact (Finset.sum_add_sum_compl S _).symm

theorem rn_main {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (∀ θstar : Fin d → ℝ, HasSupport θstar S →
      ∀ θhat : Fin d → ℝ, IsBasisPursuitSolution X (X.mulVec θstar) θhat → θhat = θstar)
    ↔ RestrictedNullspaceProperty X S := by
  classical
  constructor
  · intro H Δ hC hX
    set θs : Fin d → ℝ := fun j => if j ∈ S then Δ j else 0 with hθs
    set β : Fin d → ℝ := fun j => if j ∈ S then 0 else -Δ j with hβ
    have hsupp : HasSupport θs S := fun j hj => by simp [hθs, hj]
    have hdecomp : Δ = θs - β := by
      funext j; simp only [hθs, hβ, Pi.sub_apply]; split_ifs <;> ring
    have hfeas : X.mulVec β = X.mulVec θs := by
      have h0 : X.mulVec (θs - β) = 0 := by rw [← hdecomp]; exact hX
      rw [Matrix.mulVec_sub, sub_eq_zero] at h0
      exact h0.symm
    have hl1θ : l1Norm θs = ∑ j ∈ S, |Δ j| := by
      rw [rn_split S θs]
      have e1 : ∑ j ∈ S, |θs j| = ∑ j ∈ S, |Δ j| :=
        Finset.sum_congr rfl fun j hj => by simp [hθs, hj]
      have e2 : ∑ j ∈ Sᶜ, |θs j| = 0 :=
        Finset.sum_eq_zero fun j hj => by simp [hθs, Finset.mem_compl.mp hj]
      rw [e1, e2, add_zero]
    have hl1β : l1Norm β = ∑ j ∈ Sᶜ, |Δ j| := by
      rw [rn_split S β]
      have e1 : ∑ j ∈ S, |β j| = 0 := Finset.sum_eq_zero fun j hj => by simp [hβ, hj]
      have e2 : ∑ j ∈ Sᶜ, |β j| = ∑ j ∈ Sᶜ, |Δ j| :=
        Finset.sum_congr rfl fun j hj => by simp [hβ, Finset.mem_compl.mp hj]
      rw [e1, e2, zero_add]
    obtain ⟨θhat, hθhat⟩ := rn_exists X θs
    have h1 : θhat = θs := H θs hsupp θhat hθhat
    have hβbp : IsBasisPursuitSolution X (X.mulVec θs) β := by
      refine ⟨hfeas, fun γ hγ => ?_⟩
      have hmin := hθhat.2 γ hγ
      rw [h1] at hmin
      have hcone : ∑ j ∈ Sᶜ, |Δ j| ≤ 1 * ∑ j ∈ S, |Δ j| := hC
      rw [hl1β]
      rw [hl1θ] at hmin
      linarith
    have h2 : β = θs := H θs hsupp β hβbp
    rw [hdecomp, h2, sub_self]
  · intro hRN θs hsupp θhat hbp
    set Δ := θhat - θs with hΔ
    have hXΔ : X.mulVec Δ = 0 := by rw [hΔ, Matrix.mulVec_sub, hbp.1, sub_self]
    have hle : l1Norm θhat ≤ l1Norm θs := hbp.2 θs rfl
    have hcone : ConeSet S 1 Δ := by
      unfold ConeSet
      rw [rn_split S θhat, rn_split S θs] at hle
      have hoff : ∀ j ∈ Sᶜ, θs j = 0 := fun j hj => hsupp j (Finset.mem_compl.mp hj)
      have e0 : ∑ j ∈ Sᶜ, |θs j| = 0 := Finset.sum_eq_zero fun j hj => by rw [hoff j hj, abs_zero]
      have e1 : ∑ j ∈ Sᶜ, |θhat j| = ∑ j ∈ Sᶜ, |Δ j| :=
        Finset.sum_congr rfl fun j hj => by simp [hΔ, hoff j hj]
      have e2 : ∑ j ∈ S, |θs j| ≤ ∑ j ∈ S, |θhat j| + ∑ j ∈ S, |Δ j| := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        have : θs j = θhat j - Δ j := by simp [hΔ]
        rw [this]
        exact abs_sub _ _
      rw [e0, e1] at hle
      linarith
    exact sub_eq_zero.mp (hRN Δ hcone hXΔ)

end HighDimStat.SparseLinear

open HighDimStat.SparseLinear

theorem solution {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (∀ θstar : Fin d → ℝ, HasSupport θstar S →
      ∀ θhat : Fin d → ℝ, IsBasisPursuitSolution X (X.mulVec θstar) θhat → θhat = θstar)
    ↔ RestrictedNullspaceProperty X S := by
  exact rn_main X S
