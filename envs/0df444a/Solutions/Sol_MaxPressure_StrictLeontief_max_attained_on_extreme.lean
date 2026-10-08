-- Prove2me | solution 1 for MaxPressure.StrictLeontief.max_attained_on_extreme
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:30:29.498574+00:00
-- url     : https://prove2.me/submissions/980287fb-fb33-4673-97ec-95776e612a26

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

set_option autoImplicit false

open MaxPressure.StrictLeontief Matrix in
/-- The pressure as a linear map in the allocation. -/
noncomputable def mpPressureLin028 {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) :
    (Fin J → ℝ) →ₗ[ℝ] ℝ where
  toFun a := pressure N a z
  map_add' a b := by simp [pressure, Matrix.mulVec_add, dotProduct_add]
  map_smul' c a := by simp [pressure, Matrix.mulVec_smul, dotProduct_smul]

open MaxPressure.StrictLeontief Matrix in
lemma allocSet_isCompact_028 {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    IsCompact (allocSet N) := by
  obtain ⟨hA01, -, -, -, hAk, -⟩ := hN
  have hcl : IsClosed (allocSet N) := by
    have h1 : IsClosed {a : Fin J → ℝ | ∀ j, 0 ≤ a j} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
    have h2 : IsClosed {a : Fin J → ℝ | ∀ k, ∑ j, N.A k j * a j ≤ 1} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
        continuous_const
    have h3 : IsClosed {a : Fin J → ℝ | ∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_eq
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
        continuous_const
    have : allocSet N = {a : Fin J → ℝ | ∀ j, 0 ≤ a j} ∩
        {a : Fin J → ℝ | ∀ k, ∑ j, N.A k j * a j ≤ 1} ∩
        {a : Fin J → ℝ | ∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1} := by
      ext a; simp [allocSet, and_assoc]
    rw [this]; exact (h1.inter h2).inter h3
  refine (isCompact_Icc (a := (0 : Fin J → ℝ)) (b := 1)).of_isClosed_subset hcl ?_
  intro a ha
  obtain ⟨hpos, hle, -⟩ := ha
  refine ⟨fun j => hpos j, fun j => ?_⟩
  obtain ⟨k, hk⟩ := hAk j
  have hnn : ∀ j' ∈ (Finset.univ : Finset (Fin J)), 0 ≤ N.A k j' * a j' := by
    intro j' _
    rcases hA01 k j' with h | h <;> simp [h, hpos j']
  have := Finset.single_le_sum hnn (Finset.mem_univ j)
  simp only [hk, one_mul] at this
  simpa using this.trans (hle k)

open MaxPressure.StrictLeontief Matrix in
theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hA : (allocSet N).Nonempty) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∃ a ∈ extremeAllocs N, ∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N a z := by
  have hc := allocSet_isCompact_028 N hN
  let l : StrongDual ℝ (Fin J → ℝ) := LinearMap.toContinuousLinearMap (mpPressureLin028 N z)
  have hl : ∀ a, l a = pressure N a z := fun a => rfl
  have hexp : IsExposed ℝ (allocSet N) (l.toExposed (allocSet N)) :=
    ContinuousLinearMap.toExposed.isExposed
  have hSc : IsCompact (l.toExposed (allocSet N)) := hexp.isCompact hc
  have hSne : (l.toExposed (allocSet N)).Nonempty := by
    obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hA l.continuous.continuousOn
    exact ⟨x, hx, fun y hy => hmax hy⟩
  obtain ⟨e, he⟩ := hSc.extremePoints_nonempty hSne
  refine ⟨e, hexp.isExtreme.extremePoints_subset_extremePoints he, fun a ha => ?_⟩
  have := he.1.2 a ha
  simpa [hl] using this
