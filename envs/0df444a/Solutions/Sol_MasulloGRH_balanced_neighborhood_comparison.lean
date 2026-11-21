-- Prove2me | solution 1 for MasulloGRH.balanced_neighborhood_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:01:12.274292+00:00
-- url     : https://prove2.me/submissions/7213f131-efde-41c2-a2e9-f4baf792377e

import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.SpecificLimits.Normed

open Set Filter
open scoped Pointwise Topology

private theorem balanced_localization {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
    {c : 𝕜} (hc : c ≠ 0) (hcontract : ‖c‖ < 1)
    {D U V : Set E} (hD : Balanced 𝕜 D) (hU : U ∈ 𝓝 (0 : E))
    (hloc : D ∩ U ⊆ V ∩ c • U) : D ⊆ V := by
  intro x hx
  have stay (n : ℕ) : c ^ n • x ∈ D := by
    apply hD.smul_mem _ hx
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hcontract.le
  have lim : Tendsto (fun n : ℕ => c ^ n • x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hcontract).smul_const x
  obtain ⟨n, hn⟩ := (lim.eventually_mem hU).exists
  have descend (k : ℕ) : c ^ k • x ∈ U → x ∈ U := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro h
      obtain ⟨y, hy, heq⟩ := (hloc ⟨stay (k+1), h⟩).2
      rw [pow_succ', mul_smul] at heq
      exact ih ((smul_right_injective _ hc heq) ▸ hy)
  exact (hloc ⟨hx, descend n hn⟩).1

theorem solution {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (t₁ t₂ : TopologicalSpace E)
    [@ContinuousSMul 𝕜 E _ _ t₁] [@ContinuousSMul 𝕜 E _ _ t₂]
    {A U : Set E} (hA : Balanced 𝕜 A) (hU : U ∈ @nhds E t₁ 0)
    (hcomp : ∀ V ∈ @nhds E t₁ 0, ∃ W ∈ @nhds E t₂ 0, (W ∩ A) ∩ U ⊆ V) :
    ∀ V ∈ @nhds E t₁ 0, ∃ W ∈ @nhds E t₂ 0, W ∩ A ⊆ V := by
  intro V hV
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one 𝕜
  have hc : c ≠ 0 := norm_pos_iff.mp hc₀
  have hcU : c • U ∈ @nhds E t₁ 0 := by
    let := t₁
    exact (set_smul_mem_nhds_zero_iff hc).mpr hU
  obtain ⟨W, hW, hlocal⟩ := hcomp _ (inter_mem hV hcU)
  have basis : (@nhds E t₂ 0).HasBasis
      (fun s : Set E => s ∈ @nhds E t₂ 0 ∧ Balanced 𝕜 s) id := by
    let := t₂
    exact nhds_basis_balanced 𝕜 E
  obtain ⟨W', ⟨hW', hbal⟩, hsub⟩ := basis.mem_iff.mp hW
  refine ⟨W', hW', ?_⟩
  let := t₁
  apply balanced_localization hc hc₁ (hbal.inter hA) hU
  exact (inter_subset_inter_left U (inter_subset_inter_left A hsub)).trans hlocal
