-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_source_phi_discount_sequence_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:42:21.57849+00:00
-- url     : https://prove2.me/submissions/e858b69b-99ab-442b-b163-e52cc32678c4

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Largest nonnegative source root converges as positive discount vanishes. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      ∀ r : ℕ → ℝ, (∀ n, 0 < r n) → Tendsto r atTop (nhds 0) →
      Tendsto (fun n => Phi ψ (r n)) atTop (nhds (Phi ψ 0)) := by
  intro Ω mΩ P hP D ψ hψ r hr hlim
  obtain ⟨F, X, hpath, hpsi⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hn : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => X.X t ω)) := by
    intro h
    apply D.excludesNegativeSubordinator
    filter_upwards [h,hpath] with ω hω hω'
    intro s t hst
    simpa only [hω'] using hω hst
  obtain ⟨_, hbridge⟩ := source_result81_levy_root_domain X hn
  have he (q : ℝ) : Phi X.ψ q = Phi ψ q := by
    unfold Phi
    congr 1
    ext β
    change (0 ≤ β ∧ X.ψ β = q) ↔ (0 ≤ β ∧ ψ β = q)
    constructor
    · rintro ⟨hb, hv⟩
      exact ⟨hb, (hpsi β hb).symm.trans hv⟩
    · rintro ⟨hb, hv⟩
      exact ⟨hb, (hpsi β hb).trans hv⟩
  have hφ0 := (hbridge 0 le_rfl).1.2.1.1
  have hv0 := (hbridge 0 le_rfl).1.2.1.2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards with n
    have hle : Phi X.ψ 0 ≤ Phi X.ψ (r n) := by
      by_contra! hlt
      have hh := ((hbridge (r n) (hr n).le).2 _ hφ0).mp hlt
      rw [hv0] at hh
      exact (not_lt_of_ge (hr n).le) hh
    rw [← he (r n)]
    rw [← he 0] at ha
    exact ha.trans_le hle
  · intro b hb
    rw [← he 0] at hb
    have hb0 : 0 ≤ b := hφ0.trans hb.le
    have hpos : 0 < X.ψ b := ((hbridge 0 le_rfl).2 b hb0).mp hb
    filter_upwards [hlim.eventually (gt_mem_nhds hpos)] with n hn
    rw [← he (r n)]
    exact ((hbridge (r n) (hr n).le).2 b hb0).mpr hn
