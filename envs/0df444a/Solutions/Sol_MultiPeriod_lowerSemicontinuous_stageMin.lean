-- Prove2me | solution 1 for MultiPeriod.lowerSemicontinuous_stageMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:43.984472+00:00
-- url     : https://prove2.me/submissions/5075de4c-7e89-463c-82bb-4c2ceeed76f0

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_isCompact_feasGraph_fiber
import Theorems.Thm_MultiPeriod_continuous_projX
import Theorems.Thm_MultiPeriod_continuous_projY
import Theorems.Thm_exists_tendsto_subseq_couplings


set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
namespace MultiPeriod
theorem _root_.solution
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t)) (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    LowerSemicontinuous (stageMin κμP κνP t F C) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  rcases eq_or_ne y ⊤ with rfl | hy
  · rw [Set.Iic_top, Set.preimage_univ]
    exact isClosed_univ
  refine IsSeqClosed.isClosed fun hs h hmem hlim => ?_
  simp only [Set.mem_preimage, Set.mem_Iic] at hmem ⊢
  -- select minimizers along the sequence
  have hsel : ∀ n, ∃ γ : WeakP (X (t + 1) × Y (t + 1)),
      ((hs n, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t ∧ γ ∈ C) ∧
      F (hs n, γ) ≤ y := by
    intro n
    have hfibne : ∃ γ, (hs n, γ) ∈ FeasGraph
        (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t ∧ γ ∈ C := by
      by_contra hempty
      have htop : stageMin κμP κνP t F C (hs n) = ⊤ :=
        iInf_eq_top.mpr fun γ => iInf_eq_top.mpr fun hcond =>
          absurd hcond (not_exists.mp hempty γ)
      have := hmem n
      rw [htop] at this
      exact hy (top_le_iff.mp this)
    obtain ⟨γ₀, hγ₀⟩ := hfibne
    have hcomp : IsCompact ({γ : WeakP (X (t + 1) × Y (t + 1)) |
        (hs n, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C) :=
      (isCompact_feasGraph_fiber κμP κνP t (hs n)).inter_right hC
    have hne' : ({γ : WeakP (X (t + 1) × Y (t + 1)) |
        (hs n, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty :=
      ⟨γ₀, hγ₀.1, hγ₀.2⟩
    obtain ⟨γn, hγn_mem, hγn_min⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hne' hcomp
        ((hF.comp (Continuous.prodMk continuous_const continuous_id)
          ).lowerSemicontinuousOn _)
    refine ⟨γn, ⟨hγn_mem.1, hγn_mem.2⟩, ?_⟩
    refine le_trans (le_trans ?_ (le_refl (stageMin κμP κνP t F C (hs n))))
      (hmem n)
    exact le_iInf₂ fun γ' hγ' => isMinOn_iff.mp hγn_min γ' ⟨hγ'.1, hγ'.2⟩
  choose γs hγs_cond hγs_le using hsel
  -- marginal convergence via Feller continuity of the kernels
  have hμ : Tendsto (fun n => κμP t (projX t (hs n))) atTop
      (𝓝 (κμP t (projX t h))) :=
    (((hκμ_cont t).comp (continuous_projX t)).tendsto h).comp hlim
  have hν : Tendsto (fun n => κνP t (projY t (hs n))) atTop
      (𝓝 (κνP t (projY t h))) :=
    (((hκν_cont t).comp (continuous_projY t)).tendsto h).comp hlim
  -- upper hemicontinuity: extract a convergent subsequence of couplings
  obtain ⟨γlim, hlfst, hlsnd, φ, hφmono, hφt⟩ :=
    exists_tendsto_subseq_couplings hμ hν
      (fun n => (hγs_cond n).1.1) (fun n => (hγs_cond n).1.2)
  have hγlim_C : γlim ∈ C :=
    hC.mem_of_tendsto hφt (Eventually.of_forall fun k => (hγs_cond (φ k)).2)
  have hγlim_fib : (h, γlim) ∈ FeasGraph
      (fun t x => (κμP t x : Measure (X (t + 1))))
      (fun t y => (κνP t y : Measure (Y (t + 1)))) t := ⟨hlfst, hlsnd⟩
  -- the limit is no worse: closed sublevel set of the jointly lsc F
  have hFy : F (h, γlim) ≤ y := by
    have hclosed_sub := (lowerSemicontinuous_iff_isClosed_preimage.mp hF) y
    have hpairs : Tendsto (fun k => (hs (φ k), γs (φ k))) atTop
        (𝓝 (h, γlim)) :=
      (hlim.comp hφmono.tendsto_atTop).prodMk_nhds hφt
    exact hclosed_sub.mem_of_tendsto hpairs
      (Eventually.of_forall fun k => hγs_le (φ k))
  exact le_trans (iInf₂_le γlim ⟨hγlim_fib, hγlim_C⟩) hFy
end MultiPeriod
