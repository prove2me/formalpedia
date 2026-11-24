-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.swap_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:11.337085+00:00
-- url     : https://prove2.me/submissions/6a91a2f3-7d8e-47f0-b53a-ee63e8d20f33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]
    [SigmaFinite ν] (k : X → Y → Y → ℂ) (hk : Continuous (fun z : (Y × Y) × X => k z.2 z.1.1 z.1.2))
    (S : Set X) (B C : Set Y) (hS : IsCompact S) (hB : IsCompact B) (hC : IsCompact C)
    (hsupp : ∀ g b c, k g b c ≠ 0 → g ∈ S ∧ b ∈ B ∧ c ∈ C) :
    ∫ g, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ = ∫ b, ∫ c, ∫ g, k g b c ∂μ ∂ν ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hS.measure_lt_top⟩
  set Φ : (Y × Y) × X → ℂ := fun z => k z.2 z.1.1 z.1.2 with hΦdef
  have hΦc : HasCompactSupport Φ := by
    refine HasCompactSupport.intro ((hB.prod hC).prod hS) fun z hz => ?_
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hsupp _ _ _ h
    exact hz ⟨⟨h2, h3⟩, h1⟩
  have hΦ : Integrable Φ ((ν.prod ν).prod (μ.restrict S)) := hk.integrable_of_hasCompactSupport hΦc
  have hL : ∫ g, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ = ∫ g in S, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    have : ∀ b c, k g b c = 0 := fun b c => by
      by_contra h; exact hg (hsupp _ _ _ h).1
    simp [this]
  have hR : ∀ b c, ∫ g, k g b c ∂μ = ∫ g in S, k g b c ∂μ := fun b c => by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra h; exact hg (hsupp _ _ _ h).1
  simp_rw [hR]
  rw [hL]
  calc ∫ g in S, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ
      = ∫ g, ∫ q, Φ (q, g) ∂(ν.prod ν) ∂(μ.restrict S) := by
        refine integral_congr_ae ?_
        filter_upwards [hΦ.prod_left_ae] with g hg
        exact (integral_prod (fun q => Φ (q, g)) hg).symm
    _ = ∫ q, ∫ g, Φ (q, g) ∂(μ.restrict S) ∂(ν.prod ν) :=
        (integral_integral_swap (f := fun q g => Φ (q, g)) hΦ).symm
    _ = ∫ b, ∫ c, ∫ g in S, k g b c ∂μ ∂ν ∂ν := integral_prod _ hΦ.integral_prod_left
end GlobalTheory.JR.LinDesc.Swap
