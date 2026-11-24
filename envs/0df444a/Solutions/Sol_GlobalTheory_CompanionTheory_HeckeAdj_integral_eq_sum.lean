-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeAdj.integral_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:04.854544+00:00
-- url     : https://prove2.me/submissions/08f9c975-6944-4b80-ba16-e855f4749e9f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_finite_out_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_measure_coset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAdj
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.CompanionTheory.HeckeAdj
theorem _root_.solution (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {φ : G → ℂ} (hφ : HasCompactSupport φ)
    (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) :
    ∫ g, φ g ∂μ = μ.real (K : Set G) • ∑ᶠ q : G ⧸ K, φ q.out := by
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hF := finite_out_ne_zero K hKo hφ
  set S : Finset (G ⧸ K) := hF.toFinset with hS
  have hmeas : ∀ q : G ⧸ K, MeasurableSet ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) := fun q =>
    ((isOpen_discrete ({q} : Set (G ⧸ K))).preimage QuotientGroup.continuous_mk).measurableSet
  have hout : ∀ g : G, φ ((g : G ⧸ K)).out = φ g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hr g k k.2]
  have hsum : φ = fun g => ∑ q ∈ S, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g := by
    funext g
    have : ∀ q : G ⧸ K, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g =
        if (g : G ⧸ K) = q then φ q.out else 0 := fun q => by
      simp [Set.indicator_apply]
    simp only [this, Finset.sum_ite_eq]
    split_ifs with h
    · exact (hout g).symm
    · have : φ ((g : G ⧸ K)).out = 0 := by
        by_contra h0
        exact h (hF.mem_toFinset.2 h0)
      rw [← hout g, this]
  have hint : ∀ q ∈ S, Integrable (((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out)) μ := by
    intro q _
    refine (integrable_indicator_iff (hmeas q)).2 (integrableOn_const ?_)
    rw [measure_coset]
    exact hfin
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun q hq => hF.mem_toFinset.2 hq)]
  conv_lhs => rw [hsum]
  rw [integral_finset_sum S hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hmeas q)]
  simp only [Measure.real, measure_coset]
end GlobalTheory.CompanionTheory.HeckeAdj
