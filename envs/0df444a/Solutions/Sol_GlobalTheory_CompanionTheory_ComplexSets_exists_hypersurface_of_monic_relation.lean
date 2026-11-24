-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.exists_hypersurface_of_monic_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:30.777217+00:00
-- url     : https://prove2.me/submissions/787d89de-eef1-4815-a013-b59c7d3bd2eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermMeetOverHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeetOverHypersurfaceOfGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
namespace GlobalTheory.CompanionTheory.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hirr : GermIrreducibleAt Y w) {φ : (σ → ℂ) → ℂ}
    (hφ : AnalyticAt ℂ φ w) (hnv : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0) :
    ∀ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ Y → φ z ^ N + ∑ j, a j (A z) * φ z ^ (j : ℕ) = 0) →
      ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
        ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 → e (A z) = 0 := by
  intro N
  induction N with
  | zero =>
    intro a _ hrel
    exfalso
    have := hrel.self_of_nhds hirr.1
    simp at this
  | succ n ih =>
    intro a ha hrel
    by_cases h0 : ∀ᶠ y in 𝓝 (A w), a 0 y = 0
    · have h0' : ∀ᶠ z in 𝓝 w, a 0 (A z) = 0 := (A.continuous.tendsto w).eventually h0
      have hQ : AnalyticAt ℂ (fun z => φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) w := by
        refine (hφ.pow n).add ?_
        refine Finset.analyticAt_fun_sum _ fun j _ => ?_
        have hc : AnalyticAt ℂ (fun z => a j.succ (A z)) w :=
          AnalyticAt.comp' (ha j.succ) (A.analyticAt w)
        exact hc.mul (hφ.pow _)
      have hprod : ∀ᶠ z in 𝓝 w, z ∈ Y →
          φ z * (φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) = 0 := by
        filter_upwards [hrel, h0'] with z hz hz0 hzY
        have h := hz hzY
        rw [Fin.sum_univ_succ] at h
        simp only [Fin.val_zero, pow_zero, mul_one, hz0, zero_add, Fin.val_succ] at h
        rw [← h, mul_add, Finset.mul_sum, pow_succ']
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rcases hirr.2 φ _ hφ hQ hprod with h | h
      · exact absurd h hnv
      · exact ih (fun j => a j.succ) (fun j => ha j.succ) h
    · refine ⟨a 0, ha 0, h0, ?_⟩
      filter_upwards [hrel] with z hz hzY hφ0
      have h := hz hzY
      rw [Fin.sum_univ_succ] at h
      simpa [hφ0] using h
end GlobalTheory.CompanionTheory.ComplexSets
