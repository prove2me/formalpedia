-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ker_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:42:19.001093+00:00
-- url     : https://prove2.me/submissions/9671daa4-c00e-43e9-8540-7fa86937908e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_exists_form
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_X
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
theorem _root_.solution (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime] (hQ : IsMultiHomogIdeal Q)
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) :
    RingHom.ker (theta Q p) = chartIdeal Q p := by
  have hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0 := fun k h =>
    hp k ((phi_eq_zero_iff Q _).1 h)
  have hQk : Q ≤ RingHom.ker (theta Q p) := by
    obtain ⟨S, hS, hQS⟩ := hQ
    have hSQ : S ⊆ Q := fun f hf => hQS ▸ Ideal.subset_span hf
    conv_lhs => rw [hQS]
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    exact RingHom.mem_ker.2 ((theta_eq_zero_iff Q p hp ha).2 (hSQ hf))
  have hgen : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ RingHom.ker (theta Q p) := by
    intro k
    rw [RingHom.mem_ker, map_sub, map_one, theta_X, div_self (hx k), sub_self]
  have hle : chartIdeal Q p ≤ RingHom.ker (theta Q p) := by
    refine sup_le hQk ?_
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hgen k
  refine le_antisymm ?_ hle
  intro g hg
  have hI : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal Q p := fun k =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨d, H, hH, hm⟩ := exists_form p (chartIdeal Q p) hI g
  have hθ : theta Q p H = 0 := by
    have h1 := RingHom.mem_ker.1 (hle hm)
    rw [map_sub, RingHom.mem_ker.1 hg, sub_zero] at h1
    exact h1
  have hHQ : H ∈ chartIdeal Q p :=
    Ideal.mem_sup_left ((theta_eq_zero_iff Q p hp hH).1 hθ)
  have := Ideal.sub_mem _ hHQ hm
  simpa using this
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
