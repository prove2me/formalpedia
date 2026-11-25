-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisCross.dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:43.549582+00:00
-- url     : https://prove2.me/submissions/d6f6599a-da67-4c53-b97d-7854dcfdf4da

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_EisCross_pos_nonneg__af27ebf4d2ad
import Theorems.Thm_GlobalTheory_CompanionTheory_EisCross_pos_mul_le
import Theorems.Thm_GlobalTheory_CompanionTheory_EisCross_exp_between
import Theorems.Thm_GlobalTheory_CompanionTheory_EisCross_exp_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisCross
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.EisCross
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (Γ Δ P P' : Subgroup G) (ξ l₁ l₂ : G → ℝ) (H : ℂ → G → X)
    (a b e₁ e₂ M : ℝ),
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |ξ (g * u) - ξ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₁ (g * u) - l₁ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₂ (g * u) - l₂ g| ≤ A) →
    PositivityTheory.RgEis.Conv Δ P l₁ → PositivityTheory.RgEis.Conv Δ P' l₂ →
    (∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g, ‖H z g‖ ≤ M * (PositivityTheory.RgEis.pos Δ P l₁ g + PositivityTheory.RgEis.pos Δ P' l₂ g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    ∀ g : G, ∃ U ∈ 𝓝 g, ∃ u : PositivityTheory.RgEis.Cos Δ Γ → ℝ, Summable u ∧
      ∀ l : ℂ × ℂ, b ≤ l.1.re → l.1.re ≤ a → e₁ ≤ l.2.re → l.2.re ≤ e₂ → ∀ g' ∈ U, ∀ r,
        ‖Complex.exp (l.2 * ξ (PositivityTheory.RgEis.rep r * g')) • H l.1 (PositivityTheory.RgEis.rep r * g')‖ ≤ u r := by
  intro G _ _ _ _ X _ _ Γ Δ P P' ξ l₁ l₂ H a b e₁ e₂ M hξ hl₁ hl₂ hc₁ hc₂ hH s11 s21 s12 s22 g
  obtain ⟨C, hC1, -, hCc⟩ := local_compact_nhds (x := (1 : G)) Filter.univ_mem
  obtain ⟨Aξ, hAξ⟩ := hξ C hCc
  obtain ⟨A₁, hA₁⟩ := hl₁ C hCc
  obtain ⟨A₂, hA₂⟩ := hl₂ C hCc
  have hU : (fun g' => g⁻¹ * g') ⁻¹' C ∈ 𝓝 g := by
    apply (continuous_mul_left g⁻¹).continuousAt.preimage_mem_nhds
    simpa using hC1
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' C, hU, fun r => |M| *
      (Real.exp (|e₁| * Aξ) * Real.exp A₁ * (Real.exp (e₁ * ξ (rep r * g)) * pos Δ P l₁ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp A₁ * (Real.exp (e₂ * ξ (rep r * g)) * pos Δ P l₁ (rep r * g)) +
        Real.exp (|e₁| * Aξ) * Real.exp A₂ * (Real.exp (e₁ * ξ (rep r * g)) * pos Δ P' l₂ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp A₂ * (Real.exp (e₂ * ξ (rep r * g)) * pos Δ P' l₂ (rep r * g))), ?_, ?_⟩
  · exact Summable.mul_left |M|
      ((((s11 g).mul_left (Real.exp (|e₁| * Aξ) * Real.exp A₁)).add
        ((s21 g).mul_left (Real.exp (|e₂| * Aξ) * Real.exp A₁))).add
        ((s12 g).mul_left (Real.exp (|e₁| * Aξ) * Real.exp A₂)) |>.add
        ((s22 g).mul_left (Real.exp (|e₂| * Aξ) * Real.exp A₂)))
  · intro l hb ha he₁ he₂ g' hg' r
    have hw : g⁻¹ * g' ∈ C := hg'
    have hy : rep r * g' = rep r * g * (g⁻¹ * g') := by
      rw [mul_assoc, mul_inv_cancel_left]
    have hnorm : ‖Complex.exp (l.2 * ξ (rep r * g')) • H l.1 (rep r * g')‖ =
        Real.exp (l.2.re * ξ (rep r * g')) * ‖H l.1 (rep r * g')‖ := by
      rw [norm_smul, Complex.norm_exp]
      simp [Complex.mul_re]
    have hξw := hAξ (rep r * g) (g⁻¹ * g') hw
    rw [← hy] at hξw
    have hexp : Real.exp (l.2.re * ξ (rep r * g')) ≤
        Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
          Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g)) := by
      have h0 := exp_between e₁ e₂ l.2.re (ξ (rep r * g')) he₁ he₂
      have h1 := exp_shift e₁ (ξ (rep r * g')) (ξ (rep r * g)) Aξ hξw
      have h2 := exp_shift e₂ (ξ (rep r * g')) (ξ (rep r * g)) Aξ hξw
      linarith
    have hp1 : pos Δ P l₁ (rep r * g') ≤ Real.exp A₁ * pos Δ P l₁ (rep r * g) := by
      rw [hy]
      exact pos_mul_le Δ P l₁ C A₁ hA₁ hc₁ (rep r * g) (g⁻¹ * g') hw
    have hp2 : pos Δ P' l₂ (rep r * g') ≤ Real.exp A₂ * pos Δ P' l₂ (rep r * g) := by
      rw [hy]
      exact pos_mul_le Δ P' l₂ C A₂ hA₂ hc₂ (rep r * g) (g⁻¹ * g') hw
    have hH1 := hH l.1 hb ha (rep r * g')
    have hs0 : 0 ≤ pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g') :=
      add_nonneg (pos_nonneg' _ _ _ _) (pos_nonneg' _ _ _ _)
    have hH2 : ‖H l.1 (rep r * g')‖ ≤ |M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g')) :=
      hH1.trans (mul_le_mul_of_nonneg_right (le_abs_self M) hs0)
    have hE0 : 0 ≤ Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g)) := by positivity
    rw [hnorm]
    calc Real.exp (l.2.re * ξ (rep r * g')) * ‖H l.1 (rep r * g')‖
        ≤ Real.exp (l.2.re * ξ (rep r * g')) *
            (|M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g'))) :=
          mul_le_mul_of_nonneg_left hH2 (Real.exp_pos _).le
      _ ≤ (Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
            Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g))) *
            (|M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g'))) :=
          mul_le_mul_of_nonneg_right hexp (mul_nonneg (abs_nonneg M) hs0)
      _ ≤ (Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
            Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g))) *
            (|M| * (Real.exp A₁ * pos Δ P l₁ (rep r * g) + Real.exp A₂ * pos Δ P' l₂ (rep r * g))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) (abs_nonneg M)) hE0
      _ = _ := by ring
end GlobalTheory.CompanionTheory.EisCross
