-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.inv_bounded_on_tube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:42:52.033827+00:00
-- url     : https://prove2.me/submissions/89a041c6-0bdc-4a0e-9d15-cd7ef342829f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformLocallyBounded
import Theorems.Thm_GlobalTheory_T_exponential_fourier_integral_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T]
    (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ C : Set (ℝ × ℝ), IsCompact C →
    ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ tube C, ∀ g' ∈ U, ‖inv (fun t => φ t g') l‖ ≤ M := by
  intro X _ _ T _ φ hφ hc C hC g
  choose ε hε U hU M hM using fun x₀ : ℝ × ℝ => hφ x₀ g
  have hnhds : ∀ x ∈ C, {y : ℝ × ℝ | |y.1 - x.1| < ε x ∧ |y.2 - x.2| < ε x} ∈ 𝓝 x := by
    intro x _
    have h1 : Continuous fun y : ℝ × ℝ => |y.1 - x.1| := by fun_prop
    have h2 : Continuous fun y : ℝ × ℝ => |y.2 - x.2| := by fun_prop
    refine ((isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)).mem_nhds ?_
    simpa using hε x
  obtain ⟨s, -, hcov⟩ := hC.elim_nhds_subcover _ hnhds
  refine ⟨⋂ x ∈ s, U x, (Filter.biInter_finset_mem s).2 fun x _ => hU x,
    ‖(((2 * Real.pi) ^ 2 : ℂ)⁻¹)‖ * ∑ x ∈ s, |M x| * (2 / ε x) ^ 2, ?_⟩
  intro l hl g' hg'
  have hlC : ((l.1.re, l.2.re) : ℝ × ℝ) ∈ C := hl
  obtain ⟨x₀, hx₀, h1, h2⟩ := Set.mem_iUnion₂.1 (hcov hlC)
  have hgU : g' ∈ U x₀ := Set.mem_iInter₂.1 hg' x₀ hx₀
  have hb := (GlobalTheory.T.exponential_fourier_integral_bound X (fun t => φ t g') l (ε x₀) (M x₀) (hε x₀) (hc g')
    fun t => hM x₀ (l.1.re, l.2.re) h1.le h2.le g' hgU t).2
  have hterm : M x₀ * (2 / ε x₀) ^ 2 ≤ |M x₀| * (2 / ε x₀) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have hsum : |M x₀| * (2 / ε x₀) ^ 2 ≤ ∑ x ∈ s, |M x| * (2 / ε x) ^ 2 :=
    Finset.single_le_sum (f := fun x => |M x| * (2 / ε x) ^ 2)
      (fun x _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hx₀
  simp only [inv]
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hb.trans (hterm.trans hsum)) (norm_nonneg _)
end GlobalTheory.CompanionTheory.TubeFourier
