-- Prove2me | solution 2 for OAI.Problem313.variance_from_fourier_capture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:34:58.758653+00:00
-- url     : https://prove2.me/submissions/14068d69-1fc0-43d9-8509-10c3b76378c3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/SpectralBounds.lean:L131-L155
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.variance_from_fourier_capture. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Theorems.Thm_OAI_Problem313_finite_spectral_tail

-- ---- from OAI.Combinatorics.SharpThreshold.SpectralBounds ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Splitting at a positive spectral cutoff gives a low-degree term and a tail. -/
theorem finite_spectral_split {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i) :
    (∑ i ∈ s, mass i) ≤
      (∑ i ∈ s with degree i ≤ cutoff, mass i) +
      (∑ i ∈ s, degree i * mass i) / cutoff := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => degree i ≤ cutoff) mass
  simp only [not_le] at hsplit
  rw [← hsplit]
  exact add_le_add le_rfl (finite_spectral_tail s mass degree cutoff hcutoff hmass hdegree)

/-- The bias cancels exactly in the tail term at the bias-dependent cutoff. -/
theorem variance_tail_bias_cancellation (sigma ell : ℝ)
    (hsigma : sigma ≠ 0) (hell : ell ≠ 0) :
    sigma ^ 2 / ((sigma * ell / 64) ^ 2 / 2) = 8192 / ell ^ 2 := by
  field_simp
  ring

/-- Assemble low-degree capture and the Dirichlet identity into a variance bound. -/
theorem variance_from_spectral_capture {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i)
    (hcapture : (∑ i ∈ s with degree i ≤ (sigma * ell / 64) ^ 2 / 2, mass i)
      ≤ lowConstant * influence)
    (hdirichlet : (∑ i ∈ s, degree i * mass i) = sigma ^ 2 * influence) :
    (∑ i ∈ s, mass i) ≤ (lowConstant + 8192 / ell ^ 2) * influence := by
  have hcutoff : 0 < (sigma * ell / 64) ^ 2 / 2 := by positivity
  have hsplit := finite_spectral_split s mass degree _ hcutoff hmass hdegree
  have htail : sigma ^ 2 * influence / ((sigma * ell / 64) ^ 2 / 2) =
      (8192 / ell ^ 2) * influence := by
    calc
      _ = (sigma ^ 2 / ((sigma * ell / 64) ^ 2 / 2)) * influence := by ring
      _ = _ := by rw [variance_tail_bias_cancellation sigma ell hsigma.ne' hell.ne']
  rw [hdirichlet, htail] at hsplit
  nlinarith

/-- The spectral variance bound for Fourier coefficients indexed by finite supports. -/
theorem variance_from_fourier_capture {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence) :
    variance ≤ (lowConstant + 8192 / ell ^ 2) * influence := by
  classical
  let s : Finset (Finset ι) := Finset.univ.filter Finset.Nonempty
  have hdir : (∑ S ∈ s, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence := by
    rw [← hdirichlet]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S _ hS
    have hSempty : S = ∅ := by simpa [s, Finset.not_nonempty_iff_eq_empty] using hS
    simp [hSempty]
  have hcap : (∑ S ∈ s with (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence := by
    simpa only [s, Finset.filter_filter] using hcapture
  rw [hvariance]
  exact variance_from_spectral_capture s (fun S => coeff S ^ 2)
    (fun S => (S.card : ℝ)) sigma ell influence lowConstant hsigma hell
    (fun S _ => sq_nonneg _) (fun S _ => Nat.cast_nonneg _) hcap hdir

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution.{u} : type_of% @_root_.OAI.Problem313.variance_from_fourier_capture.{u} := @_root_.OAI.Problem313.variance_from_fourier_capture.{u}
