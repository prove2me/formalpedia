-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.cond_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:05:27.680123+00:00
-- url     : https://prove2.me/submissions/64fb00ad-ffb8-4d45-b283-89a77d51006b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_ex_bounds
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_conv_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {G : Type} [Group G]
variable {Γ A B : Subgroup G} {a b h : G → ℝ} {N R Rw : ℝ}
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g) :
    ∀ x ∈ coneC (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ A (fun g => p * (h g - a g) + t * a g) ∧
        Conv Γ A fun g => ((N - 1) * (h g - a g)) - q * (h g - a g) + t * a g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hA (t - (M + 1)) (M + 1) ?_ (by linarith)) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · refine conv_congr (hA (t - N + 1 + (m - 1)) (N - 1 - (m - 1)) ?_ (by linarith [hN'.1]))
      fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1, hN'.2]
end GlobalTheory.CompanionTheory.RgEisGal
