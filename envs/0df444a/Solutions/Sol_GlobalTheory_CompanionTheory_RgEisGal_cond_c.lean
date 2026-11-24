-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.cond_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:01:15.362161+00:00
-- url     : https://prove2.me/submissions/241f4c0f-01f4-4029-923c-a1b9f1da0eac

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
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneC (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ B (fun g => p * (-b g) + t * (h g + b g)) ∧
        Conv Γ B fun g => (-b g) - q * (-b g) + t * (h g + b g) := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hB (t - (M + 1)) (M + 1) ?_ (by linarith)) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · refine conv_congr (hB (t - 1 + (m - 1)) (1 - (m - 1)) ?_ (by linarith)) fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1]
end GlobalTheory.CompanionTheory.RgEisGal
