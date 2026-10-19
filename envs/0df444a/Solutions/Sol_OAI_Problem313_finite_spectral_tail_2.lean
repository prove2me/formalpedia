-- Prove2me | solution 2 for OAI.Problem313.finite_spectral_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:33:28.456497+00:00
-- url     : https://prove2.me/submissions/ee257743-36a5-483f-b2ae-906e25c13689

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/SpectralBounds.lean:L11-L31
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.finite_spectral_tail. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.SpectralBounds ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- A finite spectral tail is controlled by its first degree moment. -/
theorem finite_spectral_tail {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i) :
    (∑ i ∈ s with cutoff < degree i, mass i) ≤
      (∑ i ∈ s, degree i * mass i) / cutoff := by
  classical
  apply (le_div_iff₀ hcutoff).2
  rw [Finset.sum_mul]
  calc
    ∑ i ∈ s with cutoff < degree i, mass i * cutoff ≤
        ∑ i ∈ s with cutoff < degree i, degree i * mass i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hiq⟩ := Finset.mem_filter.mp hi
      nlinarith [hmass i his]
    _ ≤ ∑ i ∈ s, degree i * mass i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi _
      exact mul_nonneg (hdegree i hi) (hmass i hi)

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution.{u} : type_of% @_root_.OAI.Problem313.finite_spectral_tail.{u} := @_root_.OAI.Problem313.finite_spectral_tail.{u}
