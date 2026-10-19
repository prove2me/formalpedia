-- Prove2me | solution 2 for OAI.Problem313.variance_le_dirichlet_of_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:36:48.225716+00:00
-- url     : https://prove2.me/submissions/a64bd97a-3fd7-4944-b248-9349526bf88c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/SpectralBounds.lean:L157-L176
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.variance_le_dirichlet_of_fourier. The node keeps its source
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

/-- Parseval and the first spectral moment immediately imply Poincaré. -/
theorem variance_le_dirichlet_of_fourier {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance dirichlet : ℝ)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = dirichlet) :
    variance ≤ dirichlet := by
  classical
  rw [hvariance, ← hdirichlet]
  calc
    (∑ S : Finset ι with S.Nonempty, coeff S ^ 2) ≤
        ∑ S : Finset ι with S.Nonempty, (S.card : ℝ) * coeff S ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.mem_filter.mp hS).2
      have hcard : (1 : ℝ) ≤ S.card := by exact_mod_cast hpos
      nlinarith [sq_nonneg (coeff S)]
    _ ≤ ∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S _ _
      exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution.{u} : type_of% @_root_.OAI.Problem313.variance_le_dirichlet_of_fourier.{u} := @_root_.OAI.Problem313.variance_le_dirichlet_of_fourier.{u}
