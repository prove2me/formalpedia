-- Prove2me | solution 1 for OAI.Problem313.variance_le_dirichlet_of_fourier
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:03:01.47216+00:00
-- url     : https://prove2.me/submissions/37ba25e0-7f78-4bb5-82e3-5a35ea6b6aec

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

open OAI OAI.Problem313
universe u


theorem solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance dirichlet : ℝ)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = dirichlet) :
    variance ≤ dirichlet := by
  subst hvariance; rw [← hdirichlet, Finset.sum_filter]
  apply Finset.sum_le_sum; intro S _
  split_ifs with h
  · have : (1:ℝ) ≤ S.card := by exact_mod_cast h.card_pos
    nlinarith [sq_nonneg (coeff S)]
  · positivity

