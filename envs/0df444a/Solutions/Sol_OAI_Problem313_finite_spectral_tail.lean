-- Prove2me | solution 1 for OAI.Problem313.finite_spectral_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:03:08.905201+00:00
-- url     : https://prove2.me/submissions/7a5a807c-74b0-4dc5-a0b1-208c41c850d1

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


theorem solution {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i) :
    (∑ i ∈ s with cutoff < degree i, mass i) ≤
      (∑ i ∈ s, degree i * mass i) / cutoff := by
  rw [le_div_iff₀ hcutoff, Finset.sum_filter, Finset.sum_mul]
  apply Finset.sum_le_sum; intro i hi
  have h1 := hmass i hi
  have h2 := hdegree i hi
  split_ifs with h
  · nlinarith
  · nlinarith

