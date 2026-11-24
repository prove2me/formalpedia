-- Prove2me | solution 1 for GlobalTheory.UnimodVol.re_dotProduct_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:13.426576+00:00
-- url     : https://prove2.me/submissions/cd13f96f-d3ef-4987-a41d-626a126f6bd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_VolumeFundamentalDomainStdRealBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder
open GlobalTheory GlobalTheory.UnimodVol
namespace GlobalTheory.UnimodVol
theorem _root_.solution {g : ℕ} (z w : Fin g → ℂ) :
    (z ⬝ᵥ star w).re = ∑ k, (stdRealBasis g).repr z k * (stdRealBasis g).repr w k := by
  simp [stdRealBasis, Pi.basis_repr, Fintype.sum_sigma, Fin.sum_univ_two, dotProduct]
end GlobalTheory.UnimodVol
