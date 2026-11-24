-- Prove2me | solution 1 for GlobalTheory.FlagPts.topologicalKrullDim_affPts_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:09.059955+00:00
-- url     : https://prove2.me/submissions/3d9f00a1-286d-4ec8-9db7-d3749c345061

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePoints
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts
open MvPolynomial
variable {k : Type} [Field k] {J : Type}
namespace GlobalTheory.FlagPts
theorem _root_.solution [Fintype J] :
    topologicalKrullDim (AffPts k J) ≤ (Fintype.card J : ℕ) := by
  refine isInducing_affPtsVanIdeal.topologicalKrullDim_le.trans ?_
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card]
  simp
end GlobalTheory.FlagPts
