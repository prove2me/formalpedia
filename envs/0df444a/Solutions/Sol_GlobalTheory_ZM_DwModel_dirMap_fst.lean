-- Prove2me | solution 1 for GlobalTheory.ZM.DwModel.dirMap_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:38.804242+00:00
-- url     : https://prove2.me/submissions/520f4e82-eba7-4101-909a-6cf6fff31bf1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel
namespace GlobalTheory.ZM.DwModel
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (lam : (Fin n → K) →ₗ[K] K) (x : TrivSqZeroExt K (Fin n → K)) :
    (dirMap lam x).fst = x.fst ∧ (dirMap lam x).snd = lam x.snd := by
  constructor <;> simp [dirMap]
end GlobalTheory.ZM.DwModel
