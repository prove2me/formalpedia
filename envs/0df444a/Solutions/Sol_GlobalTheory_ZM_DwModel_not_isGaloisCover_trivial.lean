-- Prove2me | solution 1 for GlobalTheory.ZM.DwModel.not_isGaloisCover_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:50.132832+00:00
-- url     : https://prove2.me/submissions/071c94b8-083d-4e08-975a-6c1d856e644e

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
theorem _root_.solution :
    ¬ IsGaloisCover ℤˣ (fun _ => 𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) := by
  intro h
  obtain ⟨a, -, ha⟩ := h.fibre ℂ (𝟙 _) (𝟙 _) rfl
  have h1 : (1 : ℤˣ) = a := ha 1 (by simp)
  have h2 : (-1 : ℤˣ) = a := ha (-1) (by simp)
  exact absurd (h1.trans h2.symm) (by decide)
end GlobalTheory.ZM.DwModel
