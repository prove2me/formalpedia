-- Prove2me | solution 1 for GlobalTheory.T.exists_hostNorm_mod_coprime_level_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:33.527794+00:00
-- url     : https://prove2.me/submissions/36922a4d-45ae-43f0-ab4b-a50cc7d92a40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalfStatement
import Theorems.Thm_GlobalTheory_NormMod_exists_norm_mod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (n : ℕ) (ν : ℤ), 0 < n → IsCoprime ν (n : ℤ) → ∃ t : 𝓞 E, (n : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ (l.M ∣ n → t - 1 ∈ l.Mb) := by
  first | exact @GlobalTheory.NormMod.exists_norm_mod | exact GlobalTheory.NormMod.exists_norm_mod | (intros; apply GlobalTheory.NormMod.exists_norm_mod <;> assumption)
end _root_.GlobalTheory.T
