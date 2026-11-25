-- Prove2me | solution 1 for GlobalTheory.FlagSecProbe.one_isSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:13.386408+00:00
-- url     : https://prove2.me/submissions/be57379f-aa06-4855-a91f-fab6ad93f941

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_WeightEqZeroOfOneIsSec
import Theorems.Thm_GlobalTheory_FlagSecProbe_chi_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open GlobalTheory GlobalTheory.FlagSecProbe
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlagSecProbe
theorem _root_.solution (X : Data E r) :
    X.IsSec 0 (fun _ => 1) ∧ ∀ x, X.pnorm 0 (fun _ => 1) x = 1 := by
  refine ⟨⟨differentiableOn_const _, fun x _ b _ => ?_, fun γ hγ x _ => ?_⟩, fun x => ?_⟩
  · simp [bchar]
  · simp [chi_zero X hγ]
  · simp [Data.pnorm]
end GlobalTheory.FlagSecProbe
