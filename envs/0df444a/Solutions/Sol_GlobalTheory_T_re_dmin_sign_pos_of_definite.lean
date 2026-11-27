-- Prove2me | solution 1 for GlobalTheory.T.re_dmin_sign_pos_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:54.816603+00:00
-- url     : https://prove2.me/submissions/0f4a4ed5-c0c8-4384-9ebd-39924f2ca6c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DefiniteFrameLeadingMinorsSign
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DefiniteFrameLeadingMinorsSignStatement
import Theorems.Thm_GlobalTheory_FlagDomain_definite_frame_leading_minors_sign


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 0 ∨ X.p0 = r) → ∀ (x : Frame X.Ψ r) (τ : X.Ψ), (mat x τ).det ≠ 0 → ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  first | exact @GlobalTheory.FlagDomain.definite_frame_leading_minors_sign | exact GlobalTheory.FlagDomain.definite_frame_leading_minors_sign | (intros; apply GlobalTheory.FlagDomain.definite_frame_leading_minors_sign <;> assumption)
end _root_.GlobalTheory.T
