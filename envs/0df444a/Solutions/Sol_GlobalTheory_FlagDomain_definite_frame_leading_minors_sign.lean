-- Prove2me | solution 1 for GlobalTheory.FlagDomain.definite_frame_leading_minors_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:35.035368+00:00
-- url     : https://prove2.me/submissions/f8d25e7a-dbd2-4b0a-a0e4-c9b68fb7e25a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DefiniteFrameLeadingMinorsSign
import Theorems.Thm_GlobalTheory_FlagDomain_dmin_sign_of_definite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder ComplexConjugate Matrix
open GlobalTheory GlobalTheory.FlagDomain
namespace GlobalTheory.FlagDomain
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ (x : Frame X.Ψ r) (τ : X.Ψ), (mat x τ).det ≠ 0 →
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re :=
  fun E _ _ _ r X h x τ hx i => dmin_sign_of_definite E r X h x τ hx i
end GlobalTheory.FlagDomain
