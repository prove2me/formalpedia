-- Prove2me | solution 1 for GlobalTheory.UnitFrame.hermC_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:46.341866+00:00
-- url     : https://prove2.me/submissions/9d23041a-3225-45de-994e-6186aaca4046

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem
import Theorems.Thm_GlobalTheory_UnitFrame_hermC_eq
import Theorems.Thm_GlobalTheory_UnitFrame_gram_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitFrame
namespace _root_.GlobalTheory.UnitFrame
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (c c' : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (x *ᵥ c) (x *ᵥ c') = c ⬝ᵥ (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x) *ᵥ (star c') := by
  have hstar : star (x *ᵥ c') = x.map conj *ᵥ star c' := by
    funext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  rw [_root_.GlobalTheory.UnitFrame.hermC_eq, _root_.GlobalTheory.UnitFrame.gram_eq,
    ← mulVec_mulVec, ← mulVec_mulVec, hstar, dotProduct_mulVec c xᵀ, vecMul_transpose]
end _root_.GlobalTheory.UnitFrame
end GlobalTheory.UnitFrame
