-- Prove2me | solution 1 for GlobalTheory.CongruenceIndex.inv_mulVec_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:38:26.811787+00:00
-- url     : https://prove2.me/submissions/6f30c2f0-e47b-4347-9462-c245f0abd9b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex

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
open GlobalTheory GlobalTheory.CongruenceIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.CongruenceIndex
theorem _root_.solution (γ : GL (Fin r) E) (v : Fin r → E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)
      = v := by
  rw [← mul_mulVec, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
end GlobalTheory.CongruenceIndex
