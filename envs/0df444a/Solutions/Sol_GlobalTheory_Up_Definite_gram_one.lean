-- Prove2me | solution 1 for GlobalTheory.Up.Definite.gram_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:31.521795+00:00
-- url     : https://prove2.me/submissions/e1cde4af-4d0d-4cd6-b5e2-68f3fe57398c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SingleMemIntVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.Definite
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Up.Definite
theorem _root_.solution (τ : E →+* ℂ) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ (1 : Matrix (Fin r) (Fin r) E) x = (x.map conj)ᴴ * x.map conj := by
  ext a b
  simp [gram, hermC, col, Matrix.one_apply, apply_ite, Matrix.mul_apply]
end GlobalTheory.Up.Definite
