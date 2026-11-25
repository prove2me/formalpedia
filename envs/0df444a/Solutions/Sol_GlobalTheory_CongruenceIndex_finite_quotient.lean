-- Prove2me | solution 1 for GlobalTheory.CongruenceIndex.finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:38:23.389679+00:00
-- url     : https://prove2.me/submissions/66a008f3-dec3-4c1b-b95c-44089681267e

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
namespace GlobalTheory.CongruenceIndex
theorem _root_.solution (hΛ : Λ.FG) {M : ℕ} (hM : 0 < M) :
    Finite (Λ ⧸ (nsmulAddMonoidHom M : Λ →+ Λ).range) := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  haveI : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ hM.ne'
  infer_instance
end GlobalTheory.CongruenceIndex
